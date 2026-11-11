#!/usr/bin/env python3
"""Isolated, model-pinned experimental controller. Evidence is never room-mounted.

Usage: runner.py --room ROOM --evidence EVIDENCE --prompt PROMPT --seconds N --units N
A unit is 16*output + 8*(input-cached_input) + cached_input. Usage is cumulative
per independent thread, never summed twice. The controller stops on the first
usage notification reaching the cap; provider-in-flight usage can overshoot it.
"""
from __future__ import annotations

import argparse
import asyncio
import contextlib
import dataclasses
import json
import math
import os
from pathlib import Path
import signal
import sys
import time
import tomllib
from typing import Any

MODEL = 'gpt-6.1-sol'
EFFORT = 'high'
MAX_SESSIONS = 4
USAGE_KEYS = ('inputTokens', 'cachedInputTokens', 'outputTokens', 'reasoningOutputTokens', 'totalTokens', 'cacheWriteInputTokens')


def spec(name: str, description: str, properties: dict, required: list[str]) -> dict:
    return {'type': 'function', 'name': name, 'description': description,
            'inputSchema': {'type': 'object', 'properties': properties, 'required': required,
                            'additionalProperties': False}}


TOOLS = [
    spec('shell', 'Run a shell command in the shared isolated filesystem. Default cwd is /work. Only this tool provides filesystem access. No network, secrets, or host access. Output may be truncated. Maximum timeout 120 seconds.',
         {'command': {'type': 'string'}, 'timeout': {'type': 'integer', 'minimum': 1, 'maximum': 120}}, ['command']),
    spec('spawn_agent', 'Asynchronously launch an independent colleague with a role and explicit task. All colleagues share /work and these same capabilities; they do not inherit your conversation. At most four agents may run simultaneously including you. The result is an agent_id. Delegate full context explicitly.',
         {'role': {'type': 'string'}, 'prompt': {'type': 'string'}}, ['role', 'prompt']),
    spec('agent_status', 'Read a colleague status and completed answer; omit agent_id to list all colleagues.',
         {'agent_id': {'type': 'string'}}, []),
    spec('wait_agent', 'Wait up to 60 seconds for a specified colleague to finish and return their current status and completed answer.',
         {'agent_id': {'type': 'string'}, 'seconds': {'type': 'integer', 'minimum': 0, 'maximum': 60}}, ['agent_id']),
    spec('send_message', 'Send task context or a follow-up to a colleague. An active colleague receives a same-turn steering message; a completed colleague starts a follow-up turn in its independent context, subject to the same concurrency cap.',
         {'agent_id': {'type': 'string'}, 'message': {'type': 'string'}}, ['agent_id', 'message']),
    spec('checkpoint', 'Save an external evidence snapshot of the shared filesystem. Does not create files within /work.',
         {'label': {'type': 'string'}}, ['label']),
]


@dataclasses.dataclass
class Agent:
    id: str
    role: str
    parent: str | None
    status: str = 'launching'
    thread: str | None = None
    turn: str | None = None
    answer: str = ''
    error: str | None = None
    usage: dict[str, int] = dataclasses.field(default_factory=lambda: dict.fromkeys(USAGE_KEYS, 0))
    done: asyncio.Event = dataclasses.field(default_factory=asyncio.Event)

    def public(self) -> dict:
        return {k: getattr(self, k) for k in ('id', 'role', 'parent', 'status', 'thread', 'turn', 'answer', 'error', 'usage')}


class Controller:
    def __init__(self, room: Path, evidence: Path, seconds: float, units: int):
        self.room, self.evidence = room, evidence
        self.seconds, self.limit = seconds, units
        self.started = time.monotonic()
        self.agents: dict[str, Agent] = {}
        self.threads: dict[str, Agent] = {}
        self.pending: dict[int, asyncio.Future] = {}
        self.next_rpc = 1
        self.server = None
        self.children: set[asyncio.subprocess.Process] = set()
        self.tasks: set[asyncio.Task] = set()
        self.stop = asyncio.Event()
        self.reason = None
        self.snapshot_index = 0
        self.snapshot_lock = asyncio.Lock()
        self.events = (evidence / 'events.jsonl').open('x', buffering=1)
        self.stderr = (evidence / 'app-server.stderr').open('x')

    def log(self, kind: str, **data):
        self.events.write(json.dumps({'elapsed': round(time.monotonic() - self.started, 6),
                                      'kind': kind, **data}, ensure_ascii=False) + '\n')

    def launch_task(self, coroutine):
        task = asyncio.create_task(coroutine)
        self.tasks.add(task)
        task.add_done_callback(self.tasks.discard)
        task.add_done_callback(self.task_result)
        return task

    def task_result(self, task):
        if not task.cancelled() and task.exception():
            self.log('controller_task_error', error=repr(task.exception()))
            self.request_stop('controller_error')

    def request_stop(self, reason: str):
        if not self.stop.is_set():
            self.reason = reason
            self.log('stop_requested', reason=reason, usage=self.totals())
            self.stop.set()

    def totals(self):
        out = {key: sum(agent.usage[key] for agent in self.agents.values()) for key in USAGE_KEYS}
        out['uncachedInputTokens'] = max(0, out['inputTokens'] - out['cachedInputTokens'])
        out['normalisedUnits'] = 16 * out['outputTokens'] + 8 * out['uncachedInputTokens'] + out['cachedInputTokens']
        return out

    def active(self):
        return sum(a.status in ('launching', 'running') for a in self.agents.values())

    def send(self, message: dict):
        if self.server and self.server.returncode is None:
            self.log('rpc_send', message=message)
            self.server.stdin.write((json.dumps(message) + '\n').encode())
        else:
            raise RuntimeError('app-server unavailable')

    async def call(self, method: str, params: dict, timeout=45):
        if self.stop.is_set():
            raise RuntimeError('run stopped')
        rpc_id = self.next_rpc
        self.next_rpc += 1
        future = asyncio.get_running_loop().create_future()
        self.pending[rpc_id] = future
        self.send({'id': rpc_id, 'method': method, 'params': params})
        try:
            return await asyncio.wait_for(future, min(timeout, max(.1, self.seconds - (time.monotonic() - self.started))))
        finally:
            self.pending.pop(rpc_id, None)

    async def start_server(self):
        # Only the two supported service URLs are retained from user config.
        # Authentication remains the installed CLI's normal read-only auth file.
        home = Path.home()
        source_cfg = tomllib.loads((home / '.codex/config.toml').read_text())
        state = self.evidence / 'isolated-state'
        state.mkdir(mode=0o700)
        config = ''.join(k + ' = ' + json.dumps(source_cfg[k]) + '\n' for k in ('chatgpt_base_url', 'openai_base_url') if k in source_cfg)
        config += 'model="' + MODEL + '"\nmodel_reasoning_effort="high"\nweb_search="disabled"\n'
        config += '[agents]\nenabled=false\nmax_concurrent_threads_per_session=1\n'
        config += '[features]\napps=false\nplugins=false\nmemories=false\nmulti_agent=false\nmulti_agent_v2=false\nshell_tool=false\nunified_exec=false\n'
        (state / 'config.toml').write_text(config)
        cmd = ['bwrap', '--ro-bind', '/usr', '/usr', '--ro-bind', '/lib', '/lib',
               '--ro-bind', '/lib64', '/lib64', '--ro-bind', '/bin', '/bin',
               '--ro-bind', '/opt/codex/bin', '/opt/codex/bin', '--ro-bind', '/etc', '/etc',
               '--dev', '/dev', '--proc', '/proc', '--unshare-pid', '--die-with-parent',
               '--bind', str(state), str(home / '.codex'),
               '--ro-bind', str(home / '.codex/auth.json'), str(home / '.codex/auth.json'),
               '--tmpfs', '/tmp', '--dir', '/work', '--chdir', '/work',
               '--', '/opt/codex/bin/codex', 'app-server', '--listen', 'stdio://']
        allowed = {'HOME', 'USER', 'LANG', 'PATH', 'SSL_CERT_FILE', 'REQUESTS_CA_BUNDLE', 'CURL_CA_BUNDLE',
                   'NO_PROXY', 'no_proxy', 'HTTP_PROXY', 'HTTPS_PROXY', 'http_proxy', 'https_proxy', 'ALL_PROXY', 'all_proxy'}
        env = {k: v for k, v in os.environ.items() if k in allowed}
        self.server = await asyncio.create_subprocess_exec(*cmd, stdin=asyncio.subprocess.PIPE,
                    stdout=asyncio.subprocess.PIPE, stderr=self.stderr, env=env, start_new_session=True,
                    limit=32 * 1024 * 1024)
        self.launch_task(self.read_server())
        await self.call('initialize', {'clientInfo': {'name': 'isolated_experiment_controller', 'version': '1.0'},
                                       'capabilities': {'experimentalApi': True}})
        self.send({'method': 'initialized'})

    async def read_server(self):
        while line := await self.server.stdout.readline():
            try:
                message = json.loads(line)
            except ValueError:
                self.log('unparsed_server_output', text=line.decode(errors='replace'))
                continue
            self.log('rpc_receive', message=message)
            method = message.get('method')
            params = message.get('params', {})
            if method is None and message.get('id') in self.pending:
                future = self.pending[message['id']]
                if not future.done():
                    if 'error' in message:
                        future.set_exception(RuntimeError(json.dumps(message['error'])))
                    else:
                        future.set_result(message.get('result'))
            elif method and 'id' in message:
                if method == 'item/tool/call':
                    self.launch_task(self.handle_tool(message))
                else:
                    # No approvals, credential refresh, account context, or other host tools.
                    self.send({'id': message['id'], 'error': {'code': -32601, 'message': 'Host capability disabled'}})
                    self.log('rejected_server_request', method=method)
            elif method in ('item/started', 'item/completed') and params.get('item', {}).get('type') in ('subAgentActivity', 'collabAgentToolCall'):
                self.log('uncontrolled_native_agent', details=params)
                self.request_stop('uncontrolled_native_agent')
            elif method == 'thread/tokenUsage/updated':
                agent = self.threads.get(params['threadId'])
                if agent:
                    total = params['tokenUsage']['total']
                    agent.usage = {key: max(agent.usage[key], int(total.get(key, 0))) for key in USAGE_KEYS}
                    self.log('usage', agent_id=agent.id, per_thread=agent.usage, aggregate=self.totals())
                    if self.totals()['normalisedUnits'] >= self.limit:
                        self.request_stop('model_budget')
            elif method == 'turn/started':
                agent = self.threads.get(params.get('threadId'))
                if agent:
                    agent.turn = params['turn']['id']
            elif method == 'item/agentMessage/delta':
                agent = self.threads.get(params.get('threadId'))
                if agent:
                    agent.answer += params.get('delta', '')
            elif method == 'turn/completed':
                agent = self.threads.get(params.get('threadId'))
                if agent:
                    turn = params['turn']
                    agent.status = turn['status']
                    agent.answer = '\n'.join(item.get('text', '') for item in turn.get('items', []) if item.get('type') == 'agentMessage')
                    agent.error = json.dumps(turn['error']) if turn.get('error') else None
                    agent.done.set()
                    self.persist_agents()
                    self.log('agent_completed', agent=agent.public())
            elif method == 'error':
                self.log('model_error', details=params)
        for future in self.pending.values():
            if not future.done():
                future.set_exception(RuntimeError('app-server closed'))
        if not self.stop.is_set():
            self.request_stop('app_server_exit')

    def persist_agents(self):
        (self.evidence / 'agents.json').write_text(json.dumps([a.public() for a in self.agents.values()], indent=2))

    async def spawn(self, role: str, prompt: str, parent: str | None):
        if self.stop.is_set():
            raise RuntimeError('run stopped')
        if self.active() >= MAX_SESSIONS:
            raise RuntimeError('Four simultaneous sessions already active; wait for a colleague to finish')
        agent = Agent('agent-' + str(len(self.agents) + 1), role[:200], parent)
        self.agents[agent.id] = agent
        self.log('agent_spawn', agent_id=agent.id, role=agent.role, parent=parent, prompt=prompt)
        self.launch_task(self.start_agent(agent, prompt))
        return agent

    async def start_agent(self, agent: Agent, prompt: str):
        try:
            result = await self.call('thread/start', {'model': MODEL, 'allowProviderModelFallback': False,
                'environments': [], 'cwd': '/work', 'ephemeral': True, 'approvalPolicy': 'never', 'dynamicTools': TOOLS})
            if result.get('model') != MODEL:
                raise RuntimeError('Model mismatch: ' + str(result.get('model')))
            agent.thread = result['thread']['id']
            self.threads[agent.thread] = agent
            await self.start_turn(agent, prompt)
        except Exception as exc:
            agent.status, agent.error = 'failed', str(exc)
            agent.done.set()
            self.log('agent_start_failed', agent_id=agent.id, error=str(exc))
            if agent.parent is None:
                self.request_stop('launcher_start_failed')

    async def start_turn(self, agent: Agent, prompt: str):
        agent.status = 'running'
        agent.answer = ''
        agent.done.clear()
        prefix = f'Your role: {agent.role}. Your agent_id: {agent.id}. Shared working directory: /work.\n'
        result = await self.call('turn/start', {'threadId': agent.thread, 'model': MODEL, 'effort': EFFORT,
                'environments': [], 'input': [{'type': 'text', 'text': prefix + prompt, 'text_elements': []}]})
        agent.turn = result['turn']['id']
        self.persist_agents()

    async def handle_tool(self, message: dict):
        params = message['params']
        agent = self.threads.get(params.get('threadId'))
        try:
            if not agent:
                raise ValueError('Unknown calling agent')
            if self.stop.is_set():
                raise RuntimeError('run budget exhausted')
            name, args = params['tool'], params.get('arguments', {})
            if isinstance(args, str):
                args = json.loads(args)
            self.log('tool_start', agent_id=agent.id, tool=name, arguments=args)
            result = await self.tool(agent, name, args)
            success = True
        except asyncio.CancelledError:
            return
        except Exception as exc:
            result, success = str(exc), False
        self.log('tool_complete', agent_id=agent.id if agent else None, tool=params.get('tool'), success=success, result=result)
        if not self.stop.is_set():
            self.send({'id': message['id'], 'result': {'success': success,
                       'contentItems': [{'type': 'inputText', 'text': result if isinstance(result, str) else json.dumps(result)}]}})

    async def tool(self, caller: Agent, name: str, args: dict):
        if name == 'shell':
            timeout = max(1, min(120, int(args.get('timeout', 30)), math.ceil(self.seconds - (time.monotonic() - self.started))))
            return await self.shell(str(args['command']), timeout)
        if name == 'spawn_agent':
            return (await self.spawn(str(args['role']), str(args['prompt']), caller.id)).public()
        if name == 'agent_status':
            return self.agents[args['agent_id']].public() if args.get('agent_id') else [a.public() for a in self.agents.values()]
        if name == 'wait_agent':
            agent = self.agents[args['agent_id']]
            if agent is caller:
                raise ValueError('Cannot wait for yourself')
            with contextlib.suppress(asyncio.TimeoutError):
                await asyncio.wait_for(agent.done.wait(), max(0, min(60, int(args.get('seconds', 30)))))
            return agent.public()
        if name == 'send_message':
            agent = self.agents[args['agent_id']]
            if agent is caller:
                raise ValueError('Cannot send a message to yourself')
            message = f'Message from {caller.id} ({caller.role}):\n{args["message"]}'
            if agent.status == 'launching':
                raise RuntimeError('Colleague is still starting; retry shortly')
            if agent.status == 'running':
                return await self.call('turn/steer', {'threadId': agent.thread, 'expectedTurnId': agent.turn,
                     'input': [{'type': 'text', 'text': message, 'text_elements': []}]})
            if self.active() >= MAX_SESSIONS:
                raise RuntimeError('Four sessions active')
            await self.start_turn(agent, message)
            return agent.public()
        if name == 'checkpoint':
            await self.snapshot('agent-' + str(args['label'])[:80])
            return 'Checkpoint saved outside /work.'
        raise ValueError('Unavailable tool: ' + name)

    async def shell(self, command: str, timeout: int):
        process = await asyncio.create_subprocess_exec(sys.executable, str(Path(__file__).resolve()),
                    '--_shell-worker', str(self.room), command, str(timeout), stdout=asyncio.subprocess.PIPE,
                    stderr=asyncio.subprocess.STDOUT, start_new_session=True)
        self.children.add(process)
        try:
            try:
                output, _ = await asyncio.wait_for(process.communicate(), timeout + 3)
            except asyncio.TimeoutError:
                await self.kill(process)
                return 'Shell exceeded external timeout and was terminated.'
            text = output.decode(errors='replace')
            return text[-80000:] + (f'\n[helper exit {process.returncode}]' if process.returncode else '')
        finally:
            await self.kill(process)
            self.children.discard(process)

    @staticmethod
    async def kill(process):
        # Kill the process group even if its leader exited: descendants may remain.
        with contextlib.suppress(ProcessLookupError):
            os.killpg(process.pid, signal.SIGKILL)
        with contextlib.suppress(Exception):
            await asyncio.wait_for(process.wait(), 3)

    async def snapshot(self, label: str):
        async with self.snapshot_lock:
            self.snapshot_index += 1
            safe_label = ''.join(c if c.isalnum() or c in '-_' else '_' for c in label)
            dest = self.evidence / 'snapshots' / f'{self.snapshot_index:04d}-{safe_label}'
            dest.mkdir(parents=True)
            self.log('snapshot_start', snapshot=str(dest.relative_to(self.evidence)))
            process = await asyncio.create_subprocess_exec('cp', '-a', '--reflink=auto', '--', str(self.room), str(dest / 'room'),
                         stderr=asyncio.subprocess.PIPE, start_new_session=True)
            self.children.add(process)
            try:
                _, error = await asyncio.wait_for(process.communicate(), 30)
                if process.returncode:
                    raise RuntimeError(error.decode(errors='replace'))
                (dest / 'checkpoint.json').write_text(json.dumps({'elapsed': time.monotonic() - self.started,
                    'label': label, 'usage': self.totals(), 'agents': [a.public() for a in self.agents.values()]}, indent=2))
                self.log('snapshot_complete', snapshot=str(dest.relative_to(self.evidence)))
            finally:
                await self.kill(process)
                self.children.discard(process)

    async def periodic(self):
        while not self.stop.is_set():
            await asyncio.sleep(60)
            if not self.stop.is_set():
                await self.snapshot('minute')

    async def run(self, prompt: str):
        self.log('run_start', model=MODEL, effort=EFFORT, max_simultaneous_sessions=MAX_SESSIONS,
                 seconds=self.seconds, normalised_unit_limit=self.limit, prompt=prompt,
                 budget_enforcement='Stop at cumulative token usage notifications; in-flight work can overshoot.')
        async def work():
            await self.snapshot('initial')
            await self.start_server()
            await self.spawn('launcher', prompt, None)
            self.launch_task(self.periodic())
            while not self.stop.is_set():
                if self.agents and all(a.done.is_set() for a in self.agents.values()):
                    self.request_stop('all_agents_completed')
                    return
                await asyncio.sleep(.1)

        async def watchdog():
            await asyncio.sleep(self.seconds)
            self.request_stop('wall_budget')

        worker = asyncio.create_task(work())
        watcher = asyncio.create_task(watchdog())
        stop_waiter = asyncio.create_task(self.stop.wait())
        try:
            done, _ = await asyncio.wait([worker, stop_waiter], return_when=asyncio.FIRST_COMPLETED)
            if worker in done:
                await worker
        except Exception as exc:
            self.log('run_error', error=repr(exc))
            self.request_stop('controller_error')
        finally:
            worker.cancel()
            watcher.cancel()
            stop_waiter.cancel()
            await asyncio.gather(worker, watcher, stop_waiter, return_exceptions=True)
            for task in list(self.tasks):
                task.cancel()
            if self.server:
                await self.kill(self.server)
            await asyncio.gather(*(self.kill(p) for p in list(self.children)), return_exceptions=True)
            await asyncio.gather(*list(self.tasks), return_exceptions=True)
            self.children.clear()
            for agent in self.agents.values():
                if agent.status in ('launching', 'running'):
                    agent.status = 'terminated'
                    agent.error = self.reason
                    agent.done.set()
            try:
                await self.snapshot('final')
            except Exception as exc:
                self.log('final_snapshot_failed', error=repr(exc))
            summary = {'reason': self.reason, 'elapsed': time.monotonic() - self.started,
                'model': MODEL, 'effort': EFFORT, 'limits': {'seconds': self.seconds, 'units': self.limit,
                'simultaneous_sessions': MAX_SESSIONS}, 'usage': self.totals(), 'agents': [a.public() for a in self.agents.values()]}
            self.persist_agents()
            (self.evidence / 'summary.json').write_text(json.dumps(summary, indent=2))
            self.log('run_complete', summary=summary)
            self.events.close()
            self.stderr.close()
            print(json.dumps({'reason': self.reason, 'usage': self.totals(), 'evidence': str(self.evidence)}), flush=True)
        return 1 if self.reason in ('controller_error', 'launcher_start_failed', 'app_server_exit', 'uncontrolled_native_agent') else 0


def main():
    if len(sys.argv) > 1 and sys.argv[1] == '--_shell-worker':
        from room import execute
        print(execute(Path(sys.argv[2]), sys.argv[3], int(sys.argv[4])), flush=True)
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--room', required=True, type=Path)
    parser.add_argument('--evidence', required=True, type=Path)
    parser.add_argument('--prompt', required=True, type=Path)
    parser.add_argument('--seconds', required=True, type=float)
    parser.add_argument('--units', required=True, type=int)
    args = parser.parse_args()
    room, evidence = args.room.resolve(strict=True), args.evidence.resolve()
    if args.seconds <= 0 or args.units <= 0:
        parser.error('seconds and units must be positive')
    if not room.is_dir() or evidence == room or room in evidence.parents or evidence in room.parents:
        parser.error('room and evidence must be separate, non-nested directories')
    if evidence.exists() and any(evidence.iterdir()):
        parser.error('evidence directory must be new or empty')
    evidence.mkdir(parents=True, exist_ok=True)
    (evidence / 'prompt.txt').write_text(args.prompt.read_text())
    controller = Controller(room, evidence, args.seconds, args.units)
    async def run():
        loop = asyncio.get_running_loop()
        for sig in (signal.SIGTERM, signal.SIGINT):
            loop.add_signal_handler(sig, controller.request_stop, 'external_signal')
        return await controller.run(args.prompt.read_text())
    return asyncio.run(run())


if __name__ == '__main__':
    raise SystemExit(main())
