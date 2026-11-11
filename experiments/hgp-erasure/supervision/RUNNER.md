# Experimental controller

```sh
HGP_RUNTIME_ROOT=/absolute/experiment-root python supervision/runner.py \
  --room /absolute/participant-room \
  --evidence /absolute/separate-evidence-directory \
  --prompt /absolute/supervisor-prompt.txt --seconds 1200 --units 12000000
```

The evidence directory must be empty and outside the room, and neither directory
may contain the other. The room shell runs at `/work`; commands needing the Lean
project must explicitly `cd` into its directory. `room.execute` owns the shell's
filesystem/network restrictions and trusted runtime dependency mounts.

Every agent receives the same dynamic capabilities: `shell`, `spawn_agent`,
`agent_status`, `wait_agent`, `send_message`, and `checkpoint`. Spawn returns
immediately with an `id` such as `agent-2`; the child starts asynchronously with
only its explicit role/task and the shared filesystem. No parent transcript is
inherited. There are four live agent slots including the launcher. Completed
agents release a slot, and a message to a completed agent starts a follow-up in
that independent context. The run continues after launcher completion until all
children finish or the external budget stops it.

All model calls explicitly use `gpt-6.1-sol` with `high` reasoning and provider
fallback disabled. Native collaboration is disabled via `[agents] enabled=false`
and any native collaboration activity fails closed. Apps, plugins, memories,
web search, and native shell are disabled. Every thread and turn supplies
`environments: []`. The CLI receives a fresh isolated configuration/home and uses
only its normal read-only authentication file; the room never mounts that home.
No account-environment tools or personal context capabilities are supplied.

`events.jsonl` contains RPC requests, model output, tool input/output, spawn
prompts, per-thread usage updates, aggregate usage, and termination events.
`agents.json` and `summary.json` contain final statuses and answers. Initial,
every-minute, agent-requested, and final filesystem copies are saved under
`snapshots/`; these copy symlinks without following them. A live snapshot is a
best-effort copy, not a transaction across simultaneous room writes.

Token cost units are `16 * output + 8 * (input - cached_input) + cached_input`.
Reasoning tokens are recorded separately and are already included in output.
Each thread's cumulative totals are counted once; notifications do not add a
second copy of earlier usage. The controller terminates on the first reported
aggregate reaching the cap. Provider usage notifications arrive at model-step
boundaries, so in-flight work can exceed the cap and cancelled work may have
usage not yet reported. The wall watchdog independently stops the server and
shell helper process groups, including while model initialization or tools are
running. The final evidence copy happens after those processes are terminated.

No actual experimental subjects are launched by importing this module or by
its verification probes. Temporary non-mathematical smoke runs are under the
workspace's `preflight/` directory.
