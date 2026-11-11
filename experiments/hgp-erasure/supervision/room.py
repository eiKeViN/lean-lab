"""Run one shell command in a mount/PID namespace with no network sockets.

The caller owns the room directory. Trusted immutable dependencies are shared,
and the only persistent writable mount is the current participant's room.
"""
import ctypes
import errno
import os
from pathlib import Path
import signal
import subprocess
import tempfile

BASE = Path(os.environ.get("HGP_RUNTIME_ROOT", Path.cwd())).resolve()
LEAN = BASE / "runtime/lean-4.33.1-linux"
QEC = BASE / "qecert"


def network_filter():
    lib = ctypes.CDLL("libseccomp.so.2")
    lib.seccomp_init.argtypes = [ctypes.c_uint32]
    lib.seccomp_init.restype = ctypes.c_void_p
    lib.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    lib.seccomp_syscall_resolve_name.restype = ctypes.c_int
    lib.seccomp_rule_add.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_int, ctypes.c_uint]
    lib.seccomp_export_bpf.argtypes = [ctypes.c_void_p, ctypes.c_int]
    lib.seccomp_release.argtypes = [ctypes.c_void_p]
    ctx = lib.seccomp_init(0x7fff0000)
    if not ctx:
        raise RuntimeError("seccomp init failed")
    fd = os.memfd_create("room-network-policy")
    try:
        for name in ("socket", "connect", "bind", "listen", "accept", "accept4",
                     "io_uring_setup", "ptrace", "process_vm_writev", "pidfd_getfd",
                     "open_by_handle_at", "bpf"):
            nr = lib.seccomp_syscall_resolve_name(name.encode())
            if nr >= 0 and lib.seccomp_rule_add(ctx, 0x00050000 | errno.EPERM, nr, 0):
                raise RuntimeError(f"seccomp rule failed for {name}")
        if lib.seccomp_export_bpf(ctx, fd):
            raise RuntimeError("seccomp export failed")
        os.lseek(fd, 0, os.SEEK_SET)
    except BaseException:
        os.close(fd)
        raise
    finally:
        lib.seccomp_release(ctx)
    return fd


def execute(room_path: Path, command: str, timeout: int) -> str:
    room = Path(room_path).resolve(strict=True)
    fd = network_filter()
    args = ["bwrap", "--unshare-pid", "--unshare-ipc", "--unshare-uts",
            "--die-with-parent", "--new-session", "--clearenv"]
    for p in ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache", "/etc/passwd", "/etc/group"):
        if Path(p).exists():
            args += ["--ro-bind", p, p]
    args += ["--ro-bind", str(BASE / "runtime/lean4-skills"), "/opt/lean4-skills"]
    rg = Path("/usr/local/bin/rg")
    if rg.exists():
        args += ["--ro-bind", str(rg.resolve()), "/tools/rg"]
    bindir = BASE / "runtime/comparator-bin"
    for name in ("comparator","lean4export","landrun","which"):
        if (bindir / name).is_file():
            args += ["--ro-bind", str(bindir / name), "/opt/comparator/" + name]
    args += ["--ro-bind", str(Path(__file__).with_name("comparator-help.md")), "/opt/comparator/README.md"]
    args += ["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
             "--dir", "/home/agent", "--ro-bind", str(LEAN), "/opt/lean",
             "--ro-bind", str(QEC), "/opt/qecert", "--bind", str(room), "/work",
             "--setenv", "HOME", "/home/agent", "--setenv", "LANG", "C.UTF-8",
             "--setenv", "PATH", "/opt/lean/bin:/opt/comparator:/tools:/usr/local/bin:/usr/bin:/bin",
             "--setenv", "GIT_AUTHOR_NAME", "Participant", "--setenv", "GIT_AUTHOR_EMAIL", "participant@localhost",
             "--setenv", "GIT_COMMITTER_NAME", "Participant", "--setenv", "GIT_COMMITTER_EMAIL", "participant@localhost",
             "--setenv", "LEAN_NUM_THREADS", "2",
             "--chdir", "/work", "--seccomp", str(fd), "--", "/bin/bash", "-c", command]
    try:
        with tempfile.TemporaryFile() as out:
            proc = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                                    start_new_session=True, pass_fds=(fd,), env={"PATH":"/usr/bin:/bin"})
            try:
                code = proc.wait(timeout=max(1, min(600, int(timeout))))
                status = f"exit {code}"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
                status = "command timed out"
            n = out.tell()
            out.seek(0)
            if n > 56000:
                data = out.read(26000) + b"\n... output truncated ...\n"
                out.seek(-28000, 2)
                data += out.read()
            else:
                data = out.read()
            return f"[{status}]\n" + data.decode(errors="replace")
    finally:
        os.close(fd)
