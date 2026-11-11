"""Source-only planning workspace with no network sockets or participant host access."""
import ctypes,errno,os,signal,subprocess,tempfile
from pathlib import Path
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
    for p in ("/usr", "/bin", "/lib", "/lib64", "/etc/ld.so.cache", "/etc/passwd", "/etc/group", "/etc/alternatives"):
        if Path(p).exists():
            args += ["--ro-bind", p, p]
    rg = Path("/usr/local/bin/rg")
    if rg.exists():
        args += ["--ro-bind", str(rg.resolve()), "/tools/rg"]
    args += ["--dev", "/dev", "--proc", "/proc", "--tmpfs", "/tmp",
             "--dir", "/home/agent", "--bind", str(room), "/work",
             "--setenv", "HOME", "/home/agent", "--setenv", "LANG", "C.UTF-8",
             "--setenv", "PATH", "/tools:/usr/local/bin:/usr/bin:/bin",
             "--chdir", "/work", "--seccomp", str(fd), "--", "/bin/bash", "-c", command]
    try:
        with tempfile.TemporaryFile() as out:
            proc = subprocess.Popen(args, stdin=subprocess.DEVNULL, stdout=out, stderr=subprocess.STDOUT,
                                    start_new_session=True, pass_fds=(fd,), env={"PATH":"/usr/bin:/bin"})
            try:
                code = proc.wait(timeout=max(1,min(600,int(timeout))))
                status = f"exit {code}"
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid,signal.SIGKILL)
                proc.wait()
                status = "command timed out"
            n=out.tell()
            out.seek(0)
            data=out.read(56000)
            if n>56000:data+=b"\n... output truncated ..."
            return f"[{status}]\n"+data.decode(errors="replace")
    finally:
        os.close(fd)
