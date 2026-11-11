# Comparator runtime: Lean 4.33.1

Functional optional checker shared identically by both arms through room.py's read-only /opt/comparator mount. The original upstream comparator binary is preserved as comparator. No room.py changes or fake-landrun were used.

## Source pins

- Comparator: https://github.com/leanprover/comparator/commit/c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809 (last v4.33.0-era commit before toolchain bumped to v4.34.0-rc1).
- lean4export: https://github.com/leanprover/lean4export/commit/15f6055e299ad5b89345e533cc2192f4cc00f659 (Comparator's pinned dependency).
- Both compiled unmodified using bundled official Lean 4.33.1; source lean-toolchain files retain their upstream v4.33.0 declarations. Explicit PATH selected actual v4.33.1 lake/lean.
- landrun: https://github.com/Zouuup/landrun/commit/ec104f6edc1e14d7fec6d31146f1ec6f9c192c5a, reports 0.1.18; compiled from source with `go build -buildvcs=false -o ../comparator-bin/landrun ./cmd/landrun`.
- Go: official go1.27.4.linux-amd64.tar.gz, SHA256 7226736c2339719cda28fbf3a54d71aa63bcefe376e98cef00034268dab24840 checked against https://go.dev/dl/?mode=json.
- which: exact copy of installed /usr/bin/which.debianutils. Necessary because /usr/bin/which resolves through /etc/alternatives, absent in room's intentionally minimal /etc mounts.

Binaries' digests are in SHA256SUMS. Source trees are ../comparator-4.33 and ../landrun. The existing ../comparator (4.35.0 source) was not changed. No project repository commits made.

## Verification scope and security limitation

SMOKE-TEST.log records actual executions through unchanged supervision/room.py with HGP_RUNTIME_ROOT pointing to this runtime root:

- Matching theorem `1 + 1 = 2`, proof by decide: exit 0, kernel accepts.
- Different statement `1 + 1 = 3`: exit 1, statement mismatch.
- Matching statement with sorry: exit 1, illegal axiom sorryAx.
- Built-in `lake env leanchecker Solution -v`: exit 0, replaying Solution.
- Strict real landrun: exit 1, kernel Landlock ABI v0, unavailable.
- Read-only best-effort landrun probe was able to create /work/should-not-exist: exit 0. Upstream Comparator hardcodes --best-effort, so its internal Landlock protection is absent on this platform.

The functional results DO NOT establish upstream standalone comparator's adversarial security guarantee. The unchanged outer room mount/PID/seccomp sandbox still isolates each participant from supervisor resources, but it allows writes throughout that participant's /work. Therefore the common protocol must continue to rebuild supervisor-controlled source and perform axiom/semantic checks, rather than trusting the participant's comparator output. leanchecker is kernel replay, not an independent kernel, theorem-statement comparison, or axiom policy checker. Lean 4.33.1 has no lake check or lake comparator; those arrived in 4.35.0.

Usage inside either room: `lake env comparator config.json`. Required JSON fields include challenge_module, solution_module, theorem_names, permitted_axioms, enable_nanoda (set false). Challenge and solution modules should be distinct; permit only the intended foundational axioms.
