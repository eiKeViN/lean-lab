#!/usr/bin/env bash
# Host preparation only. Participants use lean-project with /opt mounts offline.
set -euo pipefail
runtime_root=${HGP_RUNTIME_ROOT:-$(cd -- "$(dirname -- "$0")/../../../.." && pwd)}
runtime_root=$(cd -- "$runtime_root" && pwd)
qec="$runtime_root/qecert"
export PATH="$runtime_root/runtime/lean-4.33.1-linux/bin:$PATH"
[[ $(git -C "$qec" rev-parse HEAD) == c0ff74952c65b48e2ba5430fc4dfa4459d120440 ]]
git -C "$qec" diff --quiet HEAD
[[ $(lean --version) == 'Lean (version 4.33.1,'* ]]
python3 - "$qec" <<'PY'
import json, subprocess, sys
from pathlib import Path
root=Path(sys.argv[1])
manifest=json.loads((root/'lake-manifest.json').read_text())
for p in manifest['packages']:
    actual=subprocess.check_output(['git','-C',str(root/'.lake/packages'/p['name']),'rev-parse','HEAD'],text=True).strip()
    if actual != p['rev']:
        raise SystemExit(f"pin mismatch for {p['name']}: {actual} != {p['rev']}")
print('All dependency source revisions match the frozen manifest.')
PY
wrapper=$(mktemp -d)
trap 'rm -rf -- "$wrapper"' EXIT
cat > "$wrapper/curl" <<'CURL'
#!/usr/bin/env bash
# --rate is ineffective with --parallel. Remove that flag and transfer serially.
args=()
for arg in "$@"; do
  if [[ "$arg" != --parallel ]]; then args+=("$arg"); fi
done
exec /usr/bin/curl --rate 8/s "${args[@]}"
CURL
chmod +x "$wrapper/curl"
export PATH="$wrapper:$PATH"
cd -- "$qec"
# QEC imports the Mathlib umbrella: the full binary cache is its import closure.
# This does not build Mathlib from source. Re-running resumes missing downloads.
lake exe cache get Mathlib
# Refuse a fallback whole-Mathlib build if the binary umbrella remains absent.
printf 'import Mathlib\n' | lake env lean --stdin || {
  echo 'Mathlib cache is incomplete; rerun cache preparation after rate limits reset.' >&2
  exit 1
}
lake build QEC.Results.QLDPC.HypergraphProductParameters
