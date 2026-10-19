# Source from another lab script or an interactive bash session.
LAB_ROOT="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
export ELAN_HOME="${ELAN_HOME:-$LAB_ROOT/.cache/elan}"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$LAB_ROOT/.cache/mathlib}"
export MATHLIB_NO_CACHE_ON_UPDATE=1
# Lean/Lake otherwise sees the host CPU count, not the container quota.
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
