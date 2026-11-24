These Lean files are derived from Google DeepMind's
`google-deepmind/formal-quantum-computation`, commit
`a88de8ff65d78af564b2373088ca369dc95f6547` (Apache-2.0).
Original copyright headers and LICENSE are retained.

`Core` and `Stream` retain the complete corresponding source modules. `Shared`
ends immediately before `theorem c2_0`; `Stage1` ends immediately before
`theorem c1_0`. Those slices append the two closing `end` commands. Imports of
these four modules are renamed to `FQCExternal.Vendor.*`; all other text in the
slices is retained. No upstream Lake configuration is executed.

`../../provenance/upstream.json` records full original SHA-256, Git blob SHA-1,
slice boundaries, derived hashes, selected certificate hashes and the retained
public proposition. `scripts/source.py` reproduces and checks these identities
from the exact public snapshot. Original data-bearing files are cached outside
Git; they are not imported by the admitted proof.

The trailing whitespace on upstream `Core.lean` line 772 is intentionally
retained for exact source identity. Whitespace checks on newly authored code
exclude these source-preserving vendor snapshots; their byte identity is checked
instead by the provenance verifier.
