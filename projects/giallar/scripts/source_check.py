#!/usr/bin/env python3
"""Check source layout and record exactly which checked source files were delivered."""
from pathlib import Path
import hashlib
import json
import re

sources = [Path('Giallar.lean'), *sorted(Path('Giallar').glob('*.lean'))]
records = []
for source in sources:
    text = source.read_text()
    assert text.startswith('/-\nCopyright'), f'{source}: copyright header missing'
    assert '\nmodule\n' in text, f'{source}: explicit module boundary missing'
    assert '/-!\n# ' in text, f'{source}: module documentation missing'
    assert not re.search(r'^.*import Mathlib\s*$', text, re.M), source
    assert not re.search(r'linter\.[\w.]+ false', text), source
    for n, line in enumerate(text.splitlines(), 1):
        assert len(line) <= 100, f'{source}:{n}: line exceeds 100 columns'
    records.append({'path': str(source), 'sha256': hashlib.sha256(source.read_bytes()).hexdigest()})
Path('evidence/sources.json').write_text(json.dumps(records, indent=2) + '\n')
print(f'Checked {len(records)} source modules: headers, documentation, line widths and hashes')
