#!/usr/bin/env python3
"""Print the exact Mathlib import frontier of this project's source dependencies."""
from pathlib import Path
import re

roots = [Path('.'), Path('.lake/packages/Physlib')]
seen, frontier = set(), set()


def visit(module):
    if module in seen:
        return
    seen.add(module)
    if module.startswith('Mathlib.'):
        frontier.add(module)
        return
    for root in roots:
        source = root / (module.replace('.', '/') + '.lean')
        if source.is_file():
            for line in source.read_text().splitlines():
                match = re.match(r'^(?:public )?import (.+)$', line)
                if match:
                    for dependency in match[1].split():
                        if dependency.startswith(('Mathlib.', 'QuantumInfo.', 'Giallar')):
                            visit(dependency)
            return


visit('Giallar')
print('\n'.join(sorted(frontier)))
