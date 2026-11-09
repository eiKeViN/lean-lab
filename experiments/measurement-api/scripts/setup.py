#!/usr/bin/env python3
"""Prepare this experiment only, at fixed versions, using the official Mathlib cache."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import re
import subprocess

from common import ROOT, environment, logged, sha, source_identity


def checkout(entry):
    path, url, rev = entry
    if (path / '.git').exists():
        head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=path,
                                       text=True).strip()
        if head != rev:
            raise RuntimeError(f'Preserve existing checkout with another revision: {path}')
        return
    if path.exists() and any(path.iterdir()):
        raise RuntimeError(f'Preserve nonempty unrecognized directory: {path}')
    path.mkdir(parents=True, exist_ok=True)
    subprocess.run(['git', 'init', '--quiet', str(path)], check=True)
    subprocess.run(['git', 'remote', 'add', 'origin', url], cwd=path, check=True)
    subprocess.run(['git', 'fetch', '--depth', '1', 'origin', rev], cwd=path,
                   check=True, env=environment())
    subprocess.run(['git', 'checkout', '--quiet', '--detach', 'FETCH_HEAD'], cwd=path,
                   check=True, env=environment())


def cache_roots():
    seen, roots = set(), {'Mathlib.Probability.ProbabilityMassFunction.Constructions'}

    def visit(module):
        if module in seen:
            return
        seen.add(module)
        path = ROOT / 'vendor/physlib' / (module.replace('.', '/') + '.lean')
        for line in path.read_text().splitlines():
            match = re.match(r'\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.]+)', line)
            if not match:
                continue
            imported = match.group(1)
            if imported.startswith('Mathlib.'):
                roots.add(imported)
            elif imported.startswith(('QuantumInfo.', 'PhyslibAlpha.')):
                visit(imported)

    for module in ['QuantumInfo.Measurements.POVM', 'QuantumInfo.Channels.Dual',
                   'QuantumInfo.ResourceTheory.HypothesisTesting']:
        visit(module)
    (ROOT / 'results/dependency-closure.json').write_text(json.dumps({
        'physlib': sorted(seen), 'mathlib_cache_roots': sorted(roots)
    }, indent=2) + '\n')
    return sorted(roots)


def main():
    pins = json.loads((ROOT / 'provenance/upstream.json').read_text())
    for name in ['downloads', 'toolchain', 'results']:
        (ROOT / name).mkdir(exist_ok=True)
    archive = ROOT / 'downloads/lean-4.35.0-linux.tar.zst'
    if not archive.exists():
        partial = archive.with_suffix(archive.suffix + '.part')
        subprocess.run(['curl', '-fL', '--retry', '2',
                        'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst',
                        '-o', str(partial)], check=True)
        if sha(partial) != pins['lean_archive_sha256']:
            raise RuntimeError('Downloaded Lean archive identity differs; preserve it for inspection')
        partial.rename(archive)
    if sha(archive) != pins['lean_archive_sha256']:
        raise RuntimeError('Lean archive checksum differs')
    if not (ROOT / 'toolchain/lean-4.35.0-linux/bin/lean').exists():
        subprocess.run(['tar', '--zstd', '-xf', str(archive), '-C', str(ROOT / 'toolchain')], check=True)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    entries = [(ROOT / '.lake/packages' / p['name'], p['url'], p['rev'])
               for p in manifest['packages']]
    entries.append((ROOT / 'vendor/physlib',
                    'https://github.com/leanprover-community/physlib.git', pins['physlib']))
    with ThreadPoolExecutor(max_workers=4) as pool:
        list(pool.map(checkout, entries))
    identity = source_identity()
    (ROOT / 'results/setup-source-identity.json').write_text(json.dumps(identity, indent=2) + '\n')
    logged(['python3', 'scripts/materialize.py'], 'materialize')
    logged(['lean', '--version'], 'lean-version')
    logged(['lake', 'exe', 'cache', 'get', *cache_roots()], 'cache-get')
    print('Pinned setup ready. Upstream Physlib Lake configuration was not executed.')


if __name__ == '__main__':
    main()
