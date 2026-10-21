#!/usr/bin/env python3
"""Verify immutable pristine Git blobs and the maintained project's dependency pins."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
from baseline import ROOT, PROJECT, snapshot, ensure_history


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def verify_sources(source, rows, upstream):
    require(len(rows) == 34, 'Expected 34 source blobs')
    actual = {p for p in source.files('OAI/') if p.endswith('.lean')}
    require(actual == {path for _, path in rows}, 'Source file set mismatch')
    for sha, path in rows:
        data = source.read_bytes(path)
        got = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        require(got == sha == upstream['lean/' + path], 'Source hash mismatch: ' + path)
        for line in data.decode().splitlines():
            if line.startswith('import '):
                for module in line[7:].split():
                    require(module == 'Mathlib' or module.replace('.', '/') + '.lean' in actual,
                            'Missing baseline import: ' + module)


def verify_project(project=PROJECT):
    baseline = snapshot('published')
    require((project/'lean-toolchain').read_bytes() == baseline.read_bytes('lean-toolchain'),
            'Toolchain pin mismatch')
    require((project/'lake-manifest.json').read_bytes() == baseline.read_bytes('lake-manifest.json'),
            'Dependency lock manifest mismatch')
    manifest = json.loads((project/'lake-manifest.json').read_text())
    packages = project/'.lake/packages'
    require(not packages.is_symlink(), 'The maintained project must own its dependency directory')
    for dep in manifest['packages']:
        directory = packages/dep['name']
        if directory.exists():
            actual = subprocess.check_output(['git', '-C', str(directory), 'rev-parse', 'HEAD'], text=True).strip()
            require(actual == dep['rev'], 'Dependency revision mismatch: ' + dep['name'])
            subprocess.run(['git', '-C', str(directory), 'diff', '--quiet', 'HEAD', '--'], check=True)


def verify():
    ensure_history()
    rows = [line.split('\t') for line in (ROOT/'provenance/kl-blobs.tsv').read_text().splitlines()]
    upstream = {path: sha for _, sha, path in
                [x.split('\t') for x in (ROOT/'provenance/upstream.manifest.tsv').read_text().splitlines()[1:]]}
    verify_sources(snapshot('pristine'), rows, upstream)
    verify_project()
    print('34 pristine Git blobs match the upstream manifest; active toolchain, lockfile and available dependencies match.')


if __name__ == '__main__':
    try:
        verify()
    except (RuntimeError, OSError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
