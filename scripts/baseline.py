#!/usr/bin/env python3
"""Read immutable source baselines from Git, without historical checkouts."""
from functools import lru_cache
from pathlib import Path, PurePosixPath
import argparse
import gzip
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PROJECT = ROOT / 'experiments/kl-for-mathlib'


def configuration(root=ROOT):
    data = json.loads((root / 'provenance/baselines.json').read_text())
    if data.get('schema') != 1:
        raise RuntimeError('Unsupported baseline configuration')
    return data


def relative_path(path):
    value = PurePosixPath(path)
    if value.is_absolute() or '..' in value.parts or not value.parts:
        raise ValueError('Expected a repository-relative baseline path')
    return value.as_posix()


class GitSnapshot:
    def __init__(self, role, root=ROOT, spec=None):
        self.root = root
        spec = spec or configuration(root)['snapshots'][role]
        self.commit = spec['commit']
        self.prefix = relative_path(spec['prefix'])
        if not re.fullmatch('[0-9a-f]{40}', self.commit):
            raise ValueError('Baseline must name an exact Git commit')
        result = subprocess.run(['git', 'cat-file', '-t', self.commit], cwd=root,
                                capture_output=True, text=True)
        if result.returncode or result.stdout.strip() != 'commit':
            raise RuntimeError('Missing baseline commit ' + self.commit +
                               '; run scripts/setup.sh or git fetch origin ' + self.commit)
        raw = subprocess.check_output(['git', 'ls-tree', '-rz', self.commit,
                                       '--', self.prefix + '/'], cwd=root)
        self.entries = {}
        for row in raw.split(b'\0'):
            if row:
                meta, name = row.split(b'\t', 1)
                mode, kind, sha = meta.decode().split()
                name = name.decode()
                if kind != 'blob' or mode not in ('100644', '100755'):
                    raise RuntimeError('Unexpected baseline tree entry: ' + name)
                self.entries[name[len(self.prefix) + 1:]] = sha
        if not self.entries:
            raise RuntimeError('Missing baseline source tree: ' + self.prefix)

    @lru_cache(maxsize=None)
    def read_bytes(self, path):
        path = relative_path(path)
        if path not in self.entries:
            raise RuntimeError('Missing baseline file: ' + path)
        data = subprocess.check_output(['git', 'cat-file', 'blob',
                                       self.commit + ':' + self.prefix + '/' + path], cwd=self.root)
        digest = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if digest != self.entries[path]:
            raise RuntimeError('Corrupt baseline Git blob: ' + path)
        return data

    def read_text(self, path):
        return self.read_bytes(path).decode()

    def files(self, prefix=''):
        return sorted(p for p in self.entries if p.startswith(prefix))


@lru_cache(maxsize=None)
def snapshot(role):
    return GitSnapshot(role)


def verify_export(root=ROOT, metadata=None):
    meta = metadata or configuration(root)['reference_export']
    packed = (root / relative_path(meta['path'])).read_bytes()
    if hashlib.sha256(packed).hexdigest() != meta['compressed_sha256']:
        raise RuntimeError('Reference export archive checksum mismatch')
    data = gzip.decompress(packed)
    if len(data) != meta['bytes'] or hashlib.sha256(data).hexdigest() != meta['sha256']:
        raise RuntimeError('Reference export content checksum mismatch')
    if meta['public_count'] != 3902:
        raise RuntimeError('Expected 3902 reference declarations')
    return data


def ensure_history(fetch_missing=False):
    for commit in sorted({s['commit'] for s in configuration()['snapshots'].values()}):
        present = subprocess.run(['git', 'cat-file', '-e', commit + '^{commit}'],
                                 cwd=ROOT, capture_output=True).returncode == 0
        if not present:
            if not fetch_missing:
                raise RuntimeError('Missing baseline history; run scripts/setup.sh or git fetch origin ' + commit)
            # Explicit setup-only read: no branch update, hooks, checkout or retry.
            subprocess.run(['git', 'fetch', '--no-tags', 'origin', commit], cwd=ROOT, check=True)
    for role in configuration()['snapshots']:
        snapshot(role)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fetch-missing', action='store_true', help='Fetch only missing pinned history during setup')
    parser.add_argument('--export-out', type=Path, help='Materialize checksum-verified type evidence, not a Lean project')
    args = parser.parse_args()
    ensure_history(args.fetch_missing)
    data = verify_export()
    if args.export_out:
        args.export_out.parent.mkdir(parents=True, exist_ok=True)
        if not args.export_out.exists() or args.export_out.read_bytes() != data:
            args.export_out.write_bytes(data)
    print('Immutable Git baseline trees and retained 3902-declaration export checksums verified.')


if __name__ == '__main__':
    main()
