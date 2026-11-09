"""Keep KL layout checks strict while allowing registered independent projects."""
from pathlib import Path
import tempfile
import unittest
from validate import check_project_layout


class ProjectLayoutTests(unittest.TestCase):
    def check_layout(self, names):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / 'experiments').mkdir()
            for name in names:
                (root / 'experiments' / name).mkdir()
            check_project_layout(root)

    def test_kl_alone(self):
        self.check_layout({'kl-for-mathlib'})

    def test_known_independent_projects(self):
        for extra in ({'stabilizer-api'}, {'measurement-api'},
                      {'stabilizer-api', 'measurement-api'}):
            with self.subTest(extra=extra):
                self.check_layout({'kl-for-mathlib'} | extra)

    def test_unknown_or_retired_copy_is_rejected(self):
        for extra in ('old-kl-copy', 'unexpected-project'):
            with self.subTest(extra=extra), self.assertRaises(RuntimeError):
                self.check_layout({'kl-for-mathlib', extra})

    def test_independent_projects_do_not_replace_kl(self):
        with self.assertRaises(RuntimeError):
            self.check_layout({'stabilizer-api', 'measurement-api'})


if __name__ == '__main__':
    unittest.main()
