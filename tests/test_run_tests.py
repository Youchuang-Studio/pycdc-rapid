#!/usr/bin/env python3

import os
import tempfile
import unittest
from unittest import mock

import run_tests


class RunTestsStatusTests(unittest.TestCase):
    def run_fixture(self, compiled, xfail, decompyle_one):
        with tempfile.TemporaryDirectory() as test_dir:
            for directory in ('compiled', 'xfail', 'tokenized'):
                os.makedirs(os.path.join(test_dir, directory))
            with open(os.path.join(test_dir, 'tokenized', 'fixture.txt'), 'w') as tokenized:
                tokenized.write('')
            if compiled:
                open(os.path.join(test_dir, 'compiled', 'fixture.3.11.pyc'), 'w').close()
            if xfail:
                open(os.path.join(test_dir, 'xfail', 'fixture.3.11.pyc'), 'w').close()

            with mock.patch.object(run_tests, 'TEST_DIR', test_dir), \
                    mock.patch.object(run_tests, 'decompyle_one', side_effect=decompyle_one):
                return run_tests.run_test(os.path.join(test_dir, 'tokenized', 'fixture.txt'))

    def test_xpass_fails_and_is_reported(self):
        failures, output = self.run_fixture(
                compiled=False, xfail=True, decompyle_one=lambda *args: (True, []))
        self.assertEqual(failures, 1)
        self.assertIn('XPASS (1)', output[0])

    def test_mixed_pass_and_xfail_reports_both_counts(self):
        def decompyle_one(test_name, pyc_file, outdir, tokenized_expect):
            return ('xfail' not in pyc_file, [])

        failures, output = self.run_fixture(
                compiled=True, xfail=True, decompyle_one=decompyle_one)
        self.assertEqual(failures, 0)
        self.assertIn('PASS (1)', output[0])
        self.assertIn('XFAIL (1)', output[0])


if __name__ == '__main__':
    unittest.main()
