import importlib.util
import os
import signal
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("verify_gate", ROOT / "scripts/verify.py")
GATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GATE)


class VerificationRunnerTests(unittest.TestCase):
    def test_should_discover_all_lean_tests_when_suites_are_nested(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Routing").mkdir()
            expected = [root / "Axioms.lean", root / "Network.lean",
                        root / "Routing/Reachability.lean"]
            for path in expected + [root / "test_verify.py", root / "Network.log"]:
                path.touch()
            self.assertEqual(GATE.lean_test_files(root), tuple(expected))

    def test_should_return_log_when_command_succeeds(self):
        with tempfile.TemporaryDirectory() as directory:
            output = GATE.run("success", [sys.executable, "-c", "print('evidence')"],
                              Path(directory), 5)
            self.assertEqual(output.strip(), "evidence")

    def test_should_fail_when_command_exits_nonzero(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "failed"):
                GATE.run("failure", [sys.executable, "-c", "raise SystemExit(2)"],
                         Path(directory), 5)

    def test_should_accept_expected_failure_when_status_matches(self):
        with tempfile.TemporaryDirectory() as directory:
            output = GATE.run("expected-failure", [sys.executable, "-c", "print('rejected'); raise SystemExit(1)"],
                              Path(directory), 5, expected_exit=1)
            self.assertEqual(output.strip(), "rejected")

    def test_should_reject_unexpected_success_when_failure_is_required(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "failed"):
                GATE.run("unexpected-success", [sys.executable, "-c", "pass"],
                         Path(directory), 5, expected_exit=1)

    def test_should_fail_when_command_exceeds_timeout(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "TimeoutExpired"):
                GATE.run("timeout", [sys.executable, "-c", "import time; time.sleep(60)"],
                         Path(directory), 0.1)

    def test_should_stop_mutation_child_when_outer_command_times_out(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "Libp2p").mkdir()
            (root / ".lake").mkdir()
            (root / "Libp2p/Pipeline.lean").write_text((ROOT / "Libp2p/Pipeline.lean").read_text())
            pidfile = root / "child.pid"
            lake = root / "lake"
            lake.write_text(f"#!{sys.executable}\nimport os, time\nfrom pathlib import Path\n"
                            f"Path({str(pidfile)!r}).write_text(str(os.getpid()))\ntime.sleep(60)\n")
            lake.chmod(0o700)
            helper = (f"import os, sys; from pathlib import Path; "
                      f"sys.path.insert(0, {str(ROOT / 'scripts')!r}); import check_mutations; "
                      f"check_mutations.ROOT = Path({directory!r}); "
                      f"os.environ['PATH'] = {directory!r} + os.pathsep + os.environ['PATH']; "
                      "check_mutations.main()")
            try:
                with self.assertRaisesRegex(RuntimeError, "TimeoutExpired"):
                    GATE.run("mutation-timeout", [sys.executable, "-c", helper], root, 2)
                self.assertTrue(pidfile.exists(), "mutation child must have started")
                with self.assertRaises(ProcessLookupError):
                    os.kill(int(pidfile.read_text()), 0)
            finally:
                if pidfile.exists():
                    try:
                        os.killpg(int(pidfile.read_text()), signal.SIGKILL)
                    except ProcessLookupError:
                        pass

    def test_should_fail_when_executable_is_missing(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(RuntimeError, "FileNotFoundError"):
                GATE.run("missing", [str(Path(directory) / "nonexistent")], Path(directory), 5)


if __name__ == "__main__":
    unittest.main()
