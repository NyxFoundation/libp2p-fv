#!/usr/bin/env python3
"""Build Veil models, rerun their checks, test policies and reject proof holes."""
import argparse
import os
import signal
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODELS = ("Pipeline", "Routing", "Cache", "TemporalBackoff", "TemporalLimits",
          "TemporalCredit", "TemporalRetention", "TemporalCausality")


def stop(process):
    try:
        os.killpg(process.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.wait()


def handle_termination(signum, _frame):
    raise SystemExit(128 + signum)


def run(label, command, output, timeout, expected_exit=0):
    print(f"RUN {label}", flush=True)
    try:
        with (output / f"{label}.log").open("w") as log:
            process = subprocess.Popen(command, cwd=ROOT, stdout=log,
                                       stderr=subprocess.STDOUT, start_new_session=True)
            try:
                code = process.wait(timeout=timeout)
            except BaseException:
                stop(process)
                raise
    except (OSError, subprocess.TimeoutExpired) as error:
        raise RuntimeError(f"{label} could not finish ({type(error).__name__})") from error
    if code != expected_exit:
        raise RuntimeError(f"{label} failed; see verification-output/{label}.log")
    return (output / f"{label}.log").read_text()


def lean_test_files(root):
    return tuple(sorted(root.rglob("*.lean")))


def check_axiom_guard(output, timeout):
    source = (ROOT / "Tests/Axioms.lean").read_text()
    cases = [
        ("axiom", "axiom Libp2p.auditSentinel : False",
         "project axiom is forbidden: Libp2p.auditSentinel"),
        ("sorry", "theorem Libp2p.auditSentinel : False := by sorry",
         "nonstandard axioms in Libp2p.auditSentinel:"),
        ("native", "theorem Libp2p.auditSentinel : (1 : Nat) + 1 = 2 := by native_decide",
         "nonstandard axioms in Libp2p.auditSentinel:"),
    ]
    with tempfile.TemporaryDirectory(prefix="axiom-guard-", dir=ROOT / ".lake") as directory:
        for name, declaration, expected in cases:
            path = Path(directory) / f"{name}.lean"
            path.write_text(source.replace("open Lean in", declaration + "\n\nopen Lean in", 1))
            text = run(f"reject-{name}", ["lake", "lean", str(path)], output,
                       timeout, expected_exit=1)
            if f"error: {expected}" not in text:
                raise RuntimeError(f"axiom guard did not reject the {name} sentinel")


def main():
    signal.signal(signal.SIGTERM, handle_termination)
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=int, default=3600, help="seconds per command")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    output = ROOT / "verification-output"
    output.mkdir(exist_ok=True)
    try:
        run("coverage", [sys.executable, "scripts/check_coverage.py"], output, args.timeout)
        run("build", ["lake", "build"], output, args.timeout)
        for model in MODELS:
            text = run(model.lower(), ["lake", "lean", f"Libp2p/{model}.lean"],
                       output, args.timeout)
            if "No violation" not in text:
                raise RuntimeError(f"{model} lacks model-checking evidence")
        for proof in sorted((ROOT / "Libp2p").glob("*Safety.lean")):
            run(f"{proof.stem.lower()}-proof", ["lake", "lean", str(proof)],
                output, args.timeout)
        for test in lean_test_files(ROOT / "Tests"):
            label = test.relative_to(ROOT / "Tests").with_suffix("").as_posix().replace("/", "-")
            run(label.lower(), ["lake", "lean", str(test)], output, args.timeout)
        check_axiom_guard(output, args.timeout)
        run("mutations", [sys.executable, "scripts/check_mutations.py"], output, args.timeout)
        run("ledger-tests", [sys.executable, "-m", "unittest", "discover", "-s", "Tests",
                             "-p", "test_*.py"], output, args.timeout)
    except RuntimeError as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    print("PASS: model checks, reachability proofs, Lean tests, axiom audit and ledger checks.")
    print("This gate verifies the artifact, not completion of every inventory obligation.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
