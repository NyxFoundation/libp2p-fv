#!/usr/bin/env python3
"""Check that Veil produces counterexamples for validation, session and dedup bypasses."""
import os
import signal
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def variant_source(source, old, new):
    if source.count(old) != 1:
        raise ValueError("mutation target must occur exactly once")
    model = source.split("#gen_spec", 1)[0].replace(old, new)
    model = model.replace('set_option veil.solver "grind"',
                          'set_option veil.deferVCGeneration true')
    checker = source.split("#model_check interpreted", 1)[1].split("sat trace", 1)[0]
    return model + "#gen_spec\n#model_check interpreted" + checker + "end Libp2p.Pipeline\n"


def check_variant(name, content, expected, directory):
    path = directory / f"{name}.lean"
    path.write_text(content)
    process = subprocess.Popen(["lake", "lean", str(path)], cwd=ROOT,
                               text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               start_new_session=True)
    try:
        output, _ = process.communicate(timeout=600)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        output, _ = process.communicate()
        (ROOT / "verification-output" / f"mutation-{name}.log").write_text(output)
        raise RuntimeError(f"mutation {name} exceeded its time limit") from None
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    (ROOT / "verification-output" / f"mutation-{name}.log").write_text(output)
    failure = next((line for line in output.splitlines()
                    if "Violation: safety_failure" in line), "")
    if expected is None:
        if process.returncode or "No violation" not in output:
            raise RuntimeError("positive control failed")
    elif process.returncode != 1 or expected not in failure or "State 0 (via init)" not in output:
        raise RuntimeError(f"mutation {name} did not expose the expected safety failure")
    print(f"PASS {name}: {'no violation' if expected is None else expected}")


def handle_termination(signum, _frame):
    raise SystemExit(128 + signum)


def main():
    signal.signal(signal.SIGTERM, handle_termination)
    source = (ROOT / "Libp2p/Pipeline.lean").read_text()
    old = "action deliver (w : task) {\n  require accepted w ∧ ¬ canceled w ∧ live (owner (source w)) ∧ ¬ reset (source w)"
    mutants = [
        ("control", old, None),
        ("validation-bypass", old.replace("accepted w ∧ ", ""), "validated_delivery"),
        ("stale-session", old.replace("live (owner (source w)) ∧ ", ""), "no_stale_effect"),
    ]
    (ROOT / "verification-output").mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="mutations-", dir=ROOT / ".lake") as directory:
        for name, replacement, expected in mutants:
            check_variant(name, variant_source(source, old, replacement), expected, Path(directory))
        collision = source.replace("task := Fin 1", "task := Fin 2")
        collision = collision.replace("object := Fin 1", "object := Fin 2")
        collision = collision.replace("context := Fin 1", "context := Fin 2")
        collision = collision.replace("payload := fun _ => 0", "payload := fun w => w")
        collision = collision.replace("scope := fun _ => 0", "scope := fun w => w")
        guard = "  require ¬ seen (key w)"
        check_variant("collision-control", variant_source(collision, guard, guard),
                      None, Path(directory))
        check_variant("deduplication-bypass", variant_source(collision, guard, ""),
                      "window_at_most_once", Path(directory))


if __name__ == "__main__":
    main()
