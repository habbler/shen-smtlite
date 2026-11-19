"""Check the example models and compare generated SMT-LIB cases against Z3."""

import argparse
from pathlib import Path
import random
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent


def run(command):
    result = subprocess.run(
        command, cwd=ROOT, capture_output=True, text=True, timeout=30
    )
    if result.returncode or result.stderr:
        raise RuntimeError(f"{command!r} exited {result.returncode}\n{result.stderr}")
    return result.stdout


def statuses(output):
    return re.findall(r"^(sat|unsat)$", output, re.MULTILINE)


def generated_cases():
    rng = random.Random(20261119)
    cases = []
    for index in range(192):
        width = rng.randrange(1, 6)
        size = 1 << width

        def term(depth):
            if depth == 0:
                return rng.choice(["x", "y", f"(_ bv{rng.randrange(size)} {width})"])
            if rng.randrange(4) == 0:
                return f"({rng.choice(['bvnot', 'bvneg'])} {term(depth - 1)})"
            op = rng.choice(["bvadd", "bvsub", "bvand", "bvor", "bvxor"])
            return f"({op} {term(depth - 1)} {term(depth - 1)})"

        def atom():
            op = rng.choice(["=", "distinct", "bvult", "bvule", "bvugt", "bvuge"])
            return f"({op} {term(2)} {term(2)})"

        first, second, third, fourth = (atom() for _ in range(4))
        lines = [
            "(reset)", "(set-logic QF_BV)",
            f"(declare-const x (_ BitVec {width}))",
            f"(declare-const y (_ BitVec {width}))",
            "(declare-const flag Bool)",
            f"(assert (= flag {first}))",
            f"(assert (ite flag (xor {second} {third}) (=> {second} {fourth})))",
        ]
        if index % 2 == 0:
            lines += [f"(assert {first})", f"(assert {third})"]
        if index % 3 == 0:
            lines += [f"(assert (= x (_ bv{rng.randrange(size)} {width})))"]
        cases.append("\n".join([*lines, "(check-sat)"]))
    return cases


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("shen", type=Path)
    parser.add_argument("z3", type=Path)
    args = parser.parse_args()
    shen = [str(args.shen.resolve()), "script", "run.shenmod"]
    z3 = [str(args.z3.resolve()), "-smt2"]
    examples = {
        "smoke": {"x": "#b110", "y": "false"},
        "fish": {"german": "#b100", "fish": "#b100"},
    }
    for name, model in examples.items():
        source = ROOT / "examples" / f"{name}.smt2"
        for backend in (shen, z3):
            output = run([*backend, str(source)])
            got = dict(re.findall(r"\((\w+)\s+(#b[01]+|true|false)\)", output))
            if statuses(output) != ["sat", "unsat"] or got != model:
                raise AssertionError((name, backend, output))

    cases = generated_cases()
    with tempfile.TemporaryDirectory() as work:
        source = Path(work) / "generated.smt2"
        source.write_text("\n".join(cases), encoding="ascii")
        expected = statuses(run([*z3, str(source)]))
        actual = statuses(run([*shen, str(source)]))
    if len(expected) != len(cases) or len(actual) != len(cases):
        raise AssertionError(f"expected {len(cases)} results, got {len(expected)} and {len(actual)}")
    for number, (want, got) in enumerate(zip(expected, actual), start=1):
        if want != got:
            raise AssertionError(f"case {number}: Z3={want}, Shen={got}\n{cases[number - 1]}")
    print(f"Both examples and {len(cases)} generated cases matched Z3 "
          f"({actual.count('sat')} sat, {actual.count('unsat')} unsat).")


if __name__ == "__main__":
    main()
