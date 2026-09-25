import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[2]


def check_negative_controls(executable, requests):
    with requests.open() as source:
        selected = {}
        for line in source:
            request = json.loads(line)
            family = request["label"].split("/")[0]
            if family in {"identity", "strict-choice"} and family not in selected:
                selected[family] = request
            if len(selected) == 2:
                break
    accepting = selected["identity"]["before"]
    rejecting = selected["strict-choice"]["before"]
    for before, after in [(accepting, rejecting), (rejecting, accepting)]:
        request = {
            "label": "negative-control",
            "before": before,
            "after": after,
            "inputs": selected["identity"]["inputs"][:1],
        }
        result = subprocess.run([executable], input=json.dumps(request) + "\n",
                                capture_output=True, text=True, cwd=ROOT)
        if result.returncode != 1 or "acceptance mismatch" not in result.stderr:
            raise ValueError("Reference checker failed to detect a deliberate acceptance flip")


def main():
    parser = argparse.ArgumentParser(description="Compare each MIR pass in plutus-core 1.65.0.0")
    parser.add_argument("--ghc", default=shutil.which("ghc"))
    arguments = parser.parse_args()
    if not arguments.ghc:
        parser.error("Supply --ghc from an environment containing plutus-core 1.65.0.0")
    ghc = Path(arguments.ghc).absolute()
    package_ids = []
    for name in ["plutus-core-1.65.0.0", "z-plutus-core-z-flat-1.65.0.0"]:
        package_id = subprocess.check_output(
            [ghc.with_name("ghc-pkg"), "field", name, "id", "--simple-output"], text=True
        ).strip()
        if not package_id or any(character.isspace() for character in package_id):
            raise ValueError(f"Expected exactly one installed package: {name}")
        package_ids.extend(["-package-id", package_id])
    directory = ROOT / ".lake" / "pass-audit"
    directory.mkdir(parents=True, exist_ok=True)
    executable = directory / "reference-pass-audit"
    subprocess.run(
        [ghc, "-O2", "-Wall", "-Werror", "-hide-all-packages",
         "-package", "base", "-package", "bytestring", "-package", "aeson", "-package", "text",
         *package_ids, "-outputdir", directory, "-o", executable,
         ROOT / "Test/MIR/ReferencePassAudit.hs"], check=True, cwd=ROOT,
    )
    subprocess.run(["lake", "build", "pass_audit"], check=True, cwd=ROOT)
    requests = directory / "requests.jsonl"
    with requests.open("w") as output:
        subprocess.run([ROOT / ".lake/build/bin/pass_audit", "--export"],
                       stdout=output, check=True, cwd=ROOT)
    check_negative_controls(executable, requests)
    with requests.open() as source, (directory / "diagnostics.log").open("w") as diagnostics:
        result = subprocess.check_output([executable], stdin=source, stderr=diagnostics,
                                         text=True, cwd=ROOT)
    report = {
        "packages": package_ids[1::2],
        "semantics": "E",
        "cpuLimit": 10000000000,
        "memoryLimit": 10000000,
        "requestSha256": hashlib.sha256(requests.read_bytes()).hexdigest(),
        "negativeControls": 2,
        "result": result.strip(),
    }
    (directory / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(result, end="")


if __name__ == "__main__":
    main()
