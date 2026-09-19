#!/usr/bin/env python3
"""Build every source module and enforce the repository's admission boundary."""

import json
from pathlib import Path
import shutil
import subprocess

from setup_mathlib import ROOT, configuration, verify_environment


def main():
    config, _, _, _ = configuration()
    verify_environment()
    source = ROOT / config.get("srcDir", ".")
    files = sorted(source.rglob("*.lean"))
    if not files:
        raise RuntimeError(f"No Lean sources found in {source}")
    modules = []
    for file in files:
        parts = file.relative_to(source).with_suffix("").parts
        if any("." in part or any(char.isspace() for char in part) for part in parts):
            raise RuntimeError(f"Unsupported Lean module path: {file}")
        if not file.resolve().is_relative_to(source.resolve()):
            raise RuntimeError(f"Source file points outside the source directory: {file}")
        modules.append(".".join(parts))
    lake = shutil.which("lake") or str(Path.home() / ".elan/bin/lake")
    print(f"Building all {len(files)} source modules", flush=True)
    # Explicit source targets include files that no other module imports and
    # fail if a source file has not been assigned to a Lake library.
    subprocess.run([lake, "build", *(str(file.relative_to(ROOT)) for file in files)], cwd=ROOT, check=True)
    # Check persisted compiler diagnostics as well as declaration bodies. This
    # includes warnings from anonymous examples and from cached compilations.
    artifact_root = ROOT / config.get("buildDir", ".lake/build") / config.get("leanLibDir", "lib/lean")
    for file, module in zip(files, modules):
        trace = artifact_root.joinpath(*module.split(".")).with_suffix(".trace")
        data = json.loads(trace.read_text())
        if file.relative_to(source).parts[0] == "External" and file.parent != source:
            continue
        for entry in data["log"]:
            if entry["level"] == "warning" and "declaration uses `sorry" in entry["message"]:
                raise RuntimeError(f"Admission outside src/External: {entry['message']}")
    subprocess.run(
        [lake, "env", "lean", "--run", str(ROOT / ".github/ci/CheckAdmissions.lean"), str(source), *modules],
        cwd=ROOT, check=True,
    )


if __name__ == "__main__":
    main()
