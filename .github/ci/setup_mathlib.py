#!/usr/bin/env python3
"""Prepare the pinned, shared mathlib installation used by the Lake configuration."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tomllib

ROOT = Path(__file__).resolve().parents[2]
REVISION_FILE = ROOT / ".github/ci/mathlib-revision"


def git(directory, *args):
    return subprocess.check_output(
        ["git", "-C", str(directory), *args], text=True
    ).strip()


def configuration():
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    dependency = next(item for item in config["require"] if item["name"] == "mathlib")
    locked = next(item for item in manifest["packages"] if item["name"] == "mathlib")
    directory = (ROOT / dependency["path"]).resolve()
    if locked["type"] != "path" or directory != (ROOT / locked["dir"]).resolve():
        raise RuntimeError("The mathlib paths in the Lake configuration and manifest disagree")
    if directory == ROOT or directory.is_relative_to(ROOT):
        raise RuntimeError("mathlib must remain in a shared installation outside this repository")
    revision = REVISION_FILE.read_text().strip()
    if not re.fullmatch(r"[0-9a-f]{40}", revision):
        raise RuntimeError("mathlib-revision must contain a full Git commit hash")
    return config, manifest, directory, revision


def verify_checkout(directory, revision):
    actual = git(directory, "rev-parse", "HEAD")
    if actual != revision:
        raise RuntimeError(f"{directory}: expected revision {revision}, found {actual}")
    if git(directory, "status", "--porcelain", "--untracked-files=no"):
        raise RuntimeError(f"{directory}: dependency has tracked local modifications")


def verify_environment():
    config, manifest, directory, revision = configuration()
    verify_checkout(directory, revision)
    if (directory / "lean-toolchain").read_text().strip() != (ROOT / "lean-toolchain").read_text().strip():
        raise RuntimeError("The project and pinned mathlib require different Lean toolchains")
    packages = (ROOT / config["packagesDir"]).resolve()
    if packages != (ROOT / manifest["packagesDir"]).resolve():
        raise RuntimeError("The package directories in the Lake configuration and manifest disagree")
    for dependency in manifest["packages"]:
        if dependency["type"] == "git":
            verify_checkout(packages / dependency["name"], dependency["rev"])
    print(f"Verified mathlib {revision} and all locked dependency revisions", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--paths", action="store_true", help="publish the dependency path for CI caching")
    parser.add_argument("--verify", action="store_true", help="check every installed dependency without modifying it")
    args = parser.parse_args()
    _, _, directory, revision = configuration()
    if args.paths:
        print(f"mathlib directory: {directory}")
        if output := os.environ.get("GITHUB_OUTPUT"):
            with open(output, "a") as stream:
                stream.write(f"mathlib-directory={directory}\n")
        return
    if args.verify:
        verify_environment()
        return
    if not directory.exists():
        directory.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(["git", "init", str(directory)], check=True)
        git(directory, "remote", "add", "origin", "https://github.com/leanprover-community/mathlib4.git")
        git(directory, "fetch", "--depth=1", "origin", revision)
        git(directory, "checkout", "--detach", "FETCH_HEAD")
    # Never reset an existing user installation to another revision.
    verify_checkout(directory, revision)
    if (directory / "lean-toolchain").read_text().strip() != (ROOT / "lean-toolchain").read_text().strip():
        raise RuntimeError("The project and pinned mathlib require different Lean toolchains")
    print(f"Prepared mathlib {revision} at {directory}")


if __name__ == "__main__":
    main()
