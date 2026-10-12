from __future__ import annotations

import os
import re
import stat
import sys
from pathlib import Path

from beejsp import assessment, dashboard

_KEY = re.compile(r"^\s*(?:export\s+)?GITHUB_TOKEN\s*(?:=|$)")
_SETTING = re.compile(
    r"\s*(?:export\s+)?GITHUB_TOKEN\s*=\s*"
    r"(?:\"([^\"\r\n]*)\"|'([^'\r\n]*)'|([^#\r\n]*?))\s*(?:#.*)?\Z"
)


def _read_file(fd: int) -> bytes:
    info = os.fstat(fd)
    if not stat.S_ISREG(info.st_mode) or info.st_nlink != 1:
        raise ValueError("configuration must be a regular file without links")
    if info.st_size > 65_536:
        raise ValueError("configuration exceeds size limit")
    data = os.read(fd, 65_537)
    if len(data) > 65_536:
        raise ValueError("configuration exceeds size limit")
    return data


def initialize_env(root: Path) -> str:
    nofollow = getattr(os, "O_NOFOLLOW", 0)
    template_path = root / ".env.example"
    env_path = root / ".env"
    if template_path.is_symlink() or env_path.is_symlink():
        raise ValueError("configuration symlinks are not allowed")
    template_fd = os.open(template_path, os.O_RDONLY | nofollow)
    try:
        template = _read_file(template_fd)
    finally:
        os.close(template_fd)
    if not any(_KEY.match(line) for line in template.decode("utf-8").splitlines()):
        raise ValueError("configuration template lacks GITHUB_TOKEN")
    try:
        fd = os.open(env_path, os.O_RDWR | os.O_CREAT | os.O_EXCL | nofollow, 0o600)
    except FileExistsError:
        fd = os.open(env_path, os.O_RDWR | nofollow)
        created = False
    else:
        created = True
    try:
        data = _read_file(fd)
        if os.name == "posix":
            os.fchmod(fd, 0o600)
        if created:
            data = template
            os.write(fd, data)
        elif not any(_KEY.match(line) for line in data.decode("utf-8").splitlines()):
            addition = (
                b"\n" if data and not data.endswith(b"\n") else b""
            ) + b"GITHUB_TOKEN=\n"
            os.lseek(fd, 0, os.SEEK_END)
            os.write(fd, addition)
            data += addition
        os.fsync(fd)
        return data.decode("utf-8")
    finally:
        os.close(fd)


def configured_token(content: str) -> str | None:
    process = os.environ.get("GITHUB_TOKEN")
    if process:
        return assessment.validate_github_token(process)
    values = []
    for line in content.splitlines():
        if not _KEY.match(line):
            continue
        match = _SETTING.fullmatch(line)
        if match is None:
            raise ValueError("invalid GITHUB_TOKEN configuration syntax")
        values.append(next(value for value in match.groups() if value is not None))
    if len(values) != 1:
        raise ValueError("GITHUB_TOKEN must be configured exactly once")
    return assessment.validate_github_token(values[0])


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    try:
        token = configured_token(initialize_env(root))
        if token:
            os.environ["GITHUB_TOKEN"] = token
        else:
            os.environ.pop("GITHUB_TOKEN", None)
        return dashboard.main(["--root", str(root), *sys.argv[1:]])
    except (OSError, ValueError):
        print(
            "Startup failed: check .env permissions, supported syntax and GITHUB_TOKEN format. Configuration contents are never logged.",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
