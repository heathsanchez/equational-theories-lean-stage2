#!/usr/bin/env python3
"""Make the integrated MathGraph solver independent of Python hash order.

The finite-model propagation queue was rescheduled by iterating the
`changed_cells` set directly.  Python deliberately randomizes set iteration
across process hash seeds, which made an otherwise identical proof search take
either seconds or exhaust its budget.  Canonical cell order preserves the same
sound propagation rules while making scheduling reproducible.
"""

import argparse
from pathlib import Path

NEEDLE = "for cell in self.changed_cells:"
REPLACEMENT = "for cell in sorted(self.changed_cells):"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("path")
    args = ap.parse_args()
    path = Path(args.path)
    text = path.read_text()
    count = text.count(NEEDLE)
    if count != 2:
        raise SystemExit(f"expected exactly 2 changed_cells traversals, found {count}")
    text = text.replace(NEEDLE, REPLACEMENT)
    compile(text, str(path), "exec")
    path.write_text(text)
    print(f"determinized {path}: {count} propagation traversals")


if __name__ == "__main__":
    main()
