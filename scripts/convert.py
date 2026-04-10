#!/usr/bin/env python3
"""
Literate Lean → Markdown converter.
Processes files containing /-! @@@ ... @@@ -/ comment blocks:
  - Text between @@@ markers is emitted as-is (markdown)
  - Lean code outside the markers is wrapped in ```lean ... ``` blocks
  - A boxed "Report an issue" link is appended at the end of each
    lowest-level subsection (detected by markdown headings).
"""

import re
import sys
from pathlib import Path

SEPARATOR = "@@@"
CODE_START = "```lean"
CODE_END = "```"

ISSUE_URL = "https://github.com/kevinsullivan/Lean4CS1/issues/new"
ISSUE_BOX = (
    '<div style="background: #f0f4f8; border: 1px solid #d0d7de; '
    'border-radius: 6px; padding: 8px 12px; margin-top: 16px; '
    'font-size: 0.9em;">'
    f'📝 <a href="{ISSUE_URL}">Report an issue</a> with this section'
    '</div>\n'
)

HEADING_RE = re.compile(r'^(#{1,6})\s')


def convert(lines):
    LIT, CODE = "lit", "code"
    mode = CODE
    segments = []  # list of (mode, [lines])
    current = []

    for line in lines:
        if SEPARATOR in line:
            if current:
                segments.append((mode, current))
                current = []
            mode = LIT if mode == CODE else CODE
        else:
            current.append(line)

    if current:
        segments.append((mode, current))

    out = []
    for mode, seg_lines in segments:
        if mode == LIT:
            out.extend(seg_lines)
        else:
            # strip leading/trailing blank lines, wrap in fences
            stripped = seg_lines
            while stripped and not stripped[0].strip():
                stripped = stripped[1:]
            while stripped and not stripped[-1].strip():
                stripped = stripped[:-1]
            if stripped:
                out.append(CODE_START)
                out.extend(stripped)
                out.append(CODE_END)
                out.append("")

    return inject_issue_links(out)


def inject_issue_links(lines):
    """Insert a boxed issue link before each heading and at the end."""
    # Find indices of all heading lines
    heading_indices = [
        i for i, line in enumerate(lines) if HEADING_RE.match(line)
    ]

    if not heading_indices:
        # No headings — just append at the end
        result = lines + ["", ISSUE_BOX]
        return "\n".join(result) + "\n"

    # Find the deepest (most #'s) heading level used
    max_depth = max(
        len(HEADING_RE.match(lines[i]).group(1))
        for i in heading_indices
    )

    # Collect indices of deepest-level headings
    deepest = [
        i for i in heading_indices
        if len(HEADING_RE.match(lines[i]).group(1)) == max_depth
    ]

    # Insert issue box before each deepest heading (except the first)
    # and after the last line of the document
    result = []
    insert_before = set(deepest[1:])  # skip first deepest heading
    for i, line in enumerate(lines):
        if i in insert_before:
            result.append("")
            result.append(ISSUE_BOX)
            result.append("")
        result.append(line)

    # Always append at the very end
    result.append("")
    result.append(ISSUE_BOX)

    return "\n".join(result) + "\n"


def main():
    args = sys.argv[1:]
    if len(args) == 1:
        input_file = args[0]
        output_file = str(Path(input_file).with_suffix(".md"))
    elif len(args) == 2:
        input_file, output_file = args
    else:
        print("Usage: convert.py <input.lean> [output.md]", file=sys.stderr)
        sys.exit(1)

    with open(input_file, encoding="utf-8") as f:
        lines = f.read().splitlines()

    result = convert(lines)

    with open(output_file, "w", encoding="utf-8") as f:
        f.write(result)

    print(f"Formatted content written to {output_file}")


if __name__ == "__main__":
    main()
