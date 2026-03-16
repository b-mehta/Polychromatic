#!/usr/bin/env python3
"""Compare Aristotle proof results against original proofs in Combi.lean.

Overview
--------
Aristotle (https://aristotle.harmonic.fun) is an automated theorem prover.
We submit lemmas from Combi.lean (via golf_batch.py) and Aristotle returns
result files with alternative proofs. This script compares those results
against the originals to identify which Aristotle proofs are shorter.

Each result file (result_*.lean) has the structure:
  1. Import stubs (Mathlib imports + stub definitions with `admit`)
  2. Section/variable declarations matching Combi.lean's structure
  3. Dependencies of the target lemma, proved with `admit`
  4. Optionally, NEW helper lemmas Aristotle introduced
  5. The target lemma with Aristotle's proof

Line counting
-------------
For each result, we compute:
  - **Body lines**: lines after `:= by` for the target lemma only (the
    declaration signature is identical in both versions, so not counted)
  - **Helper lines**: signature + body lines for any NEW helper lemmas
    that Aristotle introduced and that don't already exist in Combi.lean.
    These represent genuinely new code that would need to be added.
  - **Total** = Body + Helper, compared against the original body line count.

Stubs (proofs that are just `admit`/`sorry`) and lemmas that already exist
in Combi.lean are excluded from the helper count. The "end Stubs" marker
in each result file separates the boilerplate from the real content.

When multiple result files exist for the same lemma (e.g. result_foo.lean
and result_new_foo.lean), the script picks the best non-sorry result.

Usage
-----
  python3 compare.py                    # Full comparison, sorted by delta
  python3 compare.py --only better      # Only show improvements
  python3 compare.py --sort name        # Sort alphabetically
  python3 compare.py --sort status      # Group by status

Output columns: Lemma, Orig (original body lines), Body (Aristotle target
body), Help (new helper lines), Total (Body+Help), Delta (Total-Orig),
Status (BETTER/SAME/WORSE/SORRY/N/A), New helpers (names).
"""

import argparse
import os
import re

RESULTS_DIR = os.path.dirname(os.path.abspath(__file__))
COMBI_PATH = os.path.join(RESULTS_DIR, "..", "Combi.lean")

# Skip these result files (duplicates / old versions)
SKIP_FILES = {
    "result_case_one_interval_v2.lean",
    "result_case_one_interval_v3.lean",
    "result_case_one_res_3g_add_1_v2.lean",
    "result_case_one_res_3g_add_4_v2.lean",
    "result_old_batch_9.lean",
}


def parse_combi(path):
    """Return two things:
    1. dict: lemma_name -> proof body line count
    2. set: all declaration names in Combi.lean
    """
    with open(path) as f:
        lines = f.read().splitlines()

    bodies = {}
    names = set()
    in_comment = False

    for i, line in enumerate(lines):
        # Track block comments (skip Aristotle alternatives)
        if "/-" in line and not in_comment:
            in_comment = True
        if "-/" in line and in_comment:
            in_comment = False
            continue
        if in_comment:
            continue

        m = re.match(
            r"^(?:private\s+)?(?:noncomputable\s+)?(?:lemma|theorem|def)\s+(\S+)",
            line,
        )
        if m:
            name = m.group(1)
            names.add(name)

            # Find := by within next 15 lines
            for j in range(i, min(i + 15, len(lines))):
                if ":= by" in lines[j]:
                    after = lines[j][lines[j].index(":= by") + 5 :].strip()
                    body = 0
                    if after and after not in ("admit", "sorry"):
                        body = 1
                    for k in range(j + 1, len(lines)):
                        l = lines[k]
                        if l.strip() == "":
                            break
                        if re.match(
                            r"^(?:private\s+)?(?:noncomputable\s+)?"
                            r"(?:lemma|theorem|def|end |section |namespace |"
                            r"open |set_option|@\[|#|/-)",
                            l,
                        ):
                            break
                        body += 1
                    bodies[name] = body
                    break
                if ":= sorry" in lines[j]:
                    bodies[name] = 1
                    break

    return bodies, names


def parse_aristotle(filepath, combi_names):
    """Parse an Aristotle result file.

    Returns (target_name, target_body, helper_lines, has_sorry, helper_names)
    where:
    - target_body = body lines only (after := by) for the target lemma
    - helper_lines = sig + body for NEW helpers not in Combi.lean
    - has_sorry = True if target proof contains sorry/admit
    - helper_names = list of new helper names
    """
    with open(filepath) as f:
        lines = f.read().splitlines()

    # Find end of Stubs section
    stubs_end = 0
    for i, line in enumerate(lines):
        if line.strip() == "end Stubs":
            stubs_end = i
            break

    decls = []  # (name, sig_lines, body_lines, is_stub, has_sorry)
    i = stubs_end
    n = len(lines)
    in_comment = False

    while i < n:
        stripped = lines[i].strip()
        if "/-" in stripped and not in_comment:
            in_comment = True
        if "-/" in stripped and in_comment:
            in_comment = False
            i += 1
            continue
        if in_comment:
            i += 1
            continue

        m = re.match(
            r"^(?:private\s+)?(?:noncomputable\s+)?"
            r"(?:lemma|theorem|def)\s+(\S+)",
            stripped,
        )
        if m:
            name = m.group(1)
            sig_start = i
            for j in range(i, min(i + 20, n)):
                if ":= by" in lines[j]:
                    after = lines[j][lines[j].index(":= by") + 5 :].strip()
                    is_stub = after in ("admit", "sorry")
                    body = 0
                    has_sorry = False

                    if not is_stub and after:
                        body = 1

                    if not is_stub:
                        for k in range(j + 1, n):
                            bl = lines[k]
                            if bl.strip() == "":
                                break
                            if re.match(
                                r"^(?:private\s+)?(?:noncomputable\s+)?"
                                r"(?:lemma|theorem|def|end |section |"
                                r"namespace |open |set_option|@\[|#|/-|macro )",
                                bl,
                            ):
                                break
                            if bl.strip() in ("admit", "sorry") and body == 0:
                                is_stub = True
                                break
                            body += 1
                            if "sorry" in bl:
                                has_sorry = True

                    sig_count = j - sig_start  # lines before := by
                    decls.append((name, sig_count, body, is_stub, has_sorry))
                    break
                elif ":=" in lines[j]:
                    # Direct definition (not := by)
                    is_stub = "sorry" in lines[j] or "admit" in lines[j]
                    body = 1  # the := line
                    for k in range(j + 1, n):
                        bl = lines[k]
                        if bl.strip() == "":
                            break
                        if re.match(
                            r"^(?:private\s+)?(?:noncomputable\s+)?"
                            r"(?:lemma|theorem|def|end |section |"
                            r"namespace |open |set_option|@\[|#|/-|macro )",
                            bl,
                        ):
                            break
                        body += 1
                    sig_count = j - sig_start
                    decls.append((name, sig_count, body, is_stub, False))
                    break

        # Catch macro lines as helpers
        if stripped.startswith("macro "):
            decls.append(("_macro_", 0, 1, False, False))

        i += 1

    if not decls:
        return None, 0, 0, True, []

    # Target = last non-stub declaration
    target = None
    target_idx = None
    for idx in range(len(decls) - 1, -1, -1):
        if not decls[idx][3]:
            target = decls[idx]
            target_idx = idx
            break

    if target is None:
        return decls[-1][0] if decls else None, 0, 0, True, []

    # NEW helpers = non-stub, not target, name not in Combi.lean
    helper_lines = 0
    helper_names = []
    for idx, (name, sig, body, stub, _) in enumerate(decls):
        if stub or idx == target_idx:
            continue
        clean = name.replace("Finset.", "")
        if clean not in combi_names and name not in combi_names:
            helper_lines += sig + body
            helper_names.append(clean)

    return target[0], target[2], helper_lines, target[4], helper_names


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--sort",
        choices=["delta", "name", "status"],
        default="delta",
        help="Sort order (default: delta)",
    )
    parser.add_argument(
        "--only",
        choices=["better", "worse", "same", "sorry"],
        help="Only show results with this status",
    )
    args = parser.parse_args()

    combi_bodies, combi_names = parse_combi(COMBI_PATH)

    # Process all result files, deduplicate by target name
    all_results = {}  # key -> (target_body, helper_lines, sorry, fname, helper_names)

    for f in sorted(os.listdir(RESULTS_DIR)):
        if not f.startswith("result_") or not f.endswith(".lean") or f in SKIP_FILES:
            continue
        path = os.path.join(RESULTS_DIR, f)
        name, tbody, hlines, sorry, hnames = parse_aristotle(path, combi_names)
        if name is None:
            continue
        name = name.replace("Finset.", "")
        total = tbody + hlines

        key = name
        if key not in all_results:
            all_results[key] = (tbody, hlines, sorry, f, hnames)
        elif sorry and not all_results[key][2]:
            pass  # keep non-sorry
        elif not sorry and all_results[key][2]:
            all_results[key] = (tbody, hlines, sorry, f, hnames)
        elif not sorry and total < (all_results[key][0] + all_results[key][1]):
            all_results[key] = (tbody, hlines, sorry, f, hnames)

    # Build rows
    rows = []
    for name in sorted(all_results):
        tbody, hlines, sorry, fname, hnames = all_results[name]
        orig = combi_bodies.get(name)
        total = tbody + hlines

        if sorry:
            status = "SORRY"
            delta = None
        elif orig is None:
            status = "N/A"
            delta = None
        else:
            delta = total - orig
            status = "BETTER" if delta < 0 else ("WORSE" if delta > 0 else "SAME")

        rows.append((name, orig, tbody, hlines, total, delta, status, fname, hnames))

    # Filter
    if args.only:
        rows = [r for r in rows if r[6].lower() == args.only]

    # Sort
    status_order = {"BETTER": 0, "SAME": 1, "WORSE": 2, "SORRY": 3, "N/A": 4}
    if args.sort == "delta":
        rows.sort(
            key=lambda r: (status_order[r[6]], r[5] if r[5] is not None else 999)
        )
    elif args.sort == "name":
        rows.sort(key=lambda r: r[0])
    elif args.sort == "status":
        rows.sort(key=lambda r: (status_order[r[6]], r[0]))

    # Print
    print(
        f"{'Lemma':<38} {'Orig':>4} {'Body':>4} {'Help':>5} "
        f"{'Total':>5} {'Delta':>6} {'Status':<7} {'New helpers'}"
    )
    print("-" * 120)

    counts = {}
    for name, orig, tbody, hlines, total, delta, status, fname, hnames in rows:
        orig_s = str(orig) if orig is not None else "?"
        delta_s = f"{delta:+d}" if delta is not None else "N/A"
        help_s = f"+{hlines}" if hlines > 0 else ""
        print(
            f"{name:<38} {orig_s:>4} {tbody:>4} {help_s:>5} "
            f"{total:>5} {delta_s:>6} {status:<7} {', '.join(hnames)}"
        )
        counts[status] = counts.get(status, 0) + 1

    total_delta = sum(r[5] for r in rows if r[5] is not None)
    print(
        f"\nBETTER: {counts.get('BETTER', 0)}  "
        f"SAME: {counts.get('SAME', 0)}  "
        f"WORSE: {counts.get('WORSE', 0)}  "
        f"SORRY: {counts.get('SORRY', 0)}  "
        f"N/A: {counts.get('N/A', 0)}"
    )
    print(f"Net delta: {total_delta:+d} lines")


if __name__ == "__main__":
    main()
