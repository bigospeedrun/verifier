"""One-command reproduction of this audit package.

    python3 verify.py

Runs the bundled reduction check, verifies the package inventory against
MANIFEST.json, and asserts the audit's findings. Standard library only; no
network access; no third-party packages.
"""
import hashlib
import json
import subprocess
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parent
EVIDENCE = PKG / "evidence" / "reduction-check.json"


def fail(msg):
    print("FAIL: " + msg)
    print("SCOPE: nothing was verified")
    sys.exit(1)


def digest(path):
    """Hash with CRLF normalised to LF: this repository has no .gitattributes,
    so a clone with core.autocrlf=true rewrites line endings on checkout."""
    return hashlib.sha256(path.read_bytes().replace(b"\r\n", b"\n")).hexdigest()


def check_manifest():
    man = json.loads((PKG / "MANIFEST.json").read_text())
    if man.get("algorithm") != "sha256":
        fail("MANIFEST.json algorithm is not sha256")
    for rel, want in sorted(man["sha256"].items()):
        p = PKG / rel
        if not p.is_file():
            fail("missing package file: " + rel)
        got = digest(p)
        if got != want:
            fail("digest mismatch for %s (manifest %s, file %s)" % (rel, want, got))
    print("PASS: package inventory, %d files match MANIFEST.json" % len(man["sha256"]))


def run_check():
    if EVIDENCE.exists():
        EVIDENCE.unlink()
    proc = subprocess.run([sys.executable, "-I", "-B",
                           str(PKG / "code" / "reduction_check.py")],
                          capture_output=True, text=True)
    if proc.returncode != 0:
        fail("reduction_check.py exited %d\n%s" % (proc.returncode, proc.stderr[-2000:]))
    if not EVIDENCE.is_file():
        fail("reduction_check.py wrote no evidence file")
    return json.loads(EVIDENCE.read_text())


def expect(cond, msg):
    if not cond:
        fail(msg)
    print("PASS: " + msg)


def main():
    check_manifest()
    d = run_check()

    cx = d["input_complex"]
    expect(cx["points"] == 13 and cx["faces"] == 22 and cx["pairs"] == 33,
           "input complex: 13 points, 22 faces, 33 pairs")
    expect(cx["every_pair_in_exactly_two_faces"] and cx["distinct_faces"],
           "every point pair lies in exactly two faces; faces are distinct")
    expect(cx["euler_characteristic"] == 2,
           "closed surface: Euler characteristic 13 - 33 + 22 = 2")

    ta = d["type_algebra"]
    expect(ta["per_type_ok"],
           "type defect contributions (1,1,1)->0, (0,0,0)->0, local-only->1, (0,1,1)->2")
    expect(ta["d1_multisets_are_one_local_only_vector_plus_ordinary"],
           "defect 1 forces exactly one local-only vector (%d multisets enumerated)"
           % ta["d1_multisets_enumerated"])

    ic = d["identity_and_collapse"]
    expect(ic["identity_holds_on_all_profiles"],
           "lemma identity sum_i C(k_i,2) = sum_x sum_{l=1 endpoints} v'_i(x)")
    expect(ic["collapse_to_stated_form_holds"],
           "counted exponent collapses to the stated R (endpoint conventions enforced)")

    pi = d["pi_bound_and_halving"]
    expect(pi["pi_bound_holds"], "pi <= (v'_i + v'_j)/2 on %d exact rational trials" % pi["trials"])
    expect(pi["halving_step_holds"],
           "halving step: R <= -2m + (1/2)sum_all + (1/2)(v'_i+v'_j)_defect")

    ph = d["phi_concavity"]
    expect(ph["phi_peak_is_d(2d-1)"],
           "phi_i(x) = C(x,2) + (2d_i-x)x peaks at d_i(2d_i-1), attained at x in {2d_i-1, 2d_i}")

    g = d["allowed_graph"]
    expect(g["pairs"] == 28 and g["connected"], "allowed graph: 28 pairs, connected")
    expect(g["degrees"] == [3, 6, 3, 6, 4, 2, 4, 4, 4, 6, 4, 6, 4],
           "allowed degree sequence (3,6,3,6,4,2,4,4,4,6,4,6,4)")
    expect(g["sum_deg_sq"] == 262 and g["sum_deg_2deg_minus_1"] == 468,
           "sum d^2 = 262 and sum d(2d-1) = 468 = 2*262 - 2*28")
    expect(g["base_remainder"] == 178, "base remainder sum d^2 - 3m = 262 - 84 = 178")
    expect(g["pair_excess"] == 23, "pair excess max(2a+2b-1) = 23")
    expect(g["closed_form"] == 189, "closed form 262 - 84 + floor(23/2) = 189")

    fm = d["finite_maximum_crosscheck"]
    expect(fm["supports_with_pairs"] == 5468 and fm["relaxed_defect_one_strata"] == 55173,
           "cross-check: 5,468 supports without isolates, 55,173 relaxed defect-one strata")
    expect(fm["maximum"] == 189 and fm["agrees_with_closed_form"],
           "cross-check: finite maximum 189 equals the closed form")
    expect(fm["maximizer_count"] == 7, "cross-check: 7 maximizers (full support, spans 49-55)")

    r = d["defect_two_ratio"]
    expect(r["max_ratio"] == "122" and r["below_189"],
           "defect >= 2 ratio bound 122 (at d=2, n2=1, k=55), below defect one")

    c = d["negative_controls"]
    expect(c["flipped_cut_bit_changes_allowed_graph"] and c["flipped_cut_bit_changes_maximum"],
           "negative control: a flipped cut bit changes the allowed graph and the maximum (%d)"
           % c["flipped_maximum"])
    expect(c["unhalved_defect_term_would_give"] == 201 and c["unhalved_differs_from_claim"],
           "negative control: keeping the defect term unhalved gives 201, not 189")
    expect(c["duplicate_face_rejected"], "negative control: a duplicated face is rejected")
    expect(c["monotone_in_k"], "negative control: the ratio is monotone in k, so k = 2m-1 is worst")

    cm = d["claim_match"]
    expect(all(v["match"] for v in cm.values()),
           "claim match on C=189, ratio 122, 28 pairs, base 178, excess 23")

    print("")
    print("RESULT: the reduction behind C <= 189 is CONFIRMED as written.")
    print("SCOPE: the written reduction only. The finite maximum was audited at")
    print("       2026-10-23-ptweezy-sidorenko-c189 and is cross-checked here; the")
    print("       source containment probabilities, symplectic realizability of the")
    print("       type model, the orbit-counting transfer and the counterexample")
    print("       theorem remain outside. No Lean proof; the row stays Claimed.")


if __name__ == "__main__":
    main()
