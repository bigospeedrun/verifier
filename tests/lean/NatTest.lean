/- Self-test of the patched lean4export (patches/lean4export-*.patch). setup() builds it inside the exporter
checkout and runs it after build-comparator; a failure stops the run before any submission code.
`Export.Parse.parseDecNat?` (lean4export PR #60) must equal `String.toNat?`, and `natToDecStr` (PR #52) must
equal `toString`, on edge cases, values next to powers of ten and random digit strings. Then one
1.9 M-digit value (the size of the #187 literals) goes through the new print and parse, each in at most 60 s. -/
import Export
import Export.Parse

def check (label : String) (ok : Bool) : IO Unit := do
  unless ok do throw <| IO.userError s!"NATTEST FAIL {label}"

def parseSame (s : String) : Bool :=
  Export.Parse.parseDecNat? s == s.toNat?

def lcg (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def unitTests : IO Unit := do
  let edge := ["", "0", "00", "000", "007", "1", "9", "10", "_", "1_000", "_1", "1__0", "1_",
    "12a", "-1", " 5", "5 ", "0xff", "+1", "١٢"]
  for s in edge do check s!"edge {s}" (parseSame s)
  let mut pows := 0
  for k in [0:400] do
    let p := 10 ^ k
    for v in [p - 1, p, p + 1] do
      let s := toString v
      check s!"pow parse k={k}" (parseSame s && parseSame ("000" ++ s))
      check s!"pow print k={k}" (natToDecStr v == s)
      pows := pows + 1
  let mut x : Nat := 88172645463325252
  for i in [0:3000] do
    x := lcg x
    let len := x % 4000 + 1
    let mut s := ""
    let mut y := x
    for _ in [0:len] do
      y := lcg y
      s := s.push (Char.ofNat (48 + (y >>> 33) % 10))
    check s!"random parse {i} len={len}" (parseSame s)
    match s.toNat? with
    | some v => check s!"random print {i}" (natToDecStr v == toString v)
    | none => check s!"random isNat {i}" false
  IO.println s!"NATTEST unit ok edge={edge.length} pow={pows} random=3000"

def bigTest : IO Unit := do
  let n ← IO.lazyPure fun _ => 7 ^ 2241000 + 12345
  let t1 ← IO.monoMsNow
  let s ← IO.lazyPure fun _ => natToDecStr n
  check "big print length" (s.length > 1890000)
  let t2 ← IO.monoMsNow
  let p ← IO.lazyPure fun _ => Export.Parse.parseDecNat? s
  check "big parse" (p == some n)
  let t3 ← IO.monoMsNow
  check s!"big print {t2 - t1} ms" (t2 - t1 ≤ 60000)
  check s!"big parse {t3 - t2} ms" (t3 - t2 ≤ 60000)
  IO.println s!"NATTEST big digits={s.length} print_ms={t2 - t1} parse_ms={t3 - t2}"

def main : IO UInt32 := do
  try
    unitTests
    bigTest
    return 0
  catch e =>
    IO.eprintln e
    return 1
