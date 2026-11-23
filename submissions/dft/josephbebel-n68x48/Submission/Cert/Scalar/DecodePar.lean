import Submission.Cert.Scalar.Decode

/-! Parallel event decode for the packed-row checker (written for this submission).  Untrusted meta code only: every
definition it adds is plain data (event lists, checkpoint tries, label states) that the kernel re-checks
through PR 209's checkers.

* `decode_slice i0 n "s" …` decodes one slice of the event stream with a fresh rANS model (the encoder
  resets its model at every slice start), defines one list constant per
  string and the scalar segments `seg{i0}` … `seg{i0+n-1}` (consecutive strings, balanced by event count).
  Slices are independent modules and build in parallel.
* `def_events evs N` defines `evs := seg0 ++ (seg1 ++ … seg{N-1})`.
* `gen_ck_z S from nr d nk v N lo hi` generates the checkpoints of one key chain (ScalarCheck.CheckpointGen's
  algorithm with the zero-source skip), reading the events back from the imported `seg` constants; the rows
  are the identity rows of `decode_id_rows _ d nk v`.  Checkpoint `S{i}` is the state before segment `seg{i}`.
* `gen_label_par …` is WarpCheck.LabelGen.elabLabStates with label segments made of whole scalar segments,
  reading events, the start states and the frame table from the environment.
Written for this submission (Claude, Anthropic) on top of PR 209's Decode.lean (HalitZiyaKARTAL v7-42). -/

namespace ScalarCheck.DecodePar
open Lean Elab Command
open ScalarCheck.Decode

/-- Event list constant names of segment `i`, in order. -/
def segName (ns : Name) (i : Nat) : Name := ns ++ Name.mkSimple s!"seg{i}"

/-- `decode_slice i0 [c1, …, ck] "s1" …`: decode the strings with a fresh model; segment `i0 + j` is
one flat list of the events of strings `c_j ≤ s < c_{j+1}` (`c_0 = 0`, last segment up to the end). -/
syntax (name := decSlice) "decode_slice " num " [" num,* "]" (ppSpace str)+ : command
@[command_elab decSlice] def elabDecSlice : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let i0 := nat! stx[1]
  let cuts : Array Nat := #[0] ++ stx[3].getSepArgs.map nat!
  let strs := stx[5].getArgs
  let mut st : St := { n := 0 }
  let mut cur : Array Expr := #[]
  let mut j := 0
  for si in [0:strs.size] do
    if j + 1 < cuts.size && si == cuts[j + 1]! then
      if cur.size == 0 then throwError "decode_slice: empty segment"
      addDef (segName ns (i0 + j)) (listT evT) (mkList evT cur)
      cur := #[]; j := j + 1
    let (evs, st') ← runDecoder strs[si]! (do
      let mut out : Array Expr := #[]
      for _ in [0:← uni 65536] do out := out.push (← event).1
      return out) st
    st := st'
    cur := cur ++ evs
  unless j + 1 == cuts.size do throwError "decode_slice: cut past the last string"
  if cur.size == 0 then throwError "decode_slice: empty segment"
  addDef (segName ns (i0 + j)) (listT evT) (mkList evT cur)

syntax (name := defEvs) "def_events " ident num : command
@[command_elab defEvs] def elabDefEvs : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  addCat (ns ++ stx[1].getId) evT ((Array.range (nat! stx[2])).map (segName ns))

/-! Reading events back from the environment. -/

partial def listElems (e : Expr) (acc : Array Expr) : Option (Array Expr) :=
  if e.isAppOfArity ``List.cons 3 then listElems e.appArg! (acc.push e.appFn!.appArg!)
  else if e.isAppOfArity ``List.nil 1 then some acc
  else none

def natOf (e : Expr) : Option Nat := match e with | .lit (.natVal n) => some n | _ => none

def coOf (e : Expr) : Option (Bool × Nat × Nat) := do
  guard (e.isAppOfArity ``CertData.Co.mk 3)
  let args := e.getAppArgs
  let sg := args[0]!.isConstOf ``Bool.true
  return (sg, ← natOf args[1]!, ← natOf args[2]!)

/-- The `MEv` of a decoded event expression (inverse of `ScalarCheck.Decode.event`). -/
def mevOf (e : Expr) : Option MEv := do
  if e.isAppOfArity ``WarpCheck.WEv.g 1 then
    let g := e.appArg!
    guard (g.isAppOfArity ``CertData.Gate.out 4)
    let a := g.getAppArgs
    let f ← natOf a[0]!; let s ← natOf a[1]!
    let ps ← listElems a[2]! #[]
    if ps.size == 0 then return { kind := 0, f := f, regs := #[s] }
    let p := ps[0]!
    guard (p.isAppOfArity ``Prod.mk 4)
    let tg ← natOf p.getAppArgs[2]!
    let co ← coOf p.getAppArgs[3]!
    return { kind := 0, f := f, regs := #[s, tg], co := co }
  else if e.isAppOfArity ``WarpCheck.WEv.sc 3 then
    let a := e.getAppArgs
    return { kind := 1, f := ← natOf a[0]!, regs := #[← natOf a[1]!], co := ← coOf a[2]! }
  else if e.isAppOfArity ``WarpCheck.WEv.zf 1 then
    return { kind := 3, f := 0, regs := #[← natOf e.appArg!] }
  else if e.isAppOfArity ``WarpCheck.WEv.za 2 then
    let a := e.getAppArgs
    return { kind := 2, f := ← natOf a[1]!, regs := #[← natOf a[0]!] }
  else if e.isAppOfArity ``WarpCheck.WEv.dn 2 then
    let a := e.getAppArgs
    return { kind := 4, f := ← natOf a[1]!, regs := #[← natOf a[0]!] }
  else none

def constVal (env : Environment) (n : Name) : CommandElabM Expr := do
  let some (.defnInfo d) := env.find? n | throwError "decode_par: {n} is not a definition"
  return d.value

/-- Constants of a right-nested `++` concatenation (as built by `addCat`), in order. -/
partial def catConsts (e : Expr) (acc : Array Name) : Option (Array Name) :=
  if e.isAppOfArity ``HAppend.hAppend 6 then
    match e.appFn!.appArg! with
    | .const n _ => catConsts e.appArg! (acc.push n)
    | _ => none
  else match e with
    | .const n _ => some (acc.push n)
    | _ => none

def segEvents (env : Environment) (seg : Name) : CommandElabM (Array MEv) := do
  let v ← constVal env seg
  if let some es := listElems v #[] then
    let mut out : Array MEv := #[]
    for e in es do
      let some m := mevOf e | throwError "decode_par: unexpected event in {seg}"
      out := out.push m
    return out
  let some names := catConsts v #[] | throwError "decode_par: {seg} is not a concatenation"
  let mut out : Array MEv := #[]
  for n in names do
    let some es := listElems (← constVal env n) #[] | throwError "decode_par: {n} is not a list literal"
    for e in es do
      let some m := mevOf e | throwError "decode_par: unexpected event in {n}"
      out := out.push m
  return out

end ScalarCheck.DecodePar

namespace ScalarCheck.CheckpointGenPar
open Lean Elab Command
open ScalarCheck.Decode ScalarCheck.CheckpointGen ScalarCheck.DecodePar

/-- Checkpoint leaf: `CheckpointGen.leafE` (sparse digit tree) for rows with few nonzero digits, otherwise one
literal `OFF + (v - OFF)` or `OFF - (OFF - v)` (two kernel operations to evaluate instead of one per digit). -/
partial def countNZ (offs : Array Nat) (lim v cnt : Nat) : Nat :=
  if v == offs[cnt]! then 0
  else if cnt ≤ 1 then 1
  else
    let h := cnt / 2
    let a := countNZ offs lim (v % 2 ^ (wb * h)) h
    if a > lim then a else a + countNZ offs lim (v >>> (wb * h)) (cnt - h)

def leafH (offs : Array Nat) (v : Nat) : Expr := Id.run do
  if countNZ offs 16 v nD ≤ 16 then return leafE offs v
  let off := mkApp (mkConst ``ScalarCheck.Cx.OFF) (mkConst ``ScalarCheck.params)
  if v ≥ OFF then return mkApp (mkConst ``ScalarCheck.PT.leaf) (natC ``Nat.add off (mkRawNatLit (v - OFF)))
  return mkApp (mkConst ``ScalarCheck.PT.leaf) (natC ``Nat.sub off (mkRawNatLit (OFF - v)))

syntax (name := genCkZ) "gen_ck_z " ident " from " num ppSpace num ppSpace num ppSpace num ppSpace num ppSpace num ppSpace num : command
@[command_elab genCkZ] def elabGenCkZ : CommandElab := fun stx => do
  unless X == 2 ^ wb do throwError "gen_ck_z: digit width changed"
  let nr := nat! stx[3]; let d := nat! stx[4]; let nk := nat! stx[5]; let v := nat! stx[6]
  let C := nat! stx[7]; let lo := nat! stx[8]; let hi := nat! stx[9]
  let env ← getEnv
  let ns ← getCurrNamespace
  let mut R : Array Nat := #[]
  for r in [0:2 ^ d] do
    let row : Array (Nat × Int) := if r < nk then #[(r, (v : Int))] else #[]
    R := R.push (← ofM <| packStart r (sliceRow lo hi row))
  let offs := offTable
  let add (name : Name) (ty val : Expr) : CommandElabM Unit := do
    liftCoreM <| addDecl (.defnDecl (mkDefinitionValEx name [] ty val (.regular 0) .safe [name]))
    modifyEnv (addNoncomputable · name)
  let S := stx[1].getId
  let ptT := mkConst ``ScalarCheck.PT
  let node (a b : Expr) : Expr := mkApp2 (mkConst ``ScalarCheck.PT.node) a b
  -- T[h][key]: subtree of height h over the keys ≡ key (mod 2^(d-h)) (the layout of `mkPT`); unchanged
  -- subtrees are shared between checkpoints.
  let mut T : Array (Array Expr) := #[]
  T := T.push (Array.range (2 ^ d) |>.map fun r => mkConst (ns ++ S.appendAfter s!"0_{r}"))
  for r in [0:2 ^ d] do
    add (ns ++ S.appendAfter s!"0_{r}") ptT (leafH offs R[r]!)
  for h in [1:d + 1] do
    let b := 2 ^ (d - h)
    T := T.push ((Array.range b).map fun key => node T[h - 1]![key]! T[h - 1]![key + b]!)
  add (ns ++ S.appendAfter "0") ptT T[d]![0]!
  for i in [0:C] do
    let evs ← segEvents env (segName ns i)
    let R0 := R
    R ← ofM <| evs.foldlM (fun R e => step nr R e true) R
    for r in [0:2 ^ d] do
      if R[r]! != R0[r]! then
        let nm := ns ++ S.appendAfter s!"{i + 1}_{r}"
        add nm ptT (leafH offs R[r]!)
        T := T.modify 0 (·.set! r (mkConst nm))
        for h in [1:d + 1] do
          let b := 2 ^ (d - h)
          let key := r % b
          let e := node T[h - 1]![key]! T[h - 1]![key + b]!
          T := T.modify h (·.set! key e)
    add (ns ++ S.appendAfter (toString (i + 1))) ptT T[d]![0]!

/-! ### Checkpoints generated in parallel parts

`gen_ck_part S q dlo dhi from nr d nk v C` runs the scalar replay on the packed digits `dlo ≤ j < dhi` only (part `q`;
digit 0 is the ghost).  The real digits of every add are exact (Gate 2), so the floor division only touches the
ghost and the parts compose exactly.  For every segment it records the registers whose digits changed
(`{S}c{q}_{i} : List Nat`) and their digits as `OFF_q + P - N` (`{S}p{q}_{i}_{r}`, `{S}n{q}_{i}_{r}`, omitted when 0).
`gen_ck_join S Q from d C dlo_0 … dlo_{Q-1}` builds the checkpoint leaves `OFF + Σ P_q·X^dlo_q - Σ N_q·X^dlo_q` and the
tries `S{i}` from the parts.  All of this is untrusted data: the kernel checks it through `checkEnd` and the
segment runs. -/

def partVal (v dlo nq : Nat) : Nat := (v >>> (wb * dlo)) % 2 ^ (wb * nq)

def linP (offq : Nat) (a b : Nat) (co : Bool × Nat × Nat) : M Nat := do
  let (neg, num, den) := co
  if den == 0 then throw "zero denominator"
  let (s, m) := if neg then (den * a + num * offq, num * b) else (den * a + num * b, num * offq)
  if s < m then throw "negative row"
  return (s - m) / den

def stepP (offq nr : Nat) (R : Array Nat) (e : MEv) : M (Array Nat) := do
  let r := e.regs.getD 0 0
  if e.kind == 0 then
    if e.regs.size < 2 then return R
    let t := e.regs.getD 1 0
    if t ≥ nr || r ≥ nr || t == r then throw "add: bad registers"
    return R.set! t (← linP offq R[t]! R[r]! e.co)
  else if e.kind == 1 then
    if r ≥ nr then throw "scale: bad register"
    return R.set! r (← linP offq offq R[r]! e.co)
  else if e.kind == 2 || e.kind == 3 then
    if r ≥ nr then throw "zero buffer: bad register"
    return R.set! r offq
  else if e.kind == 4 then return R
  else throw s!"unsupported event kind {e.kind}"

/-- `OFF_q + P - N` for the part value `u` of `nq` digits: sparse digit trees or two literals. -/
def partPN (offs : Array Nat) (u nq : Nat) : Option Expr × Option Expr :=
  if countNZ offs 16 u nq ≤ 16 then ScalarCheck.CheckpointGen.split offs u nq
  else
    let o := offs[nq]!
    if u ≥ o then ((if u == o then none else some (mkRawNatLit (u - o))), none)
    else (none, some (mkRawNatLit (o - u)))

/-- the digits (index, new, old) where `u` and `v` (`cnt` digits) differ; stops early past `lim`. -/
partial def diffGo (lim u v cnt base : Nat) (acc : Array (Nat × Nat × Nat)) : Array (Nat × Nat × Nat) :=
  if u == v || acc.size > lim then acc
  else if cnt ≤ 1 then acc.push (base, u, v)
  else
    let h := cnt / 2
    let acc := diffGo lim (u % 2 ^ (wb * h)) (v % 2 ^ (wb * h)) h base acc
    diffGo lim (u >>> (wb * h)) (v >>> (wb * h)) (cnt - h) (base + h) acc

def diffDigits (u v cnt lim : Nat) : Array (Nat × Nat × Nat) := diffGo lim u v cnt 0 #[]

/-- shift-add tree of `Σ val·X^k` over the given (k, val), `none` if empty. -/
partial def sumTree (xs : Array (Nat × Nat)) : Option Expr :=
  if xs.size == 0 then none
  else if xs.size == 1 then
    let (k, x) := xs[0]!
    some (if k == 0 then mkRawNatLit x else natC ``Nat.shiftLeft (mkRawNatLit x) (mkRawNatLit (wb * k)))
  else
    let h := xs.size / 2
    match sumTree (xs.extract 0 h), sumTree (xs.extract h xs.size) with
    | some a, some b => some (natC ``Nat.add a b)
    | a, none => a
    | none, b => b

def deltaPN (dl : Array (Nat × Nat × Nat)) : Option Expr × Option Expr :=
  (sumTree (dl.filterMap fun (k, a, b) => if a > b then some (k, a - b) else none),
   sumTree (dl.filterMap fun (k, a, b) => if a < b then some (k, b - a) else none))

syntax (name := genCkPart) "gen_ck_part " ident ppSpace num ppSpace num ppSpace num " from " num ppSpace num ppSpace num ppSpace num ppSpace num : command
@[command_elab genCkPart] def elabGenCkPart : CommandElab := fun stx => do
  unless X == 2 ^ wb do throwError "gen_ck_part: digit width changed"
  let q := nat! stx[2]; let dlo := nat! stx[3]; let dhi := nat! stx[4]
  let nr := nat! stx[6]; let d := nat! stx[7]; let nk := nat! stx[8]; let v := nat! stx[9]; let C := nat! stx[10]
  let nq := dhi - dlo
  let env ← getEnv
  let ns ← getCurrNamespace
  let offs := offTable
  let offq := offs[nq]!
  let mut R : Array Nat := #[]
  for r in [0:2 ^ d] do
    let row : Array (Nat × Int) := if r < nk then #[(r, (v : Int))] else #[]
    R := R.push (partVal (← ofM <| packStart r row) dlo nq)
  let S := stx[1].getId.toString
  -- keyframe: digits against OFF_q (`p`, `n`); delta: the few digits changed since the previous emission of the
  -- register (`dp`, `dn`, listed in `{S}d{q}_{i}`), at most `K` deltas in a row.
  let K := 8
  let mut prev : Array Nat := R
  let mut age : Array Nat := Array.replicate (2 ^ d) 0
  addDef (ns ++ Name.mkSimple s!"{S}o{q}") natT (mkRawNatLit offq)
  let emit (i : Nat) (rs : Array Nat) (R prev age : Array Nat) : CommandElabM (Array Nat × Array Nat) := do
    let mut prev := prev
    let mut age := age
    let mut ds : Array Nat := #[]
    for r in rs do
      let dl := diffDigits R[r]! prev[r]! nq 16
      if i > 0 && age[r]! < K && dl.size ≤ 16 then
        let (pd, nd) := deltaPN dl
        if let some e := pd then addDef (ns ++ Name.mkSimple s!"{S}dp{q}_{i}_{r}") natT e
        if let some e := nd then addDef (ns ++ Name.mkSimple s!"{S}dn{q}_{i}_{r}") natT e
        ds := ds.push r
        age := age.set! r (age[r]! + 1)
      else
        let (p, n) := partPN offs R[r]! nq
        if let some p := p then addDef (ns ++ Name.mkSimple s!"{S}p{q}_{i}_{r}") natT p
        if let some n := n then addDef (ns ++ Name.mkSimple s!"{S}n{q}_{i}_{r}") natT n
        age := age.set! r 0
      prev := prev.set! r R[r]!
    addDef (ns ++ Name.mkSimple s!"{S}c{q}_{i}") (listT natT) (mkList natT (rs.map mkRawNatLit))
    addDef (ns ++ Name.mkSimple s!"{S}d{q}_{i}") (listT natT) (mkList natT (ds.map mkRawNatLit))
    return (prev, age)
  (prev, age) ← emit 0 (Array.range (2 ^ d)) R prev age
  for i in [0:C] do
    let evs ← segEvents env (segName ns i)
    let R0 := R
    R ← ofM <| evs.foldlM (fun R e => stepP offq nr R e) R
    (prev, age) ← emit (i + 1) ((Array.range (2 ^ d)).filter fun r => R[r]! != R0[r]!) R prev age

syntax (name := genCkJoin) "gen_ck_join " ident ppSpace num " from " num ppSpace num (ppSpace num)+ : command
@[command_elab genCkJoin] def elabGenCkJoin : CommandElab := fun stx => do
  let Q := nat! stx[2]; let d := nat! stx[4]; let C := nat! stx[5]
  let dlos := stx[6].getArgs.map nat!
  unless dlos.size == Q do throwError "gen_ck_join: {Q} digit offsets expected"
  let env ← getEnv
  let ns ← getCurrNamespace
  let S := stx[1].getId.toString
  let nmP (k : String) (q i r : Nat) : Name := ns ++ Name.mkSimple s!"{S}{k}{q}_{i}_{r}"
  let changed (q i : Nat) : CommandElabM (Array Nat) := do
    let some es := listElems (← constVal env (ns ++ Name.mkSimple s!"{S}c{q}_{i}")) #[] | throwError "gen_ck_join: bad change list"
    return es.filterMap natOf
  let natAdd (a b : Expr) : Expr := natC ``Nat.add a b
  let deltas (q i : Nat) : CommandElabM (Std.HashSet Nat) := do
    let some es := listElems (← constVal env (ns ++ Name.mkSimple s!"{S}d{q}_{i}")) #[] | throwError "gen_ck_join: bad delta list"
    return Std.HashSet.ofList (es.filterMap natOf).toList
  -- last[q][r]: segment index of the latest change of part q of register r; `{S}v{q}_{i}_{r}` its value
  let mut last : Array (Array Nat) := Array.replicate Q (Array.replicate (2 ^ d) 0)
  let nmV (q i r : Nat) : Name := ns ++ Name.mkSimple s!"{S}v{q}_{i}_{r}"
  let valE (q i r : Nat) (isDelta : Bool) (prevI : Nat) : Expr := Id.run do
    let (base, pk, nk) := if isDelta then (mkConst (nmV q prevI r), "dp", "dn") else (mkConst (ns ++ Name.mkSimple s!"{S}o{q}"), "p", "n")
    let e := if env.contains (nmP pk q i r) then natAdd base (mkConst (nmP pk q i r)) else base
    return if env.contains (nmP nk q i r) then natC ``Nat.sub e (mkConst (nmP nk q i r)) else e
  let leafOf (last : Array (Array Nat)) (r : Nat) : Expr := Id.run do
    let mut acc : Option Expr := none
    for q in [0:Q] do
      let v := mkConst (nmV q last[q]![r]! r)
      let e := if dlos[q]! == 0 then v else natC ``Nat.shiftLeft v (mkRawNatLit (wb * dlos[q]!))
      acc := some (match acc with | none => e | some a => natAdd a e)
    return mkApp (mkConst ``ScalarCheck.PT.leaf) acc.get!
  let ptT := mkConst ``ScalarCheck.PT
  let node (a b : Expr) : Expr := mkApp2 (mkConst ``ScalarCheck.PT.node) a b
  let mut T : Array (Array Expr) := #[]
  T := T.push (Array.range (2 ^ d) |>.map fun r => mkConst (ns ++ Name.mkSimple s!"{S}0_{r}"))
  for q in [0:Q] do
    for r in [0:2 ^ d] do
      addDef (nmV q 0 r) natT (valE q 0 r false 0)
  for r in [0:2 ^ d] do
    addDef (ns ++ Name.mkSimple s!"{S}0_{r}") ptT (leafOf last r)
  for h in [1:d + 1] do
    let b := 2 ^ (d - h)
    T := T.push ((Array.range b).map fun key => node T[h - 1]![key]! T[h - 1]![key + b]!)
  addDef (ns ++ Name.mkSimple s!"{S}0") ptT T[d]![0]!
  for i in [1:C + 1] do
    let mut chg : Std.HashSet Nat := {}
    for q in [0:Q] do
      let ds ← deltas q i
      for r in ← changed q i do
        chg := chg.insert r
        addDef (nmV q i r) natT (valE q i r (ds.contains r) last[q]![r]!)
        last := last.modify q (·.set! r i)
    for r in chg.toArray.qsort (· < ·) do
      let nm := ns ++ Name.mkSimple s!"{S}{i}_{r}"
      addDef nm ptT (leafOf last r)
      T := T.modify 0 (·.set! r (mkConst nm))
      for h in [1:d + 1] do
        let b := 2 ^ (d - h)
        let key := r % b
        T := T.modify h (·.set! key (node T[h - 1]![key]! T[h - 1]![key + b]!))
    addDef (ns ++ Name.mkSimple s!"{S}{i}") ptT T[d]![0]!

end ScalarCheck.CheckpointGenPar

namespace WarpCheck.LabelGenPar
open Lean Elab Command ScalarCheck.Decode ScalarCheck.DecodePar WarpCheck.LabelGen

/-- Values of a `TrieCheck.Trie` by key (leaves in `inLeafOrder`), following constants. -/
partial def trieLeaves (env : Environment) (e : Expr) (acc : Array Nat) : CommandElabM (Array Nat) := do
  match e with
  | .const n _ => trieLeaves env (← constVal env n) acc
  | _ =>
    if e.isAppOfArity ``TrieCheck.Trie.node 2 then
      let acc ← trieLeaves env e.appFn!.appArg! acc
      trieLeaves env e.appArg! acc
    else if e.isAppOfArity ``TrieCheck.Trie.leaf 1 then
      let some v := natOf e.appArg! | throwError "trie leaf expected"
      return acc.push v
    else throwError "trie expected"

def byKey (leaves : Array Nat) : Array Nat :=
  let d := leaves.size.log2
  (Array.range (2 ^ d)).map fun k => leaves.getD (regOf d k) 0

/-- `gen_label_par st0 stF evs rAll gl exits resW tab d K N v h B nq n c1 c2` (the arguments of `gen_label_states`
with the frame table `tab` and an unused depth `d` added, `K` label segments over `N` scalar segments). -/
syntax (name := labPar) "gen_label_par " ident ident ident ident ident ident ident ident num num num num num num num num num num : command
@[command_elab labPar] def elabLabPar : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let env ← getEnv
  let nm (i : Nat) := ns ++ stx[i].getId
  let n! (i : Nat) := nat! stx[i]
  let s0 := byKey (← trieLeaves env (mkConst (nm 1)) #[])
  let fdim := (byKey (← trieLeaves env (mkConst (nm 8)) #[])).map (· &&& 255)
  let cd (f : Nat) := fdim.getD f 0
  let k := n! 10; let N := n! 11
  let mut ps : Array (Name × Array MEv) := #[]
  for i in [0:N] do ps := ps.push (segName ns i, ← segEvents env (segName ns i))
  let sizes := ps.map (·.2.size)
  let S0 : Array Nat := (Array.range 4096).map fun r => s0.getD r 0
  let mut S := S0
  let nat := mkConst ``Nat; let ev := mkConst ``WarpCheck.WEv; let tr := mkConst ``TrieCheck.Trie
  let nmi (s : String) (i : Nat) := ns ++ Name.mkSimple s!"{s}{i}"
  let tot := sizes.foldl (· + ·) 0
  let mut j := 0; let mut cnt := 0
  let mut rs : Array Nat := #[]; let mut grps : Array (Array Name) := #[]; let mut cuts : Array (Nat × Array Nat) := #[]
  for i in [0:k] do
    let mut grp : Array (Name × Array MEv) := #[]
    while j < ps.size && (i == k - 1 || cnt * k < (i + 1) * tot) do
      grp := grp.push ps[j]!; cnt := cnt + sizes[j]!; j := j + 1
    if grp.size == 0 then throwError "gen_label_par: empty label segment {i}"
    let r0 := rs.size
    for c in grp do
      for e in c.2 do
        let regs := if e.kind == 3 then #[] else e.regs
        for r in regs do
          if e.kind == 4 then rs := rs.push (cd S[r]! - cd e.f)
          else if (e.kind == 0 || e.kind == 1) && S[r]! != e.f then rs := rs.push (cd e.f - cd S[r]!)
          S := S.set! r e.f
    grps := grps.push (grp.map (·.1)); cuts := cuts.push (rs.size - r0, S)
  let v := n! 12; let h := n! 13; let B := n! 14; let n := n! 16
  let ex := (Array.range n).filter fun r => B ≤ r && cd S[r]! < h
  let res := (Array.range (n! 15)).map fun q =>
    if ex.contains (B + q) then cd S[B + q]! - cd S0[B + q]! else h - cd S0[B + q]!
  unless res.all (· ≤ h) do throwError "gen_label_par: a res value exceeds h"
  let lits (a : Array Nat) := a.map lit
  addChunks (nm 4) natT (lits rs) (n! 17)
  addTrie (nm 2) 12 0 S
  let gl := (Array.range n).filter fun r => v ≤ r && S0[r]! != 0
  addChunks (nm 5) natT (lits gl) gl.size
  addChunks (nm 6) natT (lits ex) ex.size
  addChunks (nm 7) natT (lits res) (n! 18)
  addDef (nmi "labS" 0) tr (mkConst (nm 1)); addDef (nmi "labQ" 0) (listT nat) (mkConst (nm 4))
  for i in [0:k] do
    let (dd, Si) := cuts[i]!
    addDef (nmi "labE" i) (listT ev) (catE ev (grps[i]!.map mkConst))
    addDef (nmi "labL" i) (listT (listT ev)) (mkList (listT ev) (grps[i]!.map mkConst))
    let Q := mkConst (nmi "labQ" i)
    if i < k - 1 then
      addDef (nmi "labR" i) (listT nat) (mkApp3 (mkConst ``List.take [0]) nat (lit dd) Q)
      addDef (nmi "labQ" (i + 1)) (listT nat) (mkApp3 (mkConst ``List.drop [0]) nat (lit dd) Q)
      addTrie (nmi "labS" (i + 1)) 12 0 Si
    else
      addDef (nmi "labR" i) (listT nat) Q
      addDef (nmi "labS" (i + 1)) tr (mkConst (nm 2))
  let cat (s : String) := " ++ (".intercalate ((List.range k).map fun i => s!"{s}{i}") ++ String.mk (List.replicate (k - 1) ')')
  let sp (s : String) := " ".intercalate ((List.range k).map fun i => s!"{s}{i}")
  let segs := " ".intercalate ((List.range N).map fun i => s!"seg{i}")
  cmd s!"theorem lab_evs : {cat "labE"} = {stx[3].getId} := by delta {sp "labE"} {stx[3].getId}; simp only [List.append_assoc]"
  cmd s!"theorem lab_rs : {cat "labR"} = {stx[4].getId} := by delta {sp "labR"} {sp "labQ"}; simp only [List.take_append_drop]"
  let _ := segs

/-- `pack_label_states labS labN tab tabN K w tw`: `labN{i}` (i ≤ K) packs the leaves of `labS{i}` as `w`-bit
digits by key, `tabN` packs the leaves of `tab` as `tw`-bit digits (data for `WarpCheck.LabelPack.checkSegP`,
which re-checks every digit against the tries). -/
syntax (name := packLab) "pack_label_states " ident ident ident ident num num num : command
@[command_elab packLab] def elabPackLab : CommandElab := fun stx => do
  let ns ← getCurrNamespace
  let env ← getEnv
  let pack (w : Nat) (vs : Array Nat) : Nat := Id.run do
    let mut acc := 0
    for i in [0:vs.size] do acc := acc ||| (vs[i]! <<< (w * i))
    return acc
  let K := nat! stx[5]; let w := nat! stx[6]; let tw := nat! stx[7]
  let S := stx[1].getId.toString; let L := stx[2].getId.toString
  for i in [0:K + 1] do
    let vs := byKey (← trieLeaves env (mkConst (ns ++ Name.mkSimple s!"{S}{i}")) #[])
    addDef (ns ++ Name.mkSimple s!"{L}{i}") natT (lit (pack w vs))
  let ts := byKey (← trieLeaves env (mkConst (ns ++ stx[3].getId)) #[])
  addDef (ns ++ stx[4].getId) natT (lit (pack tw ts))

end WarpCheck.LabelGenPar
