import Work.Bridge401.GNetDef
import Work.Gauge.Defs

/-!
# The mixed-dispatch glue of `GXD.C588M`, in general form

The pinned mixed price file (`build-out/candidate-price.json`, `format: mixed-dispatch/1`)
serves each of the 72 calls `(ρ, l) : Fin 8 × Fin 9` of the PR #401 nine-stage word with one
of TWO provider words: `iCK = GXD.C588.ginv` on 53 calls and `iAT = GXD.C588AT.ginv` on 19
(`Gen.C588MDispatch.provList`; `prov_counts : count ck = 53 ∧ count atm3 = 19`).

Running the word through the submission route means instantiating
`GX.engine_of_ginv_401` at the per-call table

    I := fun ρ l => if d ρ l then iAT else iCK          (d := the dispatch predicate)

which needs exactly two obligations, both independent of the concrete C588/C588AT data:

* **`htve`** — `G401` requires the 72 calls to share their lines `tv` and entrance labels `ent`
  (`GX.bridge401_gcertTbl`).  `ck` and `atm3` are one word after the width unification, so
  `(GXD.C588.ginv).tv = (GXD.C588AT.ginv).tv` and likewise for `ent`; the mixed table then has
  `htve` by a 4-way case split on the two dispatch bits.
* **`price`** — `GX.G401.cost_split` turns the 72-call cost sum into the weighted invoice
  `53 * iCK.cost + 19 * iAT.cost` from the two counting facts.

Both are proved below, for any two packages sharing `tv`/`ent` and any dispatch function, so
the only data-level facts a concrete instantiation still owes are:

    htv  : (GXD.C588.ginv).tv  = (GXD.C588AT.ginv).tv      -- shared lines
    hent : (GXD.C588.ginv).ent = (GXD.C588AT.ginv).ent     -- shared entrance labels
    hd53 : (univ.filter fun k => d k.1 k.2 = false).card = 53
    hd19 : (univ.filter fun k => d k.1 k.2 = true ).card = 19

(and, as for every `GInvE`, `iCK.hunit/hgap` and `iAT.hunit/hgap`).  The instantiation itself is
`Work/FourierC588/SeamMixed.lean`.

See the accompanying report for why the generated `ck-hybrid` / `atm3-hybrid` words cannot be
used as `GXD.C588` / `GXD.C588AT` unchanged (they fail `GS.scalCheck`, so `ginvOf` — and hence
`tv`/`ent` — is not available for them).  No `sorry`.
-/

set_option maxRecDepth 100000
namespace OAI
namespace PowerSaving
namespace GX
open Binary Matrix Finset
noncomputable section

variable {H T Sl C : Type} [Fintype H] [DecidableEq H] [Fintype T] [DecidableEq T]
  [Fintype Sl] [DecidableEq Sl] [Fintype C] [DecidableEq C]

/-- The mixed dispatch table: `iAT` where the dispatch predicate `d` is true, `iCK` where it is
false.  This is `GX.G401.I` of the submission route. -/
def dispatchTbl (iCK iAT : GInvE H T Sl C) (d : Fin 8 → Fin 9 → Bool) :
    Fin 8 → Fin 9 → GInvE H T Sl C :=
  fun ρ l => if d ρ l then iAT else iCK

/-- **`htve` of the mixed dispatch table.**  Two packages that share their lines `tv` and their
entrance labels `ent` give a dispatched table whose 72 calls share them (4-way case split on the
two dispatch bits, with `rfl` on the three diagonal/equal cases and the shared facts off it). -/
theorem dispatchTbl_htve (iCK iAT : GInvE H T Sl C) (d : Fin 8 → Fin 9 → Bool)
    (htv : iCK.tv = iAT.tv) (hent : iCK.ent = iAT.ent) :
    ∀ (ρ ρ' : Fin 8) (l l' : Fin 9),
      (dispatchTbl iCK iAT d ρ l).tv = (dispatchTbl iCK iAT d ρ' l').tv
        ∧ (dispatchTbl iCK iAT d ρ l).ent = (dispatchTbl iCK iAT d ρ' l').ent := by
  intro ρ ρ' l l'
  unfold dispatchTbl
  cases h1 : d ρ l <;> cases h2 : d ρ' l' <;> simp [htv, hent]

/-- **`price` of the mixed dispatch table** (`GX.G401.cost_split`).  If the dispatch selects
`iCK` on 53 of the 72 calls and `iAT` on the other 19 and each package has a constant cost, the
72-call cost sum is the weighted invoice `53 * iCK.cost + 19 * iAT.cost`. -/
theorem dispatchTbl_cost (iCK iAT : GInvE H T Sl C) (d : Fin 8 → Fin 9 → Bool)
    (hd53 : (univ.filter (fun k : Fin 8 × Fin 9 => d k.1 k.2 = false)).card = 53)
    (hd19 : (univ.filter (fun k : Fin 8 × Fin 9 => d k.1 k.2 = true)).card = 19)
    (φ : ℕ → ℝ) :
    (∑ ρ : Fin 8, ∑ l : Fin 9, (dispatchTbl iCK iAT d ρ l).cost φ)
      = 53 * iCK.cost φ + 19 * iAT.cost φ := by
  refine cost_split (dispatchTbl iCK iAT d) iCK.cost iAT.cost d ?_ ?_ hd53 hd19 φ
  · intro ρ l h
    simp [dispatchTbl, h]
  · intro ρ l h
    simp [dispatchTbl, h]

end
end GX
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.GX.dispatchTbl_htve
#print axioms OAI.PowerSaving.GX.dispatchTbl_cost
