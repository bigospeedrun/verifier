import Submission.Work.Mixed.Rate2979Nb1

/-!
# The histogram bookkeeping of the FULL cut of NB1 (suffix 2979Nb1): unit -> body -> cut (nothing to split)

nb1-port (2026-10-21), afc-cut's Hist2979Fc.lean (fc-rate's `Hist3945F.lean` pattern) with NB1's numbers.  NB1
(the hub's word of PR #2979, T74 clock, with the table-MIP fill NB1s7, SOL-NB1 seed 7) has the unit profile
`unit2979Nb1` (its PROFILE.json, sha256 45bd5677...); its 16,576 rank-48 blocks are ALL literal heads (children 8/10), and every other
block has rank at most 23.
* M1's `cut_heads_full` removes the 16,576 heads from `headWord ++ body`: the body has the profile `body2979Nb1`
  (`hbody2979Nb1`), which has no rank-48 block (`body2979Nb1_no48`);
* M1's `splitWord 24 24` therefore has NOTHING to split: by `hist_splitWord 24 24` the histogram is unchanged
  (`hsplit2979Nb1`, stated in exactly the shape of the right-hand side of `hist_splitWord` with `a = b = 24` and `w` =
  the body), and the body profile IS R5's cut profile (`body2979Nb1_eq_cut`);
* `hcut2979Nb1`: unit -> cut in one identity; `mass2979Nb1`: the rank mass drops by exactly 48 x 16,576;
* separation: `cut2979Nb1_sep` (every paid rank < 25, in fact <= 23), `cut2979Nb1_no48`, `cut2979Nb1_no24`;
* negatives (`decide`): one head more breaks `hbody2979Nb1`; the unit profile is not the cut profile.
Prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.MX
open BlockAccounting

/-- NB1's unit profile (PROFILE.json of the NB1s7 fill): `(rank, count)`. -/
def unit2979Nb1 : List (ℕ × ℕ) :=
  [(1, 1630638), (2, 470196), (3, 154512), (4, 71928), (5, 11988), (6, 4), (7, 4), (8, 5328), (17, 8), (21, 2),
   (23, 25904), (48, 16576)]

/-- The body after the full cut removes the 16,576 literal heads: no rank-48 block is left. -/
def body2979Nb1 : List (ℕ × ℕ) :=
  [(1, 1630638), (2, 470196), (3, 154512), (4, 71928), (5, 11988), (6, 4), (7, 4), (8, 5328), (17, 8), (21, 2),
   (23, 25904)]

/-- the ranks that occur in the three profiles, and the split ranks 24 and 48 -/
def keys2979Nb1 : List ℕ := [1, 2, 3, 4, 5, 6, 7, 8, 17, 21, 23, 24, 48]

theorem histFn_eq_zero_of_keys2979Nb1 {l : List (ℕ × ℕ)} {K : List ℕ} (hl : ∀ q ∈ l, q.1 ∈ K) {r : ℕ}
    (hr : r ∉ K) : histFn l r = 0 := by
  by_contra hne
  have := mem_keys_of_histFn_ne_zero l r hne
  unfold keys at this
  rw [List.mem_toFinset, List.mem_map] at this
  obtain ⟨q, hq, rfl⟩ := this
  exact hr (hl q hq)

theorem unit2979Nb1_keys : ∀ q ∈ unit2979Nb1, q.1 ∈ keys2979Nb1 := by decide
theorem body2979Nb1_keys : ∀ q ∈ body2979Nb1, q.1 ∈ keys2979Nb1 := by decide
theorem cut2979Nb1_keys : ∀ q ∈ cut2979Nb1, q.1 ∈ keys2979Nb1 := by decide

/-- With nothing to split, the body profile is R5's cut profile. -/
theorem body2979Nb1_eq_cut : body2979Nb1 = cut2979Nb1 := rfl

/-- Removing the 16,576 literal heads (rank 48 = 24 + 24) from the unit profile leaves the body profile. -/
theorem hbody2979Nb1 : ∀ r, histFn body2979Nb1 r + (if r = 24 + 24 then 16576 else 0) = histFn unit2979Nb1 r := by
  intro r
  by_cases hr : r ∈ keys2979Nb1
  · have h : ∀ r ∈ keys2979Nb1, histFn body2979Nb1 r + (if r = 24 + 24 then 16576 else 0) = histFn unit2979Nb1 r := by
      decide
    exact h r hr
  · have h48 : r ≠ 24 + 24 := fun h => hr (by subst h; decide)
    rw [histFn_eq_zero_of_keys2979Nb1 body2979Nb1_keys hr, histFn_eq_zero_of_keys2979Nb1 unit2979Nb1_keys hr, if_neg h48]

/-- No rank-48 block is left in the body. -/
theorem body2979Nb1_no48 : histFn body2979Nb1 (24 + 24) = 0 := by decide

/-- **The split of nothing**: `splitWord 24 24` on the body leaves R5's cut profile, in the shape of the right-hand side
of M1's `hist_splitWord 24 24` (with `w` = the body).  Both added terms are zero (`body2979Nb1_no48`). -/
theorem hsplit2979Nb1 : ∀ r, histFn cut2979Nb1 r
    = (if r = 24 + 24 then 0 else histFn body2979Nb1 r) + (if r = 24 then histFn body2979Nb1 (24 + 24) else 0)
      + (if r = 24 then histFn body2979Nb1 (24 + 24) else 0) := by
  intro r
  by_cases hr : r ∈ keys2979Nb1
  · have h : ∀ r ∈ keys2979Nb1, histFn cut2979Nb1 r
        = (if r = 24 + 24 then 0 else histFn body2979Nb1 r) + (if r = 24 then histFn body2979Nb1 (24 + 24) else 0)
          + (if r = 24 then histFn body2979Nb1 (24 + 24) else 0) := by
      decide
    exact h r hr
  · have h48 : r ≠ 24 + 24 := fun h => hr (by subst h; decide)
    have h24 : r ≠ 24 := fun h => hr (by subst h; decide)
    rw [histFn_eq_zero_of_keys2979Nb1 cut2979Nb1_keys hr, histFn_eq_zero_of_keys2979Nb1 body2979Nb1_keys hr, if_neg h48,
      if_neg h24]

/-- The same for any body whose histogram is the body profile (the form M1's lemmas produce). -/
theorem hsplit2979Nb1_of {hb : ℕ → ℕ} (h : ∀ r, hb r + (if r = 24 + 24 then 16576 else 0) = histFn unit2979Nb1 r) :
    ∀ r, (if r = 24 + 24 then 0 else hb r) + (if r = 24 then hb (24 + 24) else 0)
      + (if r = 24 then hb (24 + 24) else 0) = histFn cut2979Nb1 r := by
  have hb' : ∀ r, hb r = histFn body2979Nb1 r := by
    intro r
    have h1 := h r
    have h2 := hbody2979Nb1 r
    omega
  intro r
  simp only [hb']
  exact (hsplit2979Nb1 r).symm

/-- Unit -> cut in one identity: the 16,576 rank-48 blocks (all heads) go, nothing else changes. -/
theorem hcut2979Nb1 : ∀ r, histFn cut2979Nb1 r + (if r = 24 + 24 then 16576 else 0) = histFn unit2979Nb1 r := by
  intro r
  rw [← body2979Nb1_eq_cut]
  exact hbody2979Nb1 r

/-- The rank mass of one unit drops by exactly 48 x 16,576 (the heads). -/
theorem mass2979Nb1 : (cut2979Nb1.map fun b => b.1 * b.2).sum + 48 * 16576
    = (unit2979Nb1.map fun b => b.1 * b.2).sum := by
  decide

/-- The unit's rank mass is 65,088 x 74 (one T74 clock unit, tablemip TABLE-MIP.md). -/
theorem unit2979Nb1_mass : (unit2979Nb1.map fun b => b.1 * b.2).sum = 65088 * 74 := by decide

/-- The number of paid blocks: 2,370,512 = 2,387,088 - 16,576 heads. -/
theorem count2979Nb1 : (cut2979Nb1.map Prod.snd).sum + 16576 = (unit2979Nb1.map Prod.snd).sum := by decide

/-- Separation of the full cut: every paid rank is below the cut target 25 (in fact at most 23). -/
theorem cut2979Nb1_sep : ∀ b ∈ cut2979Nb1, 1 ≤ b.1 ∧ b.1 < 25 := by decide

/-- No paid rank-48 block is left after the full cut. -/
theorem cut2979Nb1_no48 : histFn cut2979Nb1 48 = 0 := by decide

/-- No rank-24 block either: the split created nothing. -/
theorem cut2979Nb1_no24 : histFn cut2979Nb1 24 = 0 := by decide

/-- Negative control: one literal head more (16,577) breaks the body identity at rank 48. -/
theorem hbody2979Nb1_sharp : histFn body2979Nb1 48 + 16577 ≠ histFn unit2979Nb1 48 := by decide

/-- Negative control: the unit profile is not the cut profile (rank 48). -/
theorem unit2979Nb1_ne_cut : histFn unit2979Nb1 48 ≠ histFn cut2979Nb1 48 := by decide

end OAI.PowerSaving.MX

#print axioms OAI.PowerSaving.MX.body2979Nb1_eq_cut
#print axioms OAI.PowerSaving.MX.hbody2979Nb1
#print axioms OAI.PowerSaving.MX.body2979Nb1_no48
#print axioms OAI.PowerSaving.MX.hsplit2979Nb1
#print axioms OAI.PowerSaving.MX.hsplit2979Nb1_of
#print axioms OAI.PowerSaving.MX.hcut2979Nb1
#print axioms OAI.PowerSaving.MX.mass2979Nb1
#print axioms OAI.PowerSaving.MX.unit2979Nb1_mass
#print axioms OAI.PowerSaving.MX.count2979Nb1
#print axioms OAI.PowerSaving.MX.cut2979Nb1_sep
#print axioms OAI.PowerSaving.MX.cut2979Nb1_no48
#print axioms OAI.PowerSaving.MX.cut2979Nb1_no24
#print axioms OAI.PowerSaving.MX.hbody2979Nb1_sharp
#print axioms OAI.PowerSaving.MX.unit2979Nb1_ne_cut
