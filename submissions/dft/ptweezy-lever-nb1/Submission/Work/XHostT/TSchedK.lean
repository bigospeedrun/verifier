import Submission.Work.XHostT.KCheck
import Submission.Work.XHostT.TDef

/-!
# (key: bridge-host-cross) Soundness of the kernel checker of a cross-replica host table

`chkPieceCount ct rt resT NC R κ 1 bs rs = some c` (one host kind `κ`, Work/XHostT/KCheck.lean) means: there is a list
of `c` records `(i, k, q)` with `224 κ ≤ i < 224 κ + 224`, each record's call `k < NC` and slot `q < R` hosted at `i`
by the call tree `ct`, inside the kind's window, strictly ordered by `(i, k)`, and the residuals of each bin plus its
remainder (packed in `rt`) equal the rank (`kind_sound`).  With one such theorem per kind and the counts summing to
`NC * R`, every slot of every call is hosted, in its window, at most one slot per call and host, and every host's
residual load plus remainder is its rank (`table_sound`).  The streams `bs`, `rs` are existential: the decoders need no
proof.  Written by p-a3 (wht45/lever, 19 Oct 2026); prepared with assistance from Claude.  No `sorry`.
-/

namespace OAI.PowerSaving.XHostT.K
open Finset

/-- the conditions on one record `x = (i, k, q)` of a host kind with window `w`. -/
def RecOK (ct : CT) (NC R : ℕ) (w : ℕ × ℕ) (x : ℕ × ℕ × ℕ) : Prop :=
  x.2.1 < NC ∧ x.2.2 < R ∧ rowAt (ct.get x.2.1).1 x.2.2 = x.1 ∧ w.1 ≤ (ct.get x.2.1).2.1 ∧ (ct.get x.2.1).2.1 ≤ w.2

/-- the residual of a record. -/
def resOf (ct : CT) (resT : ℕ) (x : ℕ × ℕ × ℕ) : ℕ := resAt resT (ct.get x.2.1).2.2 x.2.2

/-- the order of the records: by bin, then by call. -/
def LexIK (a b : ℕ × ℕ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1)

/-- the remainder of host index `i`. -/
def remAt (rt : CT) (i : ℕ) : ℕ := ((rt.get (i / 224)).1 >>> (6 * (i % 224))) &&& 63

lemma chkRecs_sound (ct : CT) (resT NC R i lo hi : ℕ) : ∀ (m kmin load : ℕ) (rd : Rd) (load' : ℕ) (rd' : Rd),
    chkRecs ct resT NC R i lo hi m kmin load rd = some (load', rd') →
    ∃ L : List (ℕ × ℕ × ℕ), L.length = m ∧
      (∀ x ∈ L, x.1 = i ∧ kmin ≤ x.2.1 ∧ RecOK ct NC R (lo, hi) x) ∧
      L.Pairwise LexIK ∧ load' = load + (L.map (resOf ct resT)).sum := by
  intro m
  induction m with
  | zero =>
    intro kmin load rd load' rd' h
    simp only [chkRecs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨[], rfl, by simp, List.Pairwise.nil, by simp⟩
  | succ m ih =>
    intro kmin load rd load' rd' h
    simp only [chkRecs, cond_eq_if] at h
    split_ifs at h with hc
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at hc
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
    obtain ⟨L, hlen, hall, hpw, hload⟩ := ih _ _ _ _ _ h
    refine ⟨(i, (rd.next 22 128).1 &&& 4095, (rd.next 22 128).1 >>> 12) :: L, by simp [hlen], ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨rfl, h1, h2, h3, h4, h5, h6⟩
      · obtain ⟨hi, hk, hok⟩ := hall x hx
        exact ⟨hi, by omega, hok⟩
    · refine List.Pairwise.cons (fun x hx => ?_) hpw
      obtain ⟨hi, hk, -⟩ := hall x hx
      right
      refine ⟨hi.symm, ?_⟩
      show (rd.next 22 128).1 &&& 4095 < x.2.1
      omega
    · rw [hload, List.map_cons, List.sum_cons]
      simp only [resOf]
      ring

lemma chkBins_sound (ct : CT) (resT NC R lo hi rk rp : ℕ) : ∀ (n b i cnt : ℕ) (bs rs : Rd) (cnt' : ℕ) (bs' rs' : Rd),
    chkBins ct resT NC R lo hi rk rp n b i cnt bs rs = some (cnt', bs', rs') →
    ∃ L : List (ℕ × ℕ × ℕ), cnt' = cnt + L.length ∧
      (∀ x ∈ L, i ≤ x.1 ∧ x.1 < i + n ∧ RecOK ct NC R (lo, hi) x) ∧ L.Pairwise LexIK ∧
      ∀ b' < n, ((L.filter (fun x => x.1 = i + b')).map (resOf ct resT)).sum + ((rp >>> (6 * (b + b'))) &&& 63) = rk := by
  intro n
  induction n with
  | zero =>
    intro b i cnt bs rs cnt' bs' rs' h
    simp only [chkBins, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact ⟨[], by simp, by simp, List.Pairwise.nil, fun b' hb' => absurd hb' (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro b i cnt bs rs cnt' bs' rs' h
    simp only [chkBins] at h
    split at h
    · rename_i load rs1 hrec
      simp only [cond_eq_if] at h
      split_ifs at h with hc
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hc
      obtain ⟨⟨hc1, -⟩, -⟩ := hc
      obtain ⟨L1, hlen1, hall1, hpw1, hload1⟩ := chkRecs_sound ct resT NC R i lo hi _ 0 0 rs load rs1 hrec
      obtain ⟨L2, hcnt2, hall2, hpw2, hsum2⟩ := ih _ _ _ _ _ _ _ _ h
      refine ⟨L1 ++ L2, ?_, ?_, ?_, ?_⟩
      · rw [hcnt2, List.length_append, hlen1]
        ring
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨hxi, -, hok⟩ := hall1 x hx
          exact ⟨by omega, by omega, hok⟩
        · obtain ⟨h1, h2, hok⟩ := hall2 x hx
          exact ⟨by omega, by omega, hok⟩
      · refine List.pairwise_append.mpr ⟨hpw1, hpw2, fun a ha c hc => ?_⟩
        left
        have := (hall1 a ha).1
        have := (hall2 c hc).1
        omega
      · intro b' hb'
        rcases Nat.eq_zero_or_pos b' with rfl | hpos
        · have e1 : L1.filter (fun x => x.1 = i + 0) = L1 := by
            apply List.filter_eq_self.mpr
            intro x hx
            simp [(hall1 x hx).1]
          have e2 : L2.filter (fun x => x.1 = i + 0) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro x hx
            have := (hall2 x hx).1
            simp only [decide_eq_true_eq]
            omega
          rw [List.filter_append, e1, e2, List.append_nil]
          simp only [Nat.add_zero] at hc1 ⊢
          rw [hload1] at hc1
          simpa using hc1
        · obtain ⟨b'', rfl⟩ : ∃ b'', b' = b'' + 1 := ⟨b' - 1, by omega⟩
          have e1 : L1.filter (fun x => x.1 = i + (b'' + 1)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro x hx
            have := (hall1 x hx).1
            simp only [decide_eq_true_eq]
            omega
          rw [List.filter_append, e1, List.nil_append]
          have := hsum2 b'' (by omega)
          rw [show i + 1 + b'' = i + (b'' + 1) by ring, show b + 1 + b'' = b + (b'' + 1) by ring] at this
          exact this
    · exact absurd h (by simp)

/-- **one host kind**: the records of a checked kind. -/
theorem kind_sound {ct rt : CT} {resT NC R κ c : ℕ} {bs rs : List ℕ}
    (h : chkPieceCount ct rt resT NC R κ 1 bs rs = some c) :
    ∃ L : List (ℕ × ℕ × ℕ), L.length = c ∧
      (∀ x ∈ L, 224 * κ ≤ x.1 ∧ x.1 < 224 * κ + 224 ∧ RecOK ct NC R (winOf ct κ) x) ∧ L.Pairwise LexIK ∧
      ∀ b' < 224, ((L.filter (fun x => x.1 = 224 * κ + b')).map (resOf ct resT)).sum + remAt rt (224 * κ + b')
        = rkN (κ % 9) := by
  simp only [chkPieceCount, chkKinds] at h
  split at h
  · rename_i cnt' bs' rs' hb
    simp only [cond_eq_if] at h
    split_ifs at h
    simp only [chkKinds, Option.some.injEq] at h
    subst h
    obtain ⟨L, hcnt, hall, hpw, hsum⟩ := chkBins_sound ct resT NC R _ _ _ _ 224 0 (224 * κ) 0 _ _ _ _ _ hb
    refine ⟨L, by rw [hcnt]; simp, hall, hpw, fun b' hb' => ?_⟩
    have e1 : (224 * κ + b') / 224 = κ := by omega
    have e2 : (224 * κ + b') % 224 = b' := by omega
    simp only [remAt, e1, e2]
    have := hsum b' hb'
    simpa using this
  · exact absurd h (by simp)

lemma pw_or {α : Type} {R : α → α → Prop} : ∀ {l : List α}, l.Pairwise R → ∀ {a b : α}, a ∈ l → b ∈ l → a ≠ b →
    R a b ∨ R b a
  | [], _, _, _, ha, _, _ => absurd ha (List.not_mem_nil)
  | x :: xs, h, a, b, ha, hb, hne => by
    rw [List.pairwise_cons] at h
    have ha2 := List.mem_cons.mp ha
    have hb2 := List.mem_cons.mp hb
    clear ha hb
    rcases ha2 with rfl | ha3 <;> rcases hb2 with rfl | hb3
    · exact absurd rfl hne
    · exact Or.inl (h.1 _ hb3)
    · exact Or.inr (h.1 _ ha3)
    · exact pw_or h.2 ha3 hb3 hne

lemma sum_range_list (f : ℕ → ℕ) : ∀ n, ∑ κ ∈ range n, f κ = ((List.range n).map f).sum
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, sum_range_list f n, List.range_succ, List.map_append, List.sum_append]
    simp

/-- **A checked table** (one kernel theorem per host kind, counts summing to `NC * R`): every slot of every call is
hosted in its kind's window, at most one slot per call and host, and every host's residual load plus remainder is the
rank of its kind. -/
theorem table_sound {ct rt : CT} {resT NC R NK : ℕ} (cK : ℕ → ℕ)
    (hK : ∀ κ < NK, ∃ bs rs, chkPieceCount ct rt resT NC R κ 1 bs rs = some (cK κ))
    (hsum : ((List.range NK).map cK).sum = NC * R) :
    (∀ k < NC, ∀ q < R, rowAt (ct.get k).1 q < 224 * NK ∧
        (winOf ct (rowAt (ct.get k).1 q / 224)).1 ≤ (ct.get k).2.1 ∧
        (ct.get k).2.1 ≤ (winOf ct (rowAt (ct.get k).1 q / 224)).2) ∧
    (∀ k < NC, ∀ q < R, ∀ q' < R, rowAt (ct.get k).1 q = rowAt (ct.get k).1 q' → q = q') ∧
    (∀ i < 224 * NK, (∑ x ∈ (range NC ×ˢ range R).filter (fun x => rowAt (ct.get x.1).1 x.2 = i),
        resAt resT (ct.get x.1).2.2 x.2) + remAt rt i = rkN (i / 224 % 9)) := by
  have hK' : ∀ κ, ∃ L : List (ℕ × ℕ × ℕ), κ < NK → (L.length = cK κ ∧
      (∀ x ∈ L, 224 * κ ≤ x.1 ∧ x.1 < 224 * κ + 224 ∧ RecOK ct NC R (winOf ct κ) x) ∧ L.Pairwise LexIK ∧
      ∀ b' < 224, ((L.filter (fun x => x.1 = 224 * κ + b')).map (resOf ct resT)).sum + remAt rt (224 * κ + b')
        = rkN (κ % 9)) := by
    intro κ
    by_cases hκ : κ < NK
    · obtain ⟨bs, rs, h⟩ := hK κ hκ
      obtain ⟨L, h1⟩ := kind_sound h
      exact ⟨L, fun _ => h1⟩
    · exact ⟨[], fun h => absurd h hκ⟩
  choose L hL using hK'
  -- the records of all kinds as one finset of triples
  have hnd : ∀ κ < NK, (L κ).Nodup := by
    intro κ hκ
    refine List.Pairwise.imp (fun {a b} h => ?_) (hL κ hκ).2.2.1
    rintro rfl
    rcases h with h | ⟨-, h⟩ <;> omega
  let S : Finset (ℕ × ℕ × ℕ) := (range NK).biUnion (fun κ => (L κ).toFinset)
  have memS : ∀ x, x ∈ S ↔ ∃ κ < NK, x ∈ L κ := by
    intro x
    simp [S, Finset.mem_biUnion, List.mem_toFinset]
  have hdisj : ∀ κ ∈ range NK, ∀ κ' ∈ range NK, κ ≠ κ' → Disjoint (L κ).toFinset (L κ').toFinset := by
    intro κ hκ κ' hκ' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (hL κ (Finset.mem_range.mp hκ)).2.1 x (List.mem_toFinset.mp hx)
    have h2 := (hL κ' (Finset.mem_range.mp hκ')).2.1 x (List.mem_toFinset.mp hx')
    apply hne
    have : x.1 / 224 = κ := by omega
    have : x.1 / 224 = κ' := by omega
    omega
  have hcardS : S.card = NC * R := by
    rw [Finset.card_biUnion hdisj, ← hsum, ← sum_range_list]
    refine Finset.sum_congr rfl (fun κ hκ => ?_)
    rw [List.toFinset_card_of_nodup (hnd κ (Finset.mem_range.mp hκ)), (hL κ (Finset.mem_range.mp hκ)).1]
  -- every record is a slot of a call, hosted at its bin
  have recS : ∀ x ∈ S, x.2.1 < NC ∧ x.2.2 < R ∧ rowAt (ct.get x.2.1).1 x.2.2 = x.1 ∧ x.1 < 224 * NK ∧
      (winOf ct (x.1 / 224)).1 ≤ (ct.get x.2.1).2.1 ∧ (ct.get x.2.1).2.1 ≤ (winOf ct (x.1 / 224)).2 := by
    intro x hx
    obtain ⟨κ, hκ, hxL⟩ := (memS x).mp hx
    obtain ⟨h1, h2, hok⟩ := (hL κ hκ).2.1 x hxL
    have e : x.1 / 224 = κ := by omega
    rw [e]
    exact ⟨hok.1, hok.2.1, hok.2.2.1, by nlinarith, hok.2.2.2.1, hok.2.2.2.2⟩
  -- the projection to (call, slot) is injective on S and onto
  let π : ℕ × ℕ × ℕ → ℕ × ℕ := fun x => (x.2.1, x.2.2)
  have hinjπ : Set.InjOn π S := by
    intro x hx y hy hxy
    simp only [π, Prod.mk.injEq] at hxy
    obtain ⟨-, -, hx3, -⟩ := recS x hx
    obtain ⟨-, -, hy3, -⟩ := recS y hy
    have e1 : x.1 = y.1 := by rw [← hx3, ← hy3, hxy.1, hxy.2]
    exact Prod.ext e1 (Prod.ext hxy.1 hxy.2)
  have himg : S.image π = range NC ×ˢ range R := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨h1, h2, -⟩ := recS x hx
      simp [π, h1, h2]
    · rw [Finset.card_image_of_injOn hinjπ, hcardS, Finset.card_product, Finset.card_range, Finset.card_range]
  have pre : ∀ k < NC, ∀ q < R, (rowAt (ct.get k).1 q, k, q) ∈ S := by
    intro k hk q hq
    have : (k, q) ∈ S.image π := by rw [himg]; simp [hk, hq]
    obtain ⟨x, hx, hxp⟩ := Finset.mem_image.mp this
    simp only [π, Prod.mk.injEq] at hxp
    obtain ⟨-, -, h3, -⟩ := recS x hx
    have : x = (rowAt (ct.get k).1 q, k, q) := by
      rw [← hxp.1, ← hxp.2, h3]
    rw [← this]
    exact hx
  refine ⟨fun k hk q hq => ?_, fun k hk q hq q' hq' he => ?_, fun i hi => ?_⟩
  · obtain ⟨-, -, -, h4, h5, h6⟩ := recS _ (pre k hk q hq)
    exact ⟨h4, h5, h6⟩
  · -- both records lie in the list of the kind of their bin, ordered strictly by (bin, call)
    have hx := pre k hk q hq
    have hy := pre k hk q' hq'
    rw [he] at hx
    obtain ⟨κ, hκ, hxL⟩ := (memS _).mp hx
    obtain ⟨κ', hκ', hyL⟩ := (memS _).mp hy
    have e1 := (hL κ hκ).2.1 _ hxL
    have e2 := (hL κ' hκ').2.1 _ hyL
    have hκκ : κ = κ' := by
      simp only at e1 e2
      omega
    subst hκκ
    by_contra hne
    have hneq : (rowAt (ct.get k).1 q', k, q) ≠ (rowAt (ct.get k).1 q', k, q') := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact hne h.2.2
    rcases pw_or (hL κ hκ).2.2.1 hxL hyL hneq with (h | ⟨-, h⟩) | (h | ⟨-, h⟩) <;> simp at h
  · -- the load of host `i`: the records of its bin
    set κ := i / 224 with hκdef
    have hκ : κ < NK := by omega
    have hb : i % 224 < 224 := Nat.mod_lt _ (by norm_num)
    have hi' : i = 224 * κ + i % 224 := by omega
    have hs := (hL κ hκ).2.2.2 (i % 224) hb
    rw [← hi'] at hs
    have hκ9 : κ % 9 = i / 224 % 9 := by rw [hκdef]
    rw [← hκ9, ← hs]
    congr 1
    -- the bin's records, projected to (call, slot), are exactly the slots hosted at `i`
    have hnd2 : ((L κ).filter (fun x => x.1 = i)).Nodup := (hnd κ hκ).filter _
    have hndπ : (((L κ).filter (fun x => x.1 = i)).map π).Nodup := by
      refine (List.Nodup.map_on (fun x hx y hy hxy => ?_) hnd2)
      exact hinjπ ((memS x).mpr ⟨κ, hκ, (List.mem_filter.mp hx).1⟩) ((memS y).mpr ⟨κ, hκ, (List.mem_filter.mp hy).1⟩) hxy
    have hset : (((L κ).filter (fun x => x.1 = i)).map π).toFinset
        = (range NC ×ˢ range R).filter (fun x => rowAt (ct.get x.1).1 x.2 = i) := by
      ext p
      simp only [List.mem_toFinset, List.mem_map, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range]
      constructor
      · rintro ⟨x, ⟨hxL, hx1⟩, rfl⟩
        obtain ⟨h1, h2, h3, -⟩ := recS x ((memS x).mpr ⟨κ, hκ, hxL⟩)
        exact ⟨⟨h1, h2⟩, by simp only [π]; rw [h3, hx1]⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨(i, p.1, p.2), ⟨?_, rfl⟩, rfl⟩
        have hm := pre p.1 h1 p.2 h2
        rw [h3] at hm
        obtain ⟨κ', hκ', hm'⟩ := (memS _).mp hm
        have e := (hL κ' hκ').2.1 _ hm'
        have : κ' = κ := by simp only at e; omega
        rw [this] at hm'
        exact hm'
    rw [← hset, List.sum_toFinset _ hndπ, List.map_map]
    rfl

end OAI.PowerSaving.XHostT.K

#print axioms OAI.PowerSaving.XHostT.K.kind_sound
#print axioms OAI.PowerSaving.XHostT.K.table_sound
