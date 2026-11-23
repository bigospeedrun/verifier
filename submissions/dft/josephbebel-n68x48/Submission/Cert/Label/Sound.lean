--might be  containing modified Apache-2.0 codes pieces from one or several sources; notices and credits: Credits.lean
import Submission.Cert.Label.Trie
import Submission.Cert.Clifford.LabelMoves

noncomputable section
namespace LabelCheck
open TrieCheck CertData

def word (h P q : Nat) : Nat := (P >>> (h*q)) % 2^h
def cP (h c : Nat) : Nat := c >>> (8 + h)
def XorSet (S : Nat → Prop) : Prop := S 0 ∧ ∀ a b, S a → S b → S (a ^^^ b)
def InSpan (h c x : Nat) : Prop := ∀ S, XorSet S → (∀ q, q < h → S (word h (cP h c) q)) → S x
structure GoodN (h c : Nat) : Prop where
  bnd : cP h c < 2 ^ (h*h)
  ech : ∀ p q, p < h → q < h → word h (cP h c) p ≠ 0 → word h (cP h c) q ≠ 0 →
          (word h (cP h c) p).testBit q = decide (p = q)
  dim : ((List.range h).filter (fun p => word h (cP h c) p != 0)).length = cdim c

theorem InSpan.zero {h c : Nat} : InSpan h c 0 := fun _ hS _ => hS.1
theorem InSpan.xor {h c a b : Nat} (ha : InSpan h c a) (hb : InSpan h c b) : InSpan h c (a ^^^ b) :=
  fun S hS hw => hS.2 _ _ (ha S hS hw) (hb S hS hw)
theorem InSpan.of_word {h c q : Nat} (hq : q < h) : InSpan h c (word h (cP h c) q) := fun _ _ hw => hw q hq

theorem InSpan.mono {h c c' x : Nat} (hc : ∀ q, q < h → InSpan h c' (word h (cP h c) q))
    (hx : InSpan h c x) : InSpan h c' x :=
  hx _ ⟨InSpan.zero, fun _ _ => InSpan.xor⟩ hc

abbrev WIn (h c A : Nat) : Prop := ∀ q, InSpan h c (word h A q)

theorem testBit_word (h P q i : Nat) : (word h P q).testBit i = (decide (i < h) && P.testBit (h*q + i)) := by
  unfold word; rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
theorem word_zero (h q : Nat) : word h 0 q = 0 := by unfold word; rw [Nat.zero_shiftRight, Nat.zero_mod]
theorem word_lt {h X : Nat} (hX : X < 2^h) : word h X 0 = X := by
  unfold word; rw [Nat.mul_zero, Nat.shiftRight_zero, Nat.mod_eq_of_lt hX]
theorem word_xor (h a b q : Nat) : word h (a ^^^ b) q = word h a q ^^^ word h b q :=
  Nat.eq_of_testBit_eq fun i => by
    simp only [testBit_word, Nat.testBit_xor]; cases decide (i < h) <;> simp
theorem word_add {h m X : Nat} (Z q : Nat) (hX : X < 2^(h*m)) :
    word h (2^(h*m) * Z + X) q = if q < m then word h X q else word h Z (q - m) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_word, Nat.testBit_two_pow_mul_add (b_lt := hX)]
  by_cases hi : i < h
  · by_cases hq : q < m
    · have := Nat.mul_le_mul_left h (show q + 1 ≤ m from hq)
      rw [Nat.mul_add, Nat.mul_one] at this
      rw [if_pos (show h * q + i < h * m by omega), if_pos hq, testBit_word]
    · have e : h * q = h * m + h * (q - m) := by
        rw [← Nat.mul_add, Nat.add_sub_of_le (Nat.le_of_not_lt hq)]
      rw [if_neg (show ¬ h * q + i < h * m by omega), if_neg hq, testBit_word, show h * q + i - h * m = h * (q - m) + i by omega]
  · rw [decide_eq_false hi, Bool.false_and]
    split <;> rw [testBit_word, decide_eq_false hi, Bool.false_and]
theorem word_add1 {h X : Nat} (Z q : Nat) (hX : X < 2^h) :
    word h (2^h * Z + X) q = if q < 1 then word h X q else word h Z (q - 1) := by
  have := word_add (h := h) (m := 1) (X := X) Z q (by rwa [Nat.mul_one]); rwa [Nat.mul_one] at this
theorem and_mask (X h : Nat) : X &&& (2^h - 1) = X % 2^h := Nat.and_two_pow_sub_one_eq_mod X h

theorem digK_eq (h P p : Nat) : digK h (2^h-1) P p = word h P p := and_mask _ _
theorem len_filter_succ (f : Nat → Bool) (p : Nat) :
    ((List.range (p+1)).filter f).length = ((List.range p).filter f).length + (if f p then 1 else 0) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : f p <;> simp [List.filter, h]
theorem par_succ (c : Nat) : (!(c % 2 == 1)) = ((c+1) % 2 == 1) := by
  rcases Nat.mod_two_eq_zero_or_one c with e | e
  · simp [e, show (c+1) % 2 = 1 by omega]
  · simp [e, show (c+1) % 2 = 0 by omega]

theorem and_rep {h : Nat} (hh : 0 < h) (Y R : Nat) :
    Y &&& (2^h * R + 1) = 2^h * ((Y >>> h) &&& R) + (Y &&& 1) := by
  have h2 := two_le_pow hh
  have hb : Y &&& 1 < 2^h := by
    rw [Nat.and_one_is_mod]; have := Nat.mod_lt Y (show 2 > 0 by decide); omega
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add (b_lt := (show 1 < 2^h by omega)),
    Nat.testBit_two_pow_mul_add (b_lt := hb)]
  by_cases hj : j < h
  · rw [if_pos hj, if_pos hj, Nat.testBit_and]
  · rw [if_neg hj, if_neg hj, Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_sub_of_le (by omega : h ≤ j)]

theorem word_sparse {h w : Nat} (hh : 0 < h) (hw : w < 2^h) : ∀ K Y q,
    word h ((Y &&& rep h K) * w) q = if q < K ∧ Y.testBit (h*q) = true then w else 0 := by
  intro K; induction K with
  | zero => intro Y q; rw [rep_zero, Nat.and_zero, Nat.zero_mul, word_zero, if_neg (fun hc => Nat.not_lt_zero _ hc.1)]
  | succ K ih =>
    intro Y q
    have hb : (Y &&& 1) * w < 2^h := by
      rw [Nat.and_one_is_mod]; rcases Nat.mod_two_eq_zero_or_one Y with e | e <;> rw [e] <;> omega
    rw [rep_succ, and_rep hh, Nat.add_mul, Nat.mul_assoc, word_add1 _ _ hb]
    cases q with
    | zero =>
      rw [if_pos Nat.zero_lt_one, Nat.mul_zero, Nat.testBit_zero, Nat.and_one_is_mod]
      rcases Nat.mod_two_eq_zero_or_one Y with e | e <;> rw [e]
      · rw [Nat.zero_mul, word_zero]; simp
      · rw [Nat.one_mul, word_lt hw]; simp
    | succ q =>
      rw [if_neg (show ¬ q + 1 < 1 by omega), Nat.add_sub_cancel, ih, Nat.testBit_shiftRight,
        show h * (q+1) = h + h * q by rw [Nat.mul_succ, Nat.add_comm]]
      simp
theorem elimK_sound {h K c : Nat} (hh : 0 < h) : ∀ p A, p ≤ h →
    elimK h (2^h-1) (rep h K) (cP h c) p A = true → WIn h c A
  | 0, A, _, H => fun q => by rw [beq_true H, word_zero]; exact InSpan.zero
  | p+1, A, hp, H => by
    have H' : Nat.rec (motive := fun _ => Bool) (elimK h (2^h-1) (rep h K) (cP h c) p A)
        (fun m _ => forceN (Nat.xor A (Nat.mul (Nat.land (Nat.shiftRight A p) (rep h K)) (Nat.succ m)))
          fun A' => elimK h (2^h-1) (rep h K) (cP h c) p A') (word h (cP h c) p) = true := by
      rw [← digK_eq]; exact H
    have hwl : word h (cP h c) p < 2^h := Nat.mod_lt _ (Nat.two_pow_pos h)
    have hsp : InSpan h c (word h (cP h c) p) := InSpan.of_word (by omega)
    cases hw : word h (cP h c) p with
    | zero => rw [hw] at H'; exact elimK_sound hh p A (by omega) H'
    | succ m =>
      rw [hw] at H' hwl hsp
      have H2 : forceN (A ^^^ (((A >>> p) &&& rep h K) * (m+1)))
          (fun A' => elimK h (2^h-1) (rep h K) (cP h c) p A') = true := H'
      rw [forceN_eq] at H2
      have IH := elimK_sound hh p _ (by omega) H2
      intro q
      have e1 : word h A q = word h (A ^^^ (((A >>> p) &&& rep h K) * (m+1))) q ^^^
          word h (((A >>> p) &&& rep h K) * (m+1)) q := by
        rw [word_xor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [e1, word_sparse hh hwl]
      refine InSpan.xor (IH q) ?_
      split
      · exact hsp
      · exact InSpan.zero

theorem elimT_sound {h K c A : Nat} (hh : 0 < h) (H : elimT h (2^h-1) (rep h K) (cP h c) A = true) :
    WIn h c A := by
  cases A with
  | zero => exact fun q => by rw [word_zero]; exact InSpan.zero
  | succ A => exact elimK_sound hh h _ (Nat.le_refl h) H

theorem goodLoop_sound {h P M dm : Nat} : ∀ p cnt, goodLoop h (2^h-1) P M dm p cnt = true →
    (∀ q, q < p → word h P q ≠ 0 → (word h P q &&& M) = 2^q) ∧
    cnt + ((List.range p).filter (fun q => word h P q != 0)).length = dm
  | 0, cnt, H => ⟨fun q hq => absurd hq (Nat.not_lt_zero q), by have e := beq_true H; subst e; rfl⟩
  | p+1, cnt, H => by
    have H' : Nat.rec (motive := fun _ => Bool) (goodLoop h (2^h-1) P M dm p cnt)
        (fun m _ => guard (Nat.beq (Nat.land (Nat.succ m) M) (Nat.pow 2 p))
          (goodLoop h (2^h-1) P M dm p (Nat.succ cnt))) (word h P p) = true := by
      rw [← digK_eq]; exact H
    rw [len_filter_succ]
    cases hw : word h P p with
    | zero =>
      rw [hw] at H'
      obtain ⟨h1, h2⟩ := goodLoop_sound p cnt H'
      refine ⟨fun q hq hq0 => ?_, ?_⟩
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hq | hq
        · exact h1 q hq hq0
        · rw [hq] at hq0; exact absurd hw hq0
      · split
        · next hc => exact absurd hc (by decide)
        · omega
    | succ m =>
      rw [hw] at H'
      obtain ⟨g1, g2⟩ := guard_true H'
      obtain ⟨h1, h2⟩ := goodLoop_sound p (cnt+1) g2
      refine ⟨fun q hq hq0 => ?_, ?_⟩
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hq | hq
        · exact h1 q hq hq0
        · rw [hq, hw]; exact beq_true g1
      · split
        · omega
        · next hc => exact absurd rfl hc
theorem goodK_sound (h c : Nat) (H : goodK h c = true) : GoodN h c := by
  have H' : guard (Nat.ble (Nat.succ (cP h c)) (Nat.pow 2 (Nat.mul h h)))
      (goodLoop h (2^h-1) (cP h c) (Nat.land (Nat.shiftRight c 8) (2^h-1)) (Nat.land c 255) h 0) = true := by
    unfold goodK at H; rw [forceN_eq, forceN_eq] at H; exact H
  obtain ⟨g1, g2⟩ := guard_true H'
  obtain ⟨l1, l2⟩ := goodLoop_sound h 0 g2
  refine ⟨ble_true g1, fun p q hp hq hp0 hq0 => ?_, by rw [Nat.zero_add] at l2; exact l2⟩
  have mq := congrArg (fun x => Nat.testBit x q) (l1 q hq hq0)
  have mp := congrArg (fun x => Nat.testBit x q) (l1 p hp hp0)
  simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_eq_true] at mq
  simp only [Nat.testBit_and, Nat.testBit_two_pow] at mp
  rw [mq.2, Bool.and_true] at mp
  exact mp
theorem tabK_good (h : Nat) (t : Trie) (H : checkTable h t = true) (key : Nat) : GoodN h (t.get key) :=
  match t, H, key with
  | .leaf v, H, _ => goodK_sound h v H
  | .node l r, H, key => by
    have g := guard_true H
    show GoodN h (if key % 2 = 0 then l.get (key / 2) else r.get (key / 2))
    split
    · exact tabK_good h l g.1 _
    · exact tabK_good h r g.2 _
theorem tabK_node (h : Nat) (l r : TrieCheck.Trie) (hl : checkTable h l = true) (hr : checkTable h r = true) :
    checkTable h (.node l r) = true := by
  show guard (checkTable h l) (checkTable h r) = true
  rw [hl, hr]; rfl

def vOut (f : Nat) (S : Trie) (r : Nat) : Trie := if S.get r = f then S else S.set r f
def vRanks (p : Par) (f : Nat) (S : Trie) (r : Nat) : List Nat :=
  if S.get r = f then [] else [cdim (p.tab.get f) - cdim (p.tab.get (S.get r))]
def vOk (p : Par) (f : Nat) (S : Trie) (r : Nat) : Prop :=
  r < p.n ∧ (S.get r ≠ f → cdim (p.tab.get (S.get r)) < cdim (p.tab.get f))
def vCl (p : Par) (f : Nat) (S : Trie) (r : Nat) : List Nat := if S.get r = f then [] else [p.tab.get (S.get r)]
def rOut (f : Nat) : Trie → List Nat → Trie
  | S, [] => S
  | S, a :: l => rOut f (vOut f S a) l
def rRanks (p : Par) (f : Nat) : Trie → List Nat → List Nat
  | _, [] => []
  | S, a :: l => vRanks p f S a ++ rRanks p f (vOut f S a) l
def rOk (p : Par) (f : Nat) : Trie → List Nat → Prop
  | _, [] => True
  | S, a :: l => vOk p f S a ∧ rOk p f (vOut f S a) l
def rCl (p : Par) (f : Nat) : Trie → List Nat → List Nat
  | _, [] => []
  | S, a :: l => vCl p f S a ++ rCl p f (vOut f S a) l
def gOut (S : Trie) (g : Gate) : Trie := rOut g.frame S g.regs
def gRanks (p : Par) (S : Trie) (g : Gate) : List Nat := rRanks p g.frame S g.regs
def gOk (p : Par) (S : Trie) (g : Gate) : Prop :=
  rOk p g.frame S g.regs ∧ ∀ ca ∈ rCl p g.frame S g.regs, ∀ q, q < p.h → InSpan p.h (p.tab.get g.frame) (word p.h (cP p.h ca) q)

theorem rOk_lt (p : Par) (f : Nat) (l : List Nat) (S : Trie) (h : rOk p f S l) : ∀ r ∈ l, r < p.n := by
  induction l generalizing S with
  | nil => intro r hr; simp at hr
  | cons a l ih =>
    intro r hr
    rcases List.mem_cons.1 hr with hr | hr
    · rw [hr]; exact h.1.1
    · exact ih _ h.2 r hr
theorem vOut_wf {d : Nat} (f r : Nat) (S : Trie) (hS : S.wf d) : (vOut f S r).wf d := by
  unfold vOut; split
  · exact hS
  · exact Trie.wf_set d S hS r f
theorem rOut_wf {d : Nat} (f : Nat) (l : List Nat) (S : Trie) (hS : S.wf d) : (rOut f S l).wf d := by
  induction l generalizing S with
  | nil => exact hS
  | cons a l ih => exact ih _ (vOut_wf f a S hS)
theorem vOut_get {d : Nat} (f r r' : Nat) (S : Trie) (hS : S.wf d) (hr : r < 2^d) (hr' : r' < 2^d) :
    (vOut f S r).get r' = if r' = r then f else S.get r' := by
  unfold vOut; split
  · next he =>
    by_cases e : r' = r
    · rw [if_pos e, e, he]
    · rw [if_neg e]
  · exact Trie.get_set d S hS r r' f hr hr'
theorem rOut_get_nm {d : Nat} (f : Nat) (l : List Nat) (S : Trie) (hS : S.wf d) (r' : Nat)
    (hr' : r' < 2^d) (hl : ∀ r ∈ l, r < 2^d) (hn : r' ∉ l) : (rOut f S l).get r' = S.get r' := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    have ha : a < 2^d := hl a (List.mem_cons.2 (Or.inl rfl))
    show (rOut f (vOut f S a) l).get r' = _
    rw [ih _ (vOut_wf f a S hS) (fun r h => hl r (List.mem_cons.2 (Or.inr h)))
        (fun h => hn (List.mem_cons.2 (Or.inr h))), vOut_get f a r' S hS ha hr',
      if_neg (fun h => hn (List.mem_cons.2 (Or.inl h)))]
theorem rOut_get {d : Nat} (f : Nat) (l : List Nat) (S : Trie) (hS : S.wf d) (hl : ∀ r ∈ l, r < 2^d) :
    ∀ r ∈ l, (rOut f S l).get r = f := by
  induction l generalizing S with
  | nil => intro r hr; simp at hr
  | cons a l ih =>
    intro r hr
    have ha : a < 2^d := hl a (List.mem_cons.2 (Or.inl rfl))
    have hl' : ∀ r ∈ l, r < 2^d := fun r h => hl r (List.mem_cons.2 (Or.inr h))
    show (rOut f (vOut f S a) l).get r = f
    by_cases hm : r ∈ l
    · exact ih _ (vOut_wf f a S hS) hl' r hm
    · have e : r = a := by
        rcases List.mem_cons.1 hr with h | h
        · exact h
        · exact absurd h hm
      rw [e] at hm ⊢
      rw [rOut_get_nm f l _ (vOut_wf f a S hS) a ha hl' hm, vOut_get f a a S hS ha ha, if_pos rfl]
theorem rCl_tab (p : Par) (f : Nat) (l : List Nat) (S : Trie) : ∀ ca ∈ rCl p f S l, ∃ a, ca = p.tab.get a := by
  induction l generalizing S with
  | nil => intro ca h; simp [rCl] at h
  | cons a l ih =>
    intro ca h
    simp only [rCl, List.mem_append] at h
    rcases h with h | h
    · unfold vCl at h; split at h
      · simp at h
      · exact ⟨_, List.mem_singleton.1 h⟩
    · exact ih _ ca h
theorem adds_regs (g : Gate) (x : Nat × Nat × Co) (hx : x ∈ g.adds) : x.1 ∈ g.regs ∧ x.2.1 ∈ g.regs := by
  cases g with
  | out f s ts ex =>
    simp only [Gate.adds, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨List.mem_cons.2 (Or.inr (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨y, hy, rfl⟩)))),
      List.mem_cons.2 (Or.inl rfl)⟩
  | inn f t ss =>
    simp only [Gate.adds, List.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨List.mem_cons.2 (Or.inl rfl), List.mem_cons.2 (Or.inr (List.mem_map.2 ⟨y, hy, rfl⟩))⟩
theorem memK_sound (r : Nat) (gl : List Nat) (H : memK r gl = true) : r ∈ gl :=
  match gl, H with
  | [], H => absurd H Bool.false_ne_true
  | x :: xs, H => by
    rcases brec_true H with ⟨_, h2⟩ | ⟨h1, _⟩
    · exact List.mem_cons.2 (Or.inr (memK_sound r xs h2))
    · exact List.mem_cons.2 (Or.inl (beq_true h1).symm)
theorem wfK_sound (t : Trie) (d : Nat) (H : wfK t d = true) : t.wf d :=
  match t, d, H with
  | .leaf _, d, H => by have e : d = 0 := beq_true H; subst e; exact trivial
  | .node _ _, 0, H => absurd H Bool.false_ne_true
  | .node l r, d + 1, H => ⟨wfK_sound l d (guard_true H).1, wfK_sound r d (guard_true H).2⟩

theorem win_push {h c A X : Nat} (hX : X < 2^(h*h)) (H : WIn h c (A <<< (h*h) + X)) :
    WIn h c A ∧ ∀ q, q < h → InSpan h c (word h X q) := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm A] at H
  refine ⟨fun q => ?_, fun q hq => ?_⟩
  · have := H (h + q); rwa [word_add _ _ hX, if_neg (show ¬ h + q < h by omega), Nat.add_sub_cancel_left] at this
  · have := H q; rwa [word_add _ _ hX, if_pos hq] at this

def Feeds (h A A' : Nat) (cl : List Nat) : Prop :=
  ∀ c, WIn h c A' → WIn h c A ∧ ∀ ca ∈ cl, ∀ q, q < h → InSpan h c (word h (cP h ca) q)
theorem Feeds.refl (h A : Nat) : Feeds h A A [] := fun _ hA => ⟨hA, fun _ hc => by simp at hc⟩
theorem Feeds.trans {h A A' A'' : Nat} {c1 c2 : List Nat} (a : Feeds h A A' c1) (b : Feeds h A' A'' c2) :
    Feeds h A A'' (c1 ++ c2) := fun c hA => by
  obtain ⟨h2, r2⟩ := b c hA
  obtain ⟨h1, r1⟩ := a c h2
  exact ⟨h1, fun ca hc => (List.mem_append.1 hc).elim (r1 ca) (r2 ca)⟩
theorem Feeds.step {h A ca : Nat} (hX : cP h ca < 2^(h*h)) : Feeds h A (A <<< (h*h) + cP h ca) [ca] :=
  fun c hA => by
    obtain ⟨h1, h2⟩ := win_push hX hA
    exact ⟨h1, fun ca' hc => by rw [List.mem_singleton.1 hc]; exact h2⟩
theorem loopN_cons (n : Nat) (tab : Trie) (hh sh f db r : Nat) (l : List Nat) (S : Trie) (A : Nat)
    (rs : List Nat) (k : Trie → Nat → List Nat → Bool) :
    loopN n tab hh sh f db (r :: l) S A rs k =
      visitK n tab hh sh f db r S A rs fun S1 A1 rs1 => loopN n tab hh sh f db l S1 A1 rs1 k := rfl

theorem loopN_sound (p : Par) (hT : checkTable p.h p.tab = true) (f : Nat) :
    ∀ (l : List Nat) (S : Trie) (A : Nat) (rs : List Nat) (k : Trie → Nat → List Nat → Bool),
    loopN p.n p.tab (p.h*p.h) (8+p.h) f (cdim (p.tab.get f)) l S A rs k = true →
    ∃ A' rs', k (rOut f S l) A' rs' = true ∧ rs = rRanks p f S l ++ rs' ∧ rOk p f S l ∧
      Feeds p.h A A' (rCl p f S l)
  | [], S, A, rs, k, H => ⟨A, rs, H, rfl, trivial, Feeds.refl _ _⟩
  | r :: l, S, A, rs, k, H => by
    rw [loopN_cons] at H
    obtain ⟨hr, H⟩ := guard_true H
    have H := Trie.getK_true _ _ _ H
    cases hb : Nat.beq (S.get r) f with
    | true =>
      have e := beq_true hb
      rw [hb] at H
      obtain ⟨A', rs', h1, h2, h3, h4⟩ := loopN_sound p hT f l S A rs k H
      refine ⟨A', rs', ?_, ?_, ?_, ?_⟩ <;>
        simp only [rOut, rRanks, rOk, rCl, vRanks, vCl, vOut, if_pos e, List.nil_append]
      · exact h1
      · exact h2
      · exact ⟨⟨ble_true hr, (absurd e ·)⟩, h3⟩
      · exact h4
    | false =>
      have e : S.get r ≠ f := Nat.ne_of_beq_eq_false hb
      rw [hb] at H
      have H := Trie.getK_true _ _ _ H
      rw [forceN_eq] at H
      obtain ⟨hd, H⟩ := guard_true H
      cases rs with
      | nil => exact absurd H Bool.false_ne_true
      | cons r0 rs =>
        obtain ⟨h0, H⟩ := guard_true H
        rw [forceN_eq] at H
        obtain ⟨A', rs', h1, h2, h3, h4⟩ := loopN_sound p hT f l _ _ rs k H
        refine ⟨A', rs', ?_, ?_, ?_, ?_⟩ <;>
          simp only [rOut, rRanks, rOk, rCl, vRanks, vCl, vOut, if_neg e, List.singleton_append]
        · exact h1
        · rw [h2, beq_true h0]; rfl
        · exact ⟨⟨ble_true hr, fun _ => ble_true hd⟩, h3⟩
        · exact (Feeds.step (tabK_good p.h p.tab hT (S.get r)).bnd).trans h4
theorem loopN_append (n : Nat) (tab : Trie) (hh sh f db : Nat) (l₂ : List Nat) :
    ∀ (l₁ : List Nat) (S : Trie) (A : Nat) (rs : List Nat) (k : Trie → Nat → List Nat → Bool),
    loopN n tab hh sh f db (l₁ ++ l₂) S A rs k =
      loopN n tab hh sh f db l₁ S A rs fun S A rs => loopN n tab hh sh f db l₂ S A rs k
  | [], _, _, _, _ => rfl
  | r :: l₁, S, A, rs, k => by
    simp only [List.cons_append, loopN_cons, loopN_append n tab hh sh f db l₂ l₁]
theorem loopP_eq (n : Nat) (tab : Trie) (hh sh f db : Nat) :
    ∀ (ts : List (Nat × Co)) (S : Trie) (A : Nat) (rs : List Nat) (k : Trie → Nat → List Nat → Bool),
    loopP n tab hh sh f db ts S A rs k = loopN n tab hh sh f db (ts.map Prod.fst) S A rs k
  | [], _, _, _, _ => rfl
  | x :: ts, S, A, rs, k => by
    show visitK n tab hh sh f db x.1 S A rs (fun S1 A1 rs1 => loopP n tab hh sh f db ts S1 A1 rs1 k) = _
    simp only [loopP_eq n tab hh sh f db ts, List.map_cons, loopN_cons]

theorem gate_sound (p : Par) (hT : checkTable p.h p.tab = true) {K : Nat} (hh : 0 < p.h) (g : Gate)
    (S : Trie) (rs : List Nat) (k : Trie → List Nat → Bool)
    (H : checkGate p (2^p.h-1) (p.h*p.h) (8+p.h) (rep p.h K) g S rs k = true) :
    gOk p S g ∧ ∃ rs', rs = gRanks p S g ++ rs' ∧ k (gOut S g) rs' = true := by
  have L : ∀ f, loopN p.n p.tab (p.h*p.h) (8+p.h) f (Nat.land (p.tab.get f) 255) g.regs S 0 rs
      (fun S3 A3 rs3 => guard (elimT p.h (2^p.h-1) (rep p.h K) (Nat.shiftRight (p.tab.get f) (8+p.h)) A3)
        (k S3 rs3)) = true → f = g.frame →
      gOk p S g ∧ ∃ rs', rs = gRanks p S g ++ rs' ∧ k (gOut S g) rs' = true := by
    rintro f H rfl
    obtain ⟨A', rs', h1, h2, h3, h4⟩ := loopN_sound p hT _ _ _ _ _ _ H
    obtain ⟨he, hk⟩ := guard_true h1
    exact ⟨⟨h3, (h4 _ (elimT_sound (c := p.tab.get g.frame) hh he)).2⟩, rs', h2, hk⟩
  cases g <;> have H := Trie.getK_true _ _ _ H <;> simp only [forceN_eq, loopP_eq] at H <;>
    exact L _ (by simpa only [Gate.regs, Gate.frame, loopN_cons, loopN_append] using H) rfl

def oddW (h u : Nat) : Prop := ((List.range h).filter (fun q => u.testBit q)).length % 2 = 1
def orthW (h u y : Nat) : Prop := ((List.range h).filter (fun q => u.testBit q && y.testBit q)).length % 2 = 0
structure PortN (p : Par) (v : Nat) (S0 SA SF : Trie) (t u : Nat) : Prop where
  lt : u < 2 ^ p.h
  odd : oddW p.h u
  gap : ∃ q, q < p.h ∧ u.testBit q = false
  x0d : cdim (p.tab.get (S0.get t)) = 1
  x0m : InSpan p.h (p.tab.get (S0.get t)) u
  y0 : S0.get (v + t) = 0
  yA : SA.get (v + t) = 0
  xF : cdim (p.tab.get (SF.get t)) = p.h
  yFd : cdim (p.tab.get (SF.get (v + t))) + 1 = p.h
  yFo : ∀ q, q < p.h → orthW p.h u (word p.h (cP p.h (p.tab.get (SF.get (v + t)))) q)
structure EndsN (p : Par) (v : Nat) (ports rets gl el : List Nat) (S0 SA SF : Trie) : Prop where
  hh : 0 < p.h
  hn : p.n ≤ 2 ^ p.d
  hv : 2 * v ≤ p.n
  w0 : S0.wf p.d
  z0 : cdim (p.tab.get 0) = 0
  len : ports.length = v
  port : ∀ t, t < v → PortN p v S0 SA SF t (ports.getD t 0)
  ret : ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))
  slot : ∀ q, q < p.n - 2 * v →
    (S0.get (2 * v + q) = 0 ∨ 2 * v + q ∈ gl) ∧
    (memK (2 * v + q) el = false → cdim (p.tab.get (SF.get (2 * v + q))) = p.h) ∧
    (memK (2 * v + q) el = true → ∀ q', q' < p.h →
      InSpan p.h (p.tab.get (SF.get (2 * v + q))) (word p.h (cP p.h (p.tab.get (S0.get (2 * v + q)))) q'))

theorem parsK_bit (O Y j : Nat) : ∀ n, (parsK n O Y).testBit j =
    (((List.range n).filter (fun i => ((Y >>> i) &&& O).testBit j)).length % 2 == 1)
  | 0 => by show (0:Nat).testBit j = _; simp
  | n+1 => by
    show (parsK n O Y ^^^ ((Y >>> n) &&& O)).testBit j = _
    rw [Nat.testBit_xor, parsK_bit O Y j n, len_filter_succ]
    cases ((Y >>> n) &&& O).testBit j
    · rw [Bool.xor_false, if_neg Bool.false_ne_true, Nat.add_zero]
    · rw [Bool.xor_true, if_pos rfl, par_succ]
theorem oddW_of {h u : Nat} (H : parsK h 1 u = 1) : oddW h u := by
  have e := parsK_bit 1 u 0 h
  rw [H] at e
  have hf : (fun i => ((u >>> i) &&& 1).testBit 0) = (fun q => u.testBit q) := by
    funext i
    show ((u >>> i) &&& 1).testBit 0 = u.testBit i
    rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.add_zero,
      show (1:Nat).testBit 0 = true by decide, Bool.and_true]
  rw [hf] at e
  exact beq_iff_eq.1 (e.symm.trans (show (1:Nat).testBit 0 = true by decide))
theorem gap_of {h u : Nat} (hu : u + 1 < 2^h) : ∃ q, q < h ∧ u.testBit q = false :=
  Classical.byContradiction fun hc => by
    have : u = 2^h - 1 := Nat.eq_of_testBit_eq fun i => by
      rw [Nat.testBit_two_pow_sub_one]
      by_cases hi : i < h
      · rw [decide_eq_true hi]
        cases hb : u.testBit i with
        | false => exact absurd ⟨i, hi, hb⟩ hc
        | true => rfl
      · rw [decide_eq_false hi]
        exact Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hi)))
    omega
theorem orthW_of {h u Y : Nat} (hh : 0 < h) (hu : u < 2^h)
    (H : parsK h (rep h h) (Y &&& (u * rep h h)) = 0) (q : Nat) (hq : q < h) :
    orthW h u (word h Y q) := by
  have e := parsK_bit (rep h h) (Y &&& (u * rep h h)) (h*q) h
  rw [H, Nat.zero_testBit] at e
  have r1 := rep_bit h hh h q 0 hh
  rw [Nat.add_zero] at r1
  have hf : (List.range h).filter (fun i => (((Y &&& (u * rep h h)) >>> i) &&& rep h h).testBit (h*q)) =
      (List.range h).filter (fun i => u.testBit i && (word h Y q).testBit i) :=
    List.filter_congr fun i hi => by
      have hi : i < h := List.mem_range.1 hi
      show (((Y &&& (u * rep h h)) >>> i) &&& rep h h).testBit (h*q) = (u.testBit i && (word h Y q).testBit i)
      rw [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_and, Nat.add_comm i (h*q),
        mul_rep_bit h hh u hu h q i hi, r1, testBit_word, decide_eq_true hi, decide_eq_true hq]
      cases Y.testBit (h*q+i) <;> cases u.testBit i <;> rfl
  rw [hf] at e
  show ((List.range h).filter (fun i => u.testBit i && (word h Y q).testBit i)).length % 2 = 0
  rcases Nat.mod_two_eq_zero_or_one
    ((List.range h).filter (fun i => u.testBit i && (word h Y q).testBit i)).length with h0 | h1
  · exact h0
  · rw [h1] at e; exact absurd e (by decide)
set_option hygiene false in

macro "gk" : tactic => `(tactic| ((replace H := (Trie.getK_true _ _ _ H)) <;> try
  simp only [guard_eq_true, Nat.beq_eq, Nat.ble_eq, forceN_eq] at H))
theorem portsK_sound (p : Par) (hh : 0 < p.h) (v : Nat) (S0 SA SF : Trie) :
    ∀ (l : List Nat) (t : Nat), portsK p (2^p.h-1) (rep p.h p.h) (8+p.h) v S0 SA SF l t = true →
      t + l.length = v ∧ ∀ i, i < l.length → PortN p v S0 SA SF (t+i) (l.getD i 0)
  | [], t, H => ⟨beq_true H, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | u :: l, t, H => by
    simp only [portsK, guard_eq_true, Nat.beq_eq, Nat.ble_eq] at H
    obtain ⟨g1, g2, H⟩ := H; gk; gk
    obtain ⟨g3, g4, H⟩ := H; gk
    obtain ⟨g5, H⟩ := H; gk
    obtain ⟨g6, H⟩ := H; gk; gk
    obtain ⟨g7, H⟩ := H; gk; gk
    obtain ⟨g8, g9, H⟩ := H
    obtain ⟨ih1, ih2⟩ := portsK_sound p hh v S0 SA SF l (t+1) H
    have hu : u < 2^p.h := by omega
    have P0 : PortN p v S0 SA SF t u :=
      { lt := hu
        odd := oddW_of g2
        gap := gap_of (by omega)
        x0d := g3
        x0m := by
          have g4' : elimT p.h (2^p.h-1) (rep p.h 1) (cP p.h (p.tab.get (S0.get t))) u = true := by
            rw [rep_one]; exact g4
          have := elimT_sound hh g4' 0
          rwa [word_lt hu] at this
        y0 := g5
        yA := g6
        xF := g7
        yFd := g8
        yFo := fun q hq => orthW_of (Y := cP p.h (p.tab.get (SF.get (v + t)))) hh hu g9 q hq }
    refine ⟨by rw [List.length_cons]; omega, fun i hi => ?_⟩
    cases i with
    | zero => simpa using P0
    | succ i =>
      have := ih2 i (by rw [List.length_cons] at hi; omega)
      rw [show t + (i+1) = t + 1 + i by omega]
      simpa using this
theorem slotsKX_sound (p : Par) (hh : 0 < p.h) (v2 : Nat) (gl el : List Nat) (S0 SF : Trie) :
    ∀ n, slotsKX p (2^p.h-1) (rep p.h p.h) (8+p.h) v2 gl el S0 SF n = true → ∀ q, q < n →
    (S0.get (v2 + q) = 0 ∨ v2 + q ∈ gl) ∧
    (memK (v2 + q) el = false → cdim (p.tab.get (SF.get (v2 + q))) = p.h) ∧
    (memK (v2 + q) el = true → ∀ q', q' < p.h →
      InSpan p.h (p.tab.get (SF.get (v2 + q))) (word p.h (cP p.h (p.tab.get (S0.get (v2 + q)))) q'))
  | 0, _, q, hq => absurd hq (Nat.not_lt_zero _)
  | n+1, H, q, hq => by
    have H := Trie.getK_true _ _ _ H
    obtain ⟨g1, H⟩ := guard_true H
    have H := Trie.getK_true _ _ _ H
    have H := Trie.getK_true _ _ _ H
    have c1 : S0.get (v2 + n) = 0 ∨ v2 + n ∈ gl := by
      rcases brec_true g1 with ⟨_, h⟩ | ⟨h, _⟩
      · exact .inr (memK_sound _ _ h)
      · exact .inl (beq_true h)
    have ih : slotsKX p (2^p.h-1) (rep p.h p.h) (8+p.h) v2 gl el S0 SF n = true ∧
        ((memK (v2 + n) el = false → cdim (p.tab.get (SF.get (v2 + n))) = p.h) ∧
        (memK (v2 + n) el = true → ∀ q', q' < p.h → InSpan p.h (p.tab.get (SF.get (v2 + n)))
          (word p.h (cP p.h (p.tab.get (S0.get (v2 + n)))) q'))) := by
      rcases brec_true H with ⟨hm, H⟩ | ⟨hm, H⟩
      · obtain ⟨g2, H⟩ := guard_true H
        exact ⟨H, fun _ => beq_true g2, fun h => absurd (hm.symm.trans h) Bool.false_ne_true⟩
      · have H := Trie.getK_true _ _ _ H
        obtain ⟨g2, H⟩ := guard_true H
        exact ⟨H, fun h => absurd (h.symm.trans hm) Bool.false_ne_true, fun _ q' _ => elimT_sound hh g2 q'⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hq) with hq | hq
    · exact slotsKX_sound p hh v2 gl el S0 SF n ih.1 q hq
    · rw [hq]; exact ⟨c1, ih.2⟩
theorem retsK_sound (p : Par) (SA : Trie) :
    ∀ rets, retsK p SA rets = true → ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))
  | [], _, r, hr => by simp at hr
  | x :: xs, H, r, hr => by
    have H := Trie.getK_true _ _ _ H
    have H := Trie.getK_true _ _ _ H
    obtain ⟨g, ih⟩ := guard_true H
    rcases List.mem_cons.1 hr with hr | hr
    · rw [hr]; exact ble_true g
    · exact retsK_sound p SA xs ih r hr
theorem checkEnds_sound {p : Par} {v : Nat} {ports rets gl el : List Nat} {S0 SA SF : Trie}
    (hT : checkTable p.h p.tab = true) (H : checkEnds p v ports rets gl el S0 SA SF = true) :
    EndsN p v ports rets gl el S0 SA SF := by
  unfold checkEnds at H
  obtain ⟨g1, H⟩ := guard_true H
  obtain ⟨g2, H⟩ := guard_true H
  obtain ⟨g3, H⟩ := guard_true H
  obtain ⟨g4, H⟩ := guard_true H
  have H := Trie.getK_true _ _ _ H
  obtain ⟨g5, H⟩ := guard_true H
  rw [forceN_eq, forceN_eq] at H
  obtain ⟨g6, H⟩ := guard_true H
  have hh : 0 < p.h := ble_true g1
  have eO : Nat.div (Nat.sub (Nat.pow 2 (Nat.mul p.h p.h)) 1) (Nat.sub (Nat.pow 2 p.h) 1) = rep p.h p.h :=
    rep_of hh (beq_true g6)
  rw [eO] at H
  obtain ⟨g7, H⟩ := guard_true H
  obtain ⟨g8, g9⟩ := guard_true H
  obtain ⟨len, port⟩ := portsK_sound p hh v S0 SA SF ports 0 g7
  exact { hh := hh, hn := ble_true g3, hv := ble_true g4, w0 := wfK_sound _ _ g2, z0 := beq_true g5,
          len := by rw [Nat.zero_add] at len; exact len,
          port := fun t ht => by
            have := port t (by omega)
            rwa [Nat.zero_add] at this
          ret := retsK_sound p SA rets g9,
          slot := fun q hq => slotsKX_sound p hh (2 * v) gl el S0 SF _ g8 q hq }
end LabelCheck
end

namespace TrieCheck
open OAI.PowerSaving.RAM
open OAI.PowerSaving.Binary
inductive Micro where
  | dir (r z : Nat)
  | shift (r z : Nat)
  | add (t s : Nat) (c : Coef)
  | copy (s d : Nat)
  | erase (d : Nat)
  | expect (r e : Nat)
noncomputable def Coef.val (c : Coef) : ℚ :=
  (if c.neg then -(c.num : ℚ) else (c.num : ℚ)) / (c.den : ℚ)
section
variable {ρ : Type*} [Fintype ρ] [DecidableEq ρ]
def addMat (a b : ρ) (c : ℚ) : Matrix ρ ρ ℚ :=
  fun i j => (if i = j then 1 else 0) + (if i = a ∧ j = b then c else 0)
theorem actPoint_addMat (a b : ρ) (c : ℚ) (x : ρ → ℂ) (r : ρ) :
    actPoint (addMat a b c) x r = if r = a then x a + (c:ℂ) * x b else x r := by
  simp only [actPoint, addMat, Rat.cast_add, apply_ite (Rat.cast : ℚ → ℂ), Rat.cast_one,
    Rat.cast_zero]
  by_cases h : r = a
  · subst h; simp [add_mul, Finset.sum_add_distrib, ite_mul]
  · simp [h, add_mul, Finset.sum_add_distrib, ite_mul]
end
section
variable {ρ : Type} [Fintype ρ] [DecidableEq ρ]
noncomputable def matP (unemb : Nat → ρ) : List Micro → Matrix ρ ρ ℚ
  | [] => 1
  | .dir _ _ :: ms => matP unemb ms
  | .shift _ _ :: ms => matP unemb ms
  | .add t s c :: ms => matP unemb ms * addMat (unemb t) (unemb s) c.val
  | .copy _ _ :: ms => matP unemb ms
  | .erase _ :: ms => matP unemb ms
  | .expect _ _ :: ms => matP unemb ms
theorem actPoint_mul (A B : Matrix ρ ρ ℚ) : actPoint (A * B) = actPoint A ∘ actPoint B := by
  funext x r
  simp only [actPoint, Function.comp_apply, Matrix.mul_apply]
  push_cast
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm
theorem actPoint_one' : actPoint (1 : Matrix ρ ρ ℚ) = id := by
  funext x r
  simp [actPoint, Matrix.one_apply, apply_ite (Rat.cast : ℚ → ℂ)]
end
def Coef.negate (c : Coef) : Coef := ⟨!c.neg, c.num, c.den⟩
def swapNeg : Micro → Micro
  | .add t s c => .add s t c.negate
  | .dir r z => .dir r z
  | .shift r z => .shift r z
  | .copy s d => .copy s d
  | .erase d => .erase d
  | .expect r e => .expect r e
end TrieCheck

namespace TrieCheck

theorem getK_true : ∀ (t : Trie) (key : Nat) (k : Nat → Bool), t.getK key k = true → k (t.get key) = true :=
  Trie.getK_true

theorem beq_false {a b : Nat} (h : Nat.beq a b = false) : a ≠ b := by
  rintro rfl
  induction a with
  | zero => exact absurd h (by decide)
  | succ n ih => exact ih h

theorem raw_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem raw_xor (a b : Nat) : Nat.xor a b = a ^^^ b := rfl
theorem raw_shr (a b : Nat) : Nat.shiftRight a b = a >>> b := rfl
theorem raw_shl (a b : Nat) : Nat.shiftLeft a b = a <<< b := rfl
theorem raw_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem raw_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem raw_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem raw_pow (a b : Nat) : Nat.pow a b = a ^ b := rfl
theorem raw_div (a b : Nat) : Nat.div a b = a / b := rfl

end TrieCheck

namespace LabelCheck
open TrieCheck CertData OAI.PowerSaving OAI.PowerSaving.Binary OAI.PowerSaving.GenMove Finset
open OAI.PowerSaving.RAM OAI.PowerSaving.RankCost Matrix
noncomputable section

section
variable {α : Type} [Fintype α] [DecidableEq α]

def Ech (piv : Finset α) (b : α → Space α) : Prop :=
  ∀ p ∈ piv, ∀ q ∈ piv, b p q = if p = q then 1 else 0

def cfun (piv : Finset α) (b : α → Space α) (x : Space α) : Space α :=
  x + ∑ p ∈ piv, x p • fun q => if q ∈ piv then 0 else b p q

theorem cfun_cfun (piv : Finset α) (b : α → Space α) : Function.LeftInverse (cfun piv b) (cfun piv b) := by
  intro x
  have h : ∀ p ∈ piv, cfun piv b x p = x p := fun p hp => by simp [cfun, Finset.sum_apply, hp]
  have e : (∑ p ∈ piv, cfun piv b x p • fun q => if q ∈ piv then (0 : F) else b p q) =
      ∑ p ∈ piv, x p • fun q => if q ∈ piv then (0 : F) else b p q :=
    Finset.sum_congr rfl fun p hp => by rw [h p hp]
  show cfun piv b x + _ = x
  rw [e]
  show x + _ + _ = x
  rw [add_assoc, binary_cancel, add_zero]

theorem cfun_add (piv : Finset α) (b : α → Space α) (x y : Space α) :
    cfun piv b (x + y) = cfun piv b x + cfun piv b y := by
  simp only [cfun, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  abel

def canon (piv : Finset α) (b : α → Space α) : APerm α :=
  ⟨⟨cfun piv b, cfun piv b, cfun_cfun piv b, cfun_cfun piv b⟩, cfun_add piv b⟩

theorem mem_zero (U : SubspaceLabel α) : U.Mem 0 := by
  intro k _
  simp only [APerm.map_zero', Pi.zero_apply]

theorem mem_add {U : SubspaceLabel α} {x y : Space α} (hx : U.Mem x) (hy : U.Mem y) : U.Mem (x + y) := by
  intro k hk
  rw [U.G.add, Pi.add_apply, hx k hk, hy k hk, add_zero]

theorem f01 : ∀ a : F, a = 0 ∨ a = 1 := by decide

theorem f2 : ∀ a : F, a + a = 0 := by decide

theorem mem_smul {U : SubspaceLabel α} (a : F) {x : Space α} (hx : U.Mem x) : U.Mem (a • x) := by
  rcases f01 a with rfl | rfl
  · rw [zero_smul]; exact mem_zero U
  · rwa [one_smul]

theorem mem_sum {U : SubspaceLabel α} {ι : Type} (s : Finset ι) (g : ι → Space α) (h : ∀ i ∈ s, U.Mem (g i)) :
    U.Mem (∑ i ∈ s, g i) :=
  Finset.sum_induction _ _ (fun _ _ => mem_add) (mem_zero U) h

end

def bF (b : Bool) : F := if b then 1 else 0

theorem bF_xor (a b : Bool) : bF (a ^^ b) = bF a + bF b := by cases a <;> cases b <;> decide

theorem bF_and (a b : Bool) : bF (a && b) = bF a * bF b := by cases a <;> cases b <;> decide

theorem bF_cancel (a c r : Bool) : bF a = bF (a ^^ (c && r)) + bF c * bF r := by
  cases a <;> cases c <;> cases r <;> decide

theorem bF_eq_zero {a : Bool} : bF a = 0 ↔ a = false := by cases a <;> decide

def dv (h P p : Nat) : Space (Fin h) := fun q => bF (P.testBit (h * p + q.val))

def bas (h P : Nat) (p : Fin h) : Space (Fin h) := dv h P p.val

def pivs (h P : Nat) : Finset (Fin h) := univ.filter fun p => bas h P p ≠ 0

section
variable {h c : Nat}

structure GoodCode (h c : Nat) : Prop where
  ech : Ech (pivs h (cP h c)) (bas h (cP h c))
  dim : (pivs h (cP h c)).card = cdim c
  bnd : cP h c < 2 ^ (h * h)

open Classical in
noncomputable def labelOf (h c : Nat) : SubspaceLabel (Fin h) :=
  if GoodCode h c then ⟨canon (pivs h (cP h c)) (bas h (cP h c)), pivs h (cP h c)⟩ else ⟨apId _, ∅⟩

theorem lab_def (hg : GoodCode h c) :
    labelOf h c = ⟨canon (pivs h (cP h c)) (bas h (cP h c)), pivs h (cP h c)⟩ := by
  classical
  rw [labelOf, if_pos hg]

theorem lab_dim (hg : GoodCode h c) : (labelOf h c).dim = cdim c := by
  rw [lab_def hg]; exact hg.dim

theorem lab_span (hg : GoodCode h c) {x : Space (Fin h)} (hx : (labelOf h c).Mem x) :
    x = ∑ p ∈ pivs h (cP h c), x p • bas h (cP h c) p := by
  rw [lab_def hg] at hx
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k ∈ pivs h (cP h c)
  · have e : ∀ p ∈ pivs h (cP h c), x p * bas h (cP h c) p k = if p = k then x p else 0 :=
      fun p hp => by rw [hg.ech p hp k hk]; split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq', if_pos hk]
  · have e := hx k hk
    simp only [canon, Equiv.coe_fn_mk, cfun, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, if_neg hk,
      smul_eq_mul] at e
    rw [eq_neg_of_add_eq_zero_left e, ZMod.neg_eq_self_mod_two]

theorem lab_bas (hg : GoodCode h c) (p : Fin h) : (labelOf h c).Mem (bas h (cP h c) p) := by
  by_cases hp : p ∈ pivs h (cP h c)
  · rw [lab_def hg]
    intro k hk
    simp only [canon, Equiv.coe_fn_mk, cfun, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, if_neg hk,
      smul_eq_mul]
    have e : ∀ p' ∈ pivs h (cP h c), bas h (cP h c) p p' * bas h (cP h c) p' k =
        if p = p' then bas h (cP h c) p' k else 0 :=
      fun p' hp' => by rw [hg.ech p hp p' hp']; split_ifs <;> simp
    rw [Finset.sum_congr rfl e, Finset.sum_ite_eq, if_pos hp]
    exact f2 _
  · have : bas h (cP h c) p = 0 := by
      simpa [pivs] using hp
    rw [this]; exact mem_zero _

theorem lab_mem (hg : GoodCode h c) (x : Space (Fin h)) :
    (labelOf h c).Mem x ↔ x = ∑ p ∈ pivs h (cP h c), x p • bas h (cP h c) p :=
  ⟨lab_span hg, fun e => by rw [e]; exact mem_sum _ _ fun p _ => mem_smul _ (lab_bas hg p)⟩

theorem lab_sub (hg : GoodCode h c) {V : SubspaceLabel (Fin h)} (hV : ∀ p, V.Mem (bas h (cP h c) p))
    {x : Space (Fin h)} (hx : (labelOf h c).Mem x) : V.Mem x := by
  rw [lab_span hg hx]
  exact mem_sum _ _ fun p _ => mem_smul _ (hV p)

end

def mic (cf : Co → Coef) (l : List (Nat × Nat × Co)) : List Micro :=
  l.map fun x => Micro.add x.1 x.2.1 (cf x.2.2)

section
variable {ρ α : Type} [Fintype ρ] [DecidableEq ρ] [Fintype α] [DecidableEq α]
variable {p : Par} {emb : ρ → Nat} {un : Nat → ρ}

noncomputable def Par.labS (p : Par) (S : Trie) (r : Nat) : SubspaceLabel (Fin p.h) :=
  labelOf p.h (p.tab.get (S.get r))

structure Ctx (p : Par) (emb : ρ → Nat) (un : Nat → ρ) : Prop where
  hT : checkTable p.h p.tab = true
  hn : p.n ≤ 2 ^ p.d
  hun : ∀ q, un (emb q) = q
  hin : ∀ r, r < p.n →
    emb (un r) = r
  hlt : ∀ q, emb q < p.n

end

inductive Moves (n : Nat) (tab : Trie) (P : Nat → Prop) (f : Nat) : List Nat → Trie → Trie → List Nat → Prop
  | nil (S : Trie) : Moves n tab P f [] S S []
  | same {r : Nat} {l : List Nat} {S S' : Trie} {rs : List Nat} : r < n → S.get r = f →
      Moves n tab P f l S S' rs → Moves n tab P f (r :: l) S S' rs
  | up {r : Nat} {l : List Nat} {S S' : Trie} {rs : List Nat} : r < n → S.get r ≠ f → P (S.get r) →
      cdim (tab.get (S.get r)) < cdim (tab.get f) → Moves n tab P f l (S.set r f) S' rs →
      Moves n tab P f (r :: l) S S' ((cdim (tab.get f) - cdim (tab.get (S.get r))) :: rs)

theorem Moves.mono {n : Nat} {tab : Trie} {P Q : Nat → Prop} {f : Nat} (hPQ : ∀ a, P a → Q a)
    {l : List Nat} {S S' : Trie} {rs : List Nat} (h : Moves n tab P f l S S' rs) : Moves n tab Q f l S S' rs := by
  induction h with
  | nil S => exact .nil S
  | same h1 h2 _ ih => exact .same h1 h2 ih
  | up h1 h2 h3 h4 _ ih => exact .up h1 h2 (hPQ _ h3) h4 ih

def GateOK (p : Par) (S : Trie) (g : Gate) (S' : Trie) (rs : List Nat) : Prop :=
  Moves p.n p.tab (fun a => ∀ x, (labelOf p.h (p.tab.get a)).Mem x → (labelOf p.h (p.tab.get g.frame)).Mem x)
    g.frame g.regs S S' rs

def vec (h w : Nat) : Space (Fin h) := fun q => bF (w.testBit q.val)

theorem vec_xor (h a b : Nat) : vec h (a ^^^ b) = vec h a + vec h b := by
  funext q; simp only [vec, Nat.testBit_xor, bF_xor, Pi.add_apply]

theorem vec_zero (h : Nat) : vec h 0 = 0 := by funext q; simp [vec, bF]

theorem dv_word (h P p : Nat) : dv h P p = vec h (word h P p) := by
  funext q; simp only [dv, vec, testBit_word, decide_eq_true q.2, Bool.true_and]

theorem vec_eq_zero {h w : Nat} (hw : w < 2 ^ h) : vec h w = 0 ↔ w = 0 := by
  constructor
  · intro e
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < h
    · have := congrFun e ⟨i, hi⟩
      simpa [vec, bF_eq_zero] using this
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rintro rfl; exact vec_zero h

theorem inSpan_mem {h c x : Nat} (hg : GoodCode h c) (hx : InSpan h c x) : (labelOf h c).Mem (vec h x) :=
  hx (fun w => (labelOf h c).Mem (vec h w))
    ⟨show (labelOf h c).Mem (vec h 0) by rw [vec_zero]; exact mem_zero _,
      fun a b ha hb => show (labelOf h c).Mem (vec h (a ^^^ b)) by rw [vec_xor]; exact mem_add ha hb⟩
    (fun q hq => show (labelOf h c).Mem (vec h (word h (cP h c) q)) by
      rw [← dv_word]; exact lab_bas hg ⟨q, hq⟩)

theorem lab_incl {h ca cb : Nat} (ha : GoodCode h ca) (hb : GoodCode h cb)
    (H : ∀ q, q < h → InSpan h cb (word h (cP h ca) q)) :
    ∀ x, (labelOf h ca).Mem x → (labelOf h cb).Mem x :=
  fun x hx => lab_sub ha (fun i => by rw [bas, dv_word]; exact inSpan_mem hb (H i i.2)) hx

theorem count_sum (f : Nat → Bool) : ∀ n, ((List.range n).filter f).length = ∑ q ∈ range n, if f q then 1 else 0
  | 0 => by simp
  | n + 1 => by rw [len_filter_succ, count_sum f n, sum_range_succ]

theorem goodCode_of {h c : Nat} (g : GoodN h c) : GoodCode h c := by
  have hb : ∀ p : Fin h, bas h (cP h c) p ≠ 0 ↔ word h (cP h c) p ≠ 0 := fun p => by
    rw [bas, dv_word]; exact not_congr (vec_eq_zero (Nat.mod_lt _ (Nat.two_pow_pos h)))
  refine ⟨fun p hp q hq => ?_, ?_, g.bnd⟩
  · rw [pivs, mem_filter, hb] at hp hq
    simp only [bas, dv_word, vec, g.ech p q p.2 q.2 hp.2 hq.2, Fin.ext_iff]
    split_ifs with e <;> simp [bF, e]
  · rw [pivs, Finset.card_filter, ← g.dim, count_sum,
      ← Fin.sum_univ_eq_sum_range (fun q => if (word h (cP h c) q != 0) = true then 1 else 0) h]
    exact Finset.sum_congr rfl fun p _ => by simp [hb p]

theorem tabK_code (h : Nat) (t : Trie) (H : checkTable h t = true) (a : Nat) : GoodCode h (t.get a) :=
  goodCode_of (tabK_good h t H a)

theorem moves_of (p : Par) (hT : checkTable p.h p.tab = true) (f : Nat) : ∀ (l : List Nat) (S : Trie),
    rOk p f S l → (∀ ca ∈ rCl p f S l, ∀ q, q < p.h → InSpan p.h (p.tab.get f) (word p.h (cP p.h ca) q)) →
    Moves p.n p.tab (fun a => ∀ x, (labelOf p.h (p.tab.get a)).Mem x → (labelOf p.h (p.tab.get f)).Mem x)
      f l S (rOut f S l) (rRanks p f S l)
  | [], S, _, _ => .nil S
  | r :: l, S, hok, hc => by
    obtain ⟨⟨hr, hlt⟩, ho⟩ := hok
    show Moves _ _ _ f (r :: l) S (rOut f (vOut f S r) l) (vRanks p f S r ++ rRanks p f (vOut f S r) l)
    have hc' : ∀ ca ∈ vCl p f S r ++ rCl p f (vOut f S r) l, ∀ q, q < p.h →
        InSpan p.h (p.tab.get f) (word p.h (cP p.h ca) q) := hc
    by_cases e : S.get r = f
    · have ev : vOut f S r = S := if_pos e
      have hv : vRanks p f S r = [] := if_pos e
      have hcl : vCl p f S r = [] := if_pos e
      rw [hv, List.nil_append, ev]
      rw [ev] at ho
      rw [hcl, ev, List.nil_append] at hc'
      exact .same hr e (moves_of p hT f l S ho hc')
    · have ev : vOut f S r = S.set r f := if_neg e
      have hv : vRanks p f S r = [cdim (p.tab.get f) - cdim (p.tab.get (S.get r))] := if_neg e
      have hcl : vCl p f S r = [p.tab.get (S.get r)] := if_neg e
      rw [hv, ev, List.singleton_append]
      rw [ev] at ho
      rw [hcl, ev, List.singleton_append] at hc'
      have hg := tabK_code _ _ hT
      exact .up hr e (lab_incl (hg _) (hg _) (hc' _ (List.mem_cons.2 (Or.inl rfl)))) (hlt e)
        (moves_of p hT f l _ ho fun ca h => hc' ca (List.mem_cons.2 (Or.inr h)))

theorem checkGate_sound {p : Par} {K : Nat} (hT : checkTable p.h p.tab = true) (h1 : 0 < p.h) {g : Gate}
    {S : Trie} {rs : List Nat} {k : Trie → List Nat → Bool}
    (H : checkGate p (2 ^ p.h - 1) (p.h * p.h) (8 + p.h) (rep p.h K) g S rs k = true) :
    ∃ S' rs0 rs1, rs = rs0 ++ rs1 ∧ k S' rs1 = true ∧ GateOK p S g S' rs0 := by
  obtain ⟨⟨ho, hcl⟩, rs', e, hk⟩ := gate_sound p hT h1 g S rs k H
  exact ⟨_, _, rs', e, hk, moves_of p hT g.frame g.regs S ho hcl⟩

def tvec (h u : Nat) : Space (Fin h) :=
  fun q => bF (u.testBit q.val)

structure PortOK (p : Par) (v : Nat) (S0 SA SF : Trie) (u t : Nat) : Prop where
  unit : dot (tvec p.h u) (tvec p.h u) = 1
  gap : ∃ q, tvec p.h u q = 0
  x0 : (p.labS S0 t).dim = 1 ∧ (p.labS S0 t).Mem (tvec p.h u)
  y0 : S0.get (v + t) = 0
  yA : SA.get (v + t) = 0
  xF : (p.labS SF t).dim = p.h
  yF : (p.labS SF (v + t)).dim + 1 = p.h ∧ ∀ x, (p.labS SF (v + t)).Mem x → dot (tvec p.h u) x = 0

structure EndsX (p : Par) (v : Nat) (ports rets gl el : List Nat) (S0 SA SF : Trie) : Prop where
  h1 : 0 < p.h
  wf : S0.wf p.d
  hn : p.n ≤ 2 ^ p.d
  hv : 2 * v ≤ p.n
  z0 : cdim (p.tab.get 0) = 0
  len : ports.length = v
  port : ∀ t, t < v → PortOK p v S0 SA SF (ports.getD t 0) t
  ret : ∀ r ∈ rets, 0 < cdim (p.tab.get (SA.get r))
  zgl : ∀ q, q < p.n - 2 * v → S0.get (2 * v + q) = 0 ∨ 2 * v + q ∈ gl
  full : ∀ q, q < p.n - 2 * v → memK (2 * v + q) el = false → (p.labS SF (2 * v + q)).dim = p.h
  sub : ∀ q, q < p.n - 2 * v → memK (2 * v + q) el = true →
    ∀ x, (p.labS S0 (2 * v + q)).Mem x → (p.labS SF (2 * v + q)).Mem x

theorem sum_bF (f : Nat → Bool) (n : Nat) :
    (∑ q : Fin n, bF (f q)) = (((List.range n).filter f).length : F) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => bF (f q)) n, count_sum]
  push_cast
  exact Finset.sum_congr rfl fun q _ => by cases f q <;> simp [bF]

theorem castF (n : Nat) : (n : F) = ((n % 2 : Nat) : F) := (ZMod.natCast_mod n 2).symm

theorem dot_word {h u P j : Nat} (H : orthW h u (word h P j)) : dot (tvec h u) (dv h P j) = 0 := by
  have e : dot (tvec h u) (dv h P j) = ∑ q : Fin h, bF (u.testBit q && (word h P j).testBit q) := by
    simp only [dot, tvec, dv_word, vec, bF_and]
  rw [e, sum_bF (fun q => u.testBit q && (word h P j).testBit q), castF]
  unfold orthW at H
  rw [H]; simp

theorem portOK_of {p : Par} {v : Nat} {S0 SA SF : Trie} {t u : Nat} (hT : checkTable p.h p.tab = true)
    (P : PortN p v S0 SA SF t u) : PortOK p v S0 SA SF u t := by
  have hg := tabK_code _ _ hT
  refine ⟨?_, ?_, ⟨?_, inSpan_mem (hg _) P.x0m⟩, P.y0, P.yA, ?_, ⟨?_, fun x hx => ?_⟩⟩
  · have e : dot (tvec p.h u) (tvec p.h u) = ∑ q : Fin p.h, bF (u.testBit q) := by
      simp only [dot, tvec]
      exact Finset.sum_congr rfl fun q _ => by cases u.testBit q <;> decide
    have ho := P.odd
    unfold oddW at ho
    rw [e, sum_bF (fun q => u.testBit q), castF, ho]; simp
  · obtain ⟨q, hq, hb⟩ := P.gap
    exact ⟨⟨q, hq⟩, by simp [tvec, hb, bF]⟩
  · rw [Par.labS, lab_dim (hg _)]; exact P.x0d
  · rw [Par.labS, lab_dim (hg _)]; exact P.xF
  · rw [Par.labS, lab_dim (hg _)]; exact P.yFd
  · rw [Par.labS] at hx
    rw [lab_span (hg _) hx, dot_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [dot_smul_right]
    exact mul_eq_zero_of_right _ (dot_word (P.yFo j j.2))

theorem checkEnds_soundX {p : Par} {v : Nat} {ports rets gl el : List Nat} {S0 SA SF : Trie}
    (hT : checkTable p.h p.tab = true) (H : checkEnds p v ports rets gl el S0 SA SF = true) :
    EndsX p v ports rets gl el S0 SA SF := by
  have E := checkEnds_sound hT H
  have hg := tabK_code _ _ hT
  exact ⟨E.hh, E.w0, E.hn, E.hv, E.z0, E.len, fun t ht => portOK_of hT (E.port t ht), E.ret,
    fun q hq => (E.slot q hq).1,
    fun q hq hm => by rw [Par.labS, lab_dim (hg _)]; exact (E.slot q hq).2.1 hm,
    fun q hq hm => lab_incl (hg _) (hg _) ((E.slot q hq).2.2 hm)⟩

end
end LabelCheck
