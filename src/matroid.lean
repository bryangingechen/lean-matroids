/-
Matroids, after Chapter 1 of Oxley, Matroid Theory, 1992.
-/
import tactic.wlog data.equiv.list tactic.find

/- The next two sections are by Mario Carneiro (For mathlib) https://gist.github.com/digama0/edc2a9fe4d468c3921c87650eea5b77a -/
namespace multiset
open nat

@[simp] theorem card_filter_map_le {α β} {f : α → option β}
  (s : multiset α) : card (filter_map f s) ≤ card s :=
multiset.induction_on s (nat.zero_le _) begin
  intros a s IH,
  cases h : f a,
  { rw [filter_map_cons_none _ _ h, card_cons],
    exact le_succ_of_le IH },
  { rw [filter_map_cons_some _ _ _ h, card_cons, card_cons],
    exact succ_le_succ IH }
end

end multiset

namespace finset
open nat

def filter_map {α β} [decidable_eq β] (f : α → option β) (s : finset α) : finset β :=
(s.1.filter_map f).to_finset

@[simp] theorem filter_map_empty {α β} [decidable_eq β] (f : α → option β) :
  filter_map f ∅ = ∅ := rfl

@[simp] theorem mem_filter_map {α β} [decidable_eq β] {f : α → option β} {s : finset α}
  {b : β} : b ∈ s.filter_map f ↔ ∃ a ∈ s, b ∈ f a :=
by simp [filter_map]; refl

theorem card_filter_map_le {α β} [decidable_eq β] {f : α → option β} {s : finset α} :
  card (s.filter_map f) ≤ card s :=
le_trans (multiset.card_le_of_le $ multiset.erase_dup_le _)
  (multiset.card_filter_map_le _)

theorem filter_map_insert_none {α β} [decidable_eq α] [decidable_eq β]
  (f : α → option β) {a : α} {s : finset α} (hf : f a = none) :
  filter_map f (insert a s) = filter_map f s :=
begin
  by_cases a ∈ s,
  { rw insert_eq_of_mem h },
  { simp [filter_map, multiset.ndinsert_of_not_mem h,
      multiset.filter_map_cons_none _ _ hf] }
end

theorem filter_map_insert_some {α β} [decidable_eq α] [decidable_eq β]
  (f : α → option β) {a : α} {s : finset α} {b} (hf : f a = some b) :
  filter_map f (insert a s) = insert b (filter_map f s) :=
begin
  by_cases a ∈ s,
  { rw [insert_eq_of_mem h, insert_eq_of_mem],
    exact mem_filter_map.2 ⟨_, h, hf⟩ },
  { simp [filter_map, multiset.ndinsert_of_not_mem h, multiset.filter_map_cons_some _ _ _ hf] }
end

theorem mem_of_card_filter_map {α β} [decidable_eq β] {f : α → option β} {s : finset α}
  (h : card (s.filter_map f) = card s) {a} (ha : a ∈ s) : ∃ b, b ∈ f a :=
begin
  haveI := classical.dec_eq α,
  cases h' : f a with b, swap, {exact ⟨b, rfl⟩},
  refine (not_succ_le_self (card (erase s a)) (_ : _ + 1 ≤ _)).elim,
  rw [← insert_erase ha, filter_map_insert_none f h',
    card_insert_of_not_mem (not_mem_erase _ _)] at h, rw ← h,
  apply card_filter_map_le
end

theorem inj_of_card_filter_map {α β} [decidable_eq β] {f : α → option β} {s : finset α}
  (H : card (s.filter_map f) = card s) {a a'} (ha : a ∈ s) (ha' : a' ∈ s)
    {b} (h1 : b ∈ f a) (h2 : b ∈ f a') : a = a' :=
begin
  haveI := classical.dec_eq α,
  by_contra h,
  rw [← insert_erase ha', filter_map_insert_some f h2,
    card_insert_of_not_mem (not_mem_erase _ _), insert_eq_of_mem] at H,
  { refine (not_succ_le_self (card (erase s a')) (_ : _ + 1 ≤ _)).elim,
    rw ← H, apply card_filter_map_le },
  { exact mem_filter_map.2 ⟨_, mem_erase.2 ⟨h, ha⟩, h1⟩ }
end

theorem exists_subset_filter_map_eq
  {α β} [decidable_eq α] [decidable_eq β] (f : α → option β) (s : finset α) :
  ∃ t ⊆ s, s.filter_map f = filter_map f t ∧ card (t.filter_map f) = card t :=
begin
  refine finset.induction_on s ⟨∅, by simp⟩ _,
  rintro a s as ⟨t, ss, st, ct⟩,
  cases h : f a with b,
  { refine ⟨t, subset.trans ss (subset_insert _ _), _, ct⟩,
    simpa [filter_map_insert_none f h] },
  simp [filter_map_insert_some f h],
  by_cases h' : b ∈ filter_map f s,
  { simp [h'],
    refine ⟨t, subset.trans ss (subset_insert _ _), _, ct⟩,
    simpa [filter_map_insert_none f h] },
  { refine ⟨insert a t, _⟩,
    have ha := mt (@ss _) as,
    rw [filter_map_insert_some f h],
    refine ⟨insert_subset_insert _ ss, by rw st, _⟩,
    rw [← st, card_insert_of_not_mem h', st, ct, card_insert_of_not_mem ha] }
end

end finset

variables {α : Type*} {β : Type*} [decidable_eq α]

namespace finset

lemma inter_of_subset {A B : finset α} (h : A ⊆ B) : A ∩ B = A :=
by simp [ext]; exact λ a, iff.intro (λ H, H.1) (λ H, ⟨H, mem_of_subset h H⟩)

lemma subset_iff_sdiff_eq_empty {x y : finset α} : x ⊆ y ↔ x \ y = ∅ :=
by simp [sdiff_eq_filter, eq_empty_iff_forall_not_mem, subset_iff]

lemma inter_subset_inter_of_subset {x y : finset α} (h₁ : x ⊆ y) (z : finset α) : x ∩ z ⊆ y ∩ z :=
by simp [subset_iff]; exact λ a h₂ h₃, ⟨h₁ h₂, h₃⟩

lemma empty_sdiff (E : finset α): E \ ∅ = E :=
by simp [ext]

lemma sdiff_subset (A B : finset α): A \ B ⊆ A := (empty_sdiff A).subst $
  sdiff_subset_sdiff (subset.refl A) $ empty_subset B

lemma sdiff_eq_sdiff_inter (A B : finset α) : A \ B = A \ (A ∩ B) :=
by simp [ext]; exact λ a, iff.intro (λ h, ⟨h.1, λ x, h.2⟩) (λ h, ⟨h.1, h.2 h.1⟩)

lemma union_eq_union_sdiff (A B : finset α) : A ∪ B = A ∪ (B \ A) :=
by simp [ext]; exact λ a, ⟨λ ha, or.elim ha (λ H, or.inl H)
  (by { intro H, by_cases h : a ∈ A, { exact or.inl h }, { exact or.inr ⟨H, h⟩ } }),
  λ ha, or.elim ha (λ H, or.inl H) (λ H, or.inr H.1)⟩

lemma card_eq_inter_sdiff (A B : finset α) : card A = card (A ∩ B) + card (A \ B) :=
begin
  have hA : A \ B ∪ A ∩ B = A := by simp [ext];
    exact λ a, iff.intro (λ ha, or.elim ha (λ H, H.1) (λ H, H.1))
      (by { intro ha, by_cases h : a ∈ B, { exact or.inl ⟨ha, h⟩ }, { exact or.inr ⟨ha, h⟩ } }),
  have : disjoint (A \ B) (A ∩ B) := by simp [disjoint],
  replace this := card_disjoint_union this, rwa [hA, add_comm] at this
end

lemma card_sdiff (A B : finset α) : card (A \ B) = card A - card (A ∩ B) :=
(nat.sub_eq_of_eq_add $ card_eq_inter_sdiff A B).symm

lemma card_union_inter (A B : finset α) : card A + card B = card (A ∪ B) + card (A ∩ B) :=
begin
  have hBA : card B = card (B \ A) + card (A ∩ B) := inter_comm B A ▸
    (add_comm (card (B ∩ A)) (card (B \ A))) ▸ (card_eq_inter_sdiff B A),
  have Hdis : disjoint A (B \ A) := by simp [disjoint],
  have H : card A + card (B \ A) = card (A ∪ B) :=
    (congr_arg card $ union_eq_union_sdiff A B).substr (card_disjoint_union Hdis).symm,
  calc
  card A + card B = card A + card (B \ A) + card (A ∩ B) : by rw [add_assoc, hBA]
  ... = card (A ∪ B) + card (A ∩ B) : by rw H
end

/- proof by Kenny Lau https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/choosing.20from.20difference.20of.20finsets/near/133624012 -/
lemma exists_sdiff_of_card_lt {x y : finset α} (hcard : card x < card y) : ∃ e : α, e ∈ y \ x :=
suffices ∃ e ∈ y, e ∉ x, by simpa,
by_contradiction $ λ H, not_le_of_lt hcard $ card_le_of_subset $ by simpa using H

/- proof by chris hughes
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/maximal.20finset.20in.20finset.20of.20finsets/near/133905271 -/
lemma max_fun_of_ne_empty {F : finset β} (func : β → ℕ) (h : F ≠ ∅) :
  ∃ x ∈ F, ∀ g ∈ F, func g ≤ func x :=
let ⟨n, hn⟩ := (max_of_ne_empty (mt image_eq_empty.1 h) : ∃ a, a ∈ finset.max (F.image func)) in
let ⟨x, hx₁, hx₂⟩ := mem_image.1 (mem_of_max hn) in
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, le_max_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

lemma min_fun_of_ne_empty {F : finset β} (func : β → ℕ) (h : F ≠ ∅) :
  ∃ x ∈ F, ∀ g ∈ F, func x ≤ func g :=
let ⟨n, hn⟩ := (min_of_ne_empty $ mt image_eq_empty.1 h : ∃ a, a ∈ finset.min (F.image func)) in
let ⟨x, hx₁, hx₂⟩ := mem_image.1 (mem_of_min hn) in
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, le_min_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

section inst

variables {F : finset α} {Q : finset α → Prop} [decidable_pred Q] {P : α → Prop} [decidable_pred P]

instance decidable_not_forall (c₁ : finset (finset α)) :
  decidable (∃ x : finset α, ¬(x ∈ c₁ → ¬Q x)) :=
decidable_of_iff (∃ x ∈ c₁, Q x) $ by simp

instance decidable_exists_and_mem : decidable (∃ e, e ∈ F ∧ P e) :=
decidable_of_iff (∃ e ∈ F, P e) $ by simp

end inst

end finset

open finset

-- § 1.1

namespace matroid

variables [fintype α]

variable (α)
/-- `indep E` is the type of matroids (encoded as systems of independent sets) with ground set `E` :
`finset α` -/
structure indep :=
(indep : finset (finset α))
-- (I1)
(empty_mem_indep : ∅ ∈ indep)
-- (I2)
(indep_of_subset_indep {x y} (hx : x ∈ indep) (hyx : y ⊆ x) : y ∈ indep)
-- (I3)
(indep_exch {x y : finset α} (hx : x ∈ indep) (hy : y ∈ indep) (hcard : card x < card y)
  : ∃ e : α, e ∈ y \ x ∧ insert e x ∈ indep)
--attribute [class] indep

instance indep_repr [has_repr α] : has_repr (indep α) :=
⟨λ m, has_repr.repr m.indep⟩

variable {α}
theorem eq_of_indep_eq : ∀ {M₁ M₂ : indep α}, M₁.1 = M₂.1 → M₁ = M₂
  | ⟨I₁, p₁, q₁, r₁⟩ ⟨I₂, p₂, q₂, r₂⟩ h :=
by simpa

/-- A circuit of a matroid is a minimal dependent subset of the ground set -/
def is_circuit (x : finset α) (m : indep α) : Prop :=
x ∉ m.indep ∧ ∀ y, y ⊂ x → y ∈ m.indep

/-- proof by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finsets.2C.20decidable_mem.2C.20and.20filter/near/133708937 -/
instance decidable_circuit (x : finset α) (m : indep α) : decidable (is_circuit x m) :=
decidable_of_iff (x ∉ m.indep ∧ ∀ y ∈ (powerset x).erase x, y ∈ m.indep)
begin
  simp [is_circuit, (⊂)],
  refine and_congr iff.rfl (forall_congr $ λ y, _),
  refine ⟨λ H h₁ h₂, H (mt _ h₂) h₁, λ H h₁ h₂, H h₂ $ mt _ h₁⟩,
  { rintro rfl, refl }, { exact subset.antisymm h₂ }
end

instance decidable_circuit_subset (x : finset α) (m : indep α) :
  decidable (∃ (y : finset α) (H : y ⊆ x), is_circuit y m) :=
decidable_of_iff (∃ (y : finset α) (H : y ∈ powerset x), is_circuit y m) $ by simp

/- should I make this definition reducible? I don't know when to use attributes... -/
def circuits_circ_of_indep (m : indep α) : finset (finset α) :=
(powerset univ).filter (λ S, is_circuit S m)

lemma C2_of_indep (m : indep α) (x y : finset α) (hx : x ∈ circuits_circ_of_indep m)
  (hy : y ∈ circuits_circ_of_indep m) (hxy : x ⊆ y) : x = y :=
begin
  simp [circuits_circ_of_indep, is_circuit] at *,
  have hnxy : ¬x ⊂ y := λ h, hx.2.1 $ hy.2.2 x h,
  rw ←lt_iff_ssubset at hnxy, rw [←le_iff_subset, le_iff_eq_or_lt] at hxy,
  exact or.elim hxy id (λ hxy2, false.elim $ hnxy hxy2)
end

theorem dep_iff_circuit_subset (x : finset α) (m : indep α) :
  x ∉ m.indep ↔ ∃ y ⊆ x, is_circuit y m :=
iff.intro (λ hxd, exists.elim (min_fun_of_ne_empty card (ne_empty_of_mem $
    mem_filter.mpr ⟨mem_powerset.mpr $ subset.refl x, hxd⟩)) $
  λ a ha, exists.elim ha $
    λ ha2 hamin, exists.intro a $ have hax : a ⊆ x := mem_powerset.mp (mem_filter.mp ha2).1,
      exists.intro hax $ by unfold is_circuit;
        exact ⟨(mem_filter.mp ha2).2, by { intros y hy, by_contra h,
          exact not_le_of_lt (card_lt_card hy) (hamin y $ mem_filter.mpr ⟨mem_powerset.mpr $
            subset.trans (le_of_lt $ lt_iff_ssubset.mpr hy) hax, h⟩) }⟩) $
  λ H, exists.elim H $ λ a ha, exists.elim ha $
    by { intros hax hacirc hxi, unfold is_circuit at hacirc,
    exact hacirc.1 (m.indep_of_subset_indep hxi hax) }

/-- Lemma 1.1.3 -/
lemma C3_of_indep (m : indep α) (x y : finset α) (e : α) (hx : x ∈ circuits_circ_of_indep m)
  (hy : y ∈ circuits_circ_of_indep m) (hxny : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits_circ_of_indep m ∧ z ⊆ erase (x ∪ y) e :=
have hxmy : x \ y ≠ ∅ := mt subset_iff_sdiff_eq_empty.mpr $ mt (C2_of_indep m x y hx hy) hxny,
  exists.elim (exists_mem_of_ne_empty hxmy) $
    by { clear hxny hxmy,
    intros a ha, simp [circuits_circ_of_indep] at ha hx hy he,
    have hxai : erase x a ∈ m.indep := by unfold is_circuit at hx;
      exact hx.2.2 (erase x a) (erase_ssubset ha.1),
    let F := (powerset (x ∪ y)).filter (λ S, erase x a ⊆ S ∧ S ∈ m.indep),
    have hxaF : erase x a ∈ F := mem_filter.2 ⟨mem_powerset.mpr $ subset.trans (erase_subset a x) $
      @subset_union_left _ _ x y, ⟨subset.refl _, hxai⟩⟩, clear hxai,
    exact exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem hxaF)
      (λ I hEI2, exists.elim hEI2 $ by clear hxaF hEI2;
        exact λ hIF hI,
          have hIFindep : I ∈ m.indep := (mem_filter.mp hIF).2.2,
          have hIdep : _ → I ∉ m.indep := (dep_iff_circuit_subset I m).2,
          have hIFxa : erase x a ⊆ I := (mem_filter.mp hIF).2.1,
          have hIxuy : I ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hIF).1,
          have haniI : a ∉ I :=
            λ H, have hxI : x ⊆ I := (insert_erase ha.1) ▸ insert_subset.mpr ⟨H, hIFxa⟩,
              have ∃ A ⊆ I, is_circuit A m := exists.intro x (exists.intro hxI hx.2),
              hIdep this hIFindep,
          have hEg : ∃ g ∈ y, g ∉ I :=
            by { have hIdep2 := mt hIdep, simp at hIdep2,
            have hyI0 := mt (hIdep2 hIFindep y), simp at hyI0,
            have hYI : ¬y ⊆ I := hyI0 hy.2,
            have this := exists_mem_of_ne_empty (mt subset_iff_sdiff_eq_empty.mpr hYI),
            simp at this, simpa },
          exists.elim hEg $ λ g hEg2, exists.elim hEg2 $ by { clear hEg hEg2 hIdep,
            intros hgy hgnI,
            have hga : g ≠ a := λ H, ha.2 (H ▸ hgy),
            have hIag : I ⊆ erase (erase (x ∪ y) a) g :=
              subset_iff.mpr (λ xx hxx, mem_erase.mpr ⟨λ hgg, hgnI $ hgg ▸ hxx,
                mem_erase.mpr ⟨λ hgga, haniI $ hgga ▸ hxx, mem_of_subset hIxuy hxx⟩⟩),
            have haxuy : a ∈ x ∪ y := mem_union_left y ha.1,
            have hcardxye : card (erase (x ∪ y) a) = nat.pred (card (x ∪ y)) :=
              card_erase_of_mem haxuy,
            have hpcard : nat.pred (card (x ∪ y)) > 0 := by rw ←hcardxye;
              exact card_pos.mpr (ne_empty_of_mem $ mem_erase.mpr ⟨hga, mem_union_right x hgy⟩),
            have hcard : card I < card (erase (x ∪ y) e) :=
              calc card I ≤ card (erase (erase (x ∪ y) a) g) : card_le_of_subset hIag
              ... = nat.pred (nat.pred (card (x ∪ y))) : by rw [card_erase_of_mem
                (mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), hcardxye]
              ... < card (erase (x ∪ y) e) :
                by { rw [card_erase_of_mem (mem_union_left y he.1),
                ←nat.succ_pred_eq_of_pos hpcard], exact nat.lt_succ_self _ },
            clear hga hIag haxuy hcardxye hpcard he,
            by_contra h, simp [circuits_circ_of_indep] at h,
            have : (∀ x_1 : finset α, x_1 ⊆ erase (x ∪ y) e → ¬is_circuit x_1 m) :=
              λ x1 hx1, (mt $ h x1 $ subset_univ x1) $ not_not.mpr hx1,
            have hindep := mt (dep_iff_circuit_subset (erase (x ∪ y) e) m).mp, simp at hindep,
            replace hindep : erase (x ∪ y) e ∈ m.indep := hindep this,
            have hfinal := m.indep_exch hIFindep hindep hcard,
            exact exists.elim hfinal (λ El ⟨hElxy, hElindep⟩,
              have hElF : insert El I ∈ F := mem_filter.mpr ⟨mem_powerset.mpr
                (insert_subset.mpr ⟨(mem_erase.mp (mem_sdiff.mp hElxy).1).2, hIxuy⟩),
                ⟨subset.trans hIFxa (subset_insert El I), hElindep⟩⟩,
              have hcardEl : card I < card (insert El I) :=
                by { rw card_insert_of_not_mem (mem_sdiff.mp hElxy).2,
                exact lt_add_one (card I) },
              not_lt.mpr (hI (insert El I) hElF) hcardEl) } ) }

variable (α)
structure circuits :=
(circuits : finset (finset α))
-- (C1)
(empty_not_mem_circuits : ∅ ∉ circuits)
-- (C2)
(circuits_eq_of_subset {x y} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ⊆ y) : x = y)
-- (C3)
(circuit_elim {x y e} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits ∧ z ⊆ erase (x ∪ y) e)
--attribute [class] circuits

instance circuits_repr [has_repr α] (E : finset α) : has_repr (circuits α) :=
⟨λ c, has_repr.repr c.circuits⟩

variable {α}
theorem eq_of_circ_eq : ∀ {C₁ C₂ : circuits α}, C₁.1 = C₂.1 → C₁ = C₂
  | ⟨c₁, p₁, q₁, r₁⟩ ⟨c₂, p₂, q₂, r₂⟩ h :=
by simpa

def circuits_of_indep (m : indep α) : circuits α :=
⟨circuits_circ_of_indep m,
by simp [circuits_circ_of_indep, is_circuit]; exact λ h h1, h m.empty_mem_indep,
C2_of_indep m,
C3_of_indep m⟩

/- make reducible? -/
def indep_indep_of_circuits (C : circuits α) : finset (finset α) :=
(powerset univ).filter (λ S, ∀ c ∈ C.circuits, ¬c ⊆ S)

/-- first part of Theorem 1.1.4 -/
lemma I2_of_circuits (C : circuits α) (x y : finset α) : x ∈ indep_indep_of_circuits C → y ⊆ x →
  y ∈ indep_indep_of_circuits C :=
by unfold indep_indep_of_circuits at *; simp at *;
  exact λ hxE hx hxy, ⟨subset.trans hxy hxE, λ c hc H, hx c hc $ subset.trans H hxy⟩

/-- second part of Theorem 1.1.4 -/
lemma I3_of_circuits (C : circuits α) (x y : finset α) (hx : x ∈ indep_indep_of_circuits C)
  (hy : y ∈ indep_indep_of_circuits C) (hcardxy : card x < card y)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep_indep_of_circuits C :=
begin
  unfold indep_indep_of_circuits at *, simp at hx hy,
  by_contra h, simp at h,
  let F := (powerset $ x ∪ y).filter (λ S, (∀ c ∈ C.circuits, ¬c ⊆ S) ∧ card x < card S),
  have hyF : y ∈ F := mem_filter.mpr ⟨mem_powerset.mpr $ subset_union_right x y,
    ⟨hy.2, hcardxy⟩⟩,
  exact exists.elim (min_fun_of_ne_empty (λ f, card (x \ f)) $ ne_empty_of_mem hyF)
    (λ z Hz, exists.elim Hz $ by { clear hcardxy Hz hyF,
      intros hz hminz,
      have hzxuy : z ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hz).1,
      replace hz := (mem_filter.mp hz).2,
      exact exists.elim (exists_sdiff_of_card_lt hz.2)
        (by { intros a ha, simp at ha,
        have hxsdiffz : x \ z ≠ ∅ :=
          by { intro H,
          have Hxsubz : x ⊆ z := subset_iff_sdiff_eq_empty.mpr H,
          have hay : a ∈ y := or.elim (mem_union.mp $ mem_of_subset hzxuy ha.1)
            (λ Hax, false.elim $ ha.2 Hax) id,
          have haindep : insert a x ∈ indep_indep_of_circuits C := I2_of_circuits C z (insert a x)
            (by simp [indep_indep_of_circuits];
            exact ⟨subset.trans hzxuy $ union_subset hx.1 hy.1, hz.1⟩)
            (insert_subset.mpr ⟨ha.1, Hxsubz⟩),
          unfold indep_indep_of_circuits at haindep, simp at haindep,
          exact h a hay ha.2 haindep.1 haindep.2 },
        exact exists.elim (exists_mem_of_ne_empty hxsdiffz)
          (by { clear h ha hxsdiffz,
          intros e he, simp at he,
          let T : α → finset α := λ f, erase (insert e z) f,
          have hTf1 : ∀ f, f ∈ z \ x → T f ⊆ x ∪ y :=
            by { intros f hf, simp at hf,
            rw [subset_iff],
            intros gg hgg, simp at hgg,
            simp,
            exact or.elim hgg.2 (λ gge, or.inl $ gge.symm ▸ he.1)
              (λ ggz, mem_union.mp $ mem_of_subset hzxuy ggz) },
          have hTf2 : ∀ f, f ∈ z \ x → card (x \ T f) < card (x \ z) :=
            by { intros f hf, simp at hf,
            suffices H : x \ T f ⊂ x \ z, exact card_lt_card H,
            by simp [ssubset_iff]; exact exists.intro e
              ⟨λ h_, ⟨λ hef, hf.2 $ hef ▸ he.1, or.inl rfl⟩,
              by { rw [subset_iff],
                intros gg hgg, simp at hgg,
                have ggnef : gg ≠ f := λ ggef, or.elim hgg
                  (λ gge, (gge.symm ▸ he.2) $ ggef.substr hf.1) (λ H, (ggef.substr hf.2) H.1),
                have he0 := mem_sdiff.mpr he,
                exact or.elim hgg (λ gge, gge.symm ▸ he0)
                (λ H, mem_sdiff.mpr ⟨H.1, λ ggz, (H.2 ggnef) $ or.inr ggz⟩) }⟩ },
          have hTfindep : ∀ f, f ∈ z \ x → T f ∉ indep_indep_of_circuits C :=
            by { intros f hf,
            unfold indep_indep_of_circuits, simp,
            intros hTfE H,
            have HTf1 : T f ⊆ x ∪ y := hTf1 f hf,
            have HTf2 : card (x \ T f) < card (x \ z) := hTf2 f hf,
            simp at hf,
            have HTfcard : card z = card (T f) :=
              by { simp [card_erase_of_mem (mem_insert.mpr $ or.inr hf.1),
              card_insert_of_not_mem he.2] },
            replace HTfcard : card x < card (T f) := HTfcard ▸ hz.2,
            have : T f ∈ F := mem_filter.mpr ⟨mem_powerset.mpr HTf1, ⟨H, HTfcard⟩⟩,
            exact not_lt.mpr (hminz (T f) this) HTf2 },
          have hTfC : ∀ f, f ∈ z \ x → ∃ c ∈ C.circuits, c ⊆ T f :=
            by { intros f hf,
            have : T f ∉ indep_indep_of_circuits C := hTfindep f hf,
              simp [indep_indep_of_circuits] at this,
            have hfc := this (subset.trans (hTf1 f hf) $ union_subset hx.1 hy.1),
            by_contra H, simp at H, contradiction },
          exact exists.elim (exists_sdiff_of_card_lt hz.2) (λ g hg, exists.elim (hTfC g hg) $
              λ Cg hCg, exists.elim hCg $
                by { clear hCg hTf1 hTf2 hTfindep hg,
                intros HCg1 HCg2,
                have hCgsub : Cg ⊆ insert e z := subset.trans HCg2 (erase_subset g $ insert e z),
                rw [subset_iff] at HCg2,
                have HCgzx : Cg ∩ (z \ x) ≠ ∅ :=
                  λ H, suffices Cg ⊆ x, from hx.2 Cg HCg1 this,
                    suffices H1 : Cg ⊆ erase (insert e (x ∩ z)) g, from
                    suffices H2 : erase (insert e (x ∩ z)) g ⊆ x, from
                    subset.trans H1 H2,
                    show erase (insert e (x ∩ z)) g ⊆ x, by
                      { rw [subset_iff],
                      intros gg hgg, simp at hgg,
                      exact or.elim hgg.2 (λ gge, gge.symm ▸ he.1) (λ ggxggz, ggxggz.1) },
                    show Cg ⊆ erase (insert e (x ∩ z)) g, by
                      { rw [subset_iff],
                      intros gg hgg,
                      replace HCg2 : gg ∈ T g := HCg2 hgg, simp at HCg2,
                      simp, split,
                        { exact HCg2.1 },
                        { rw eq_empty_iff_forall_not_mem at H,
                        replace H : gg ∉ Cg ∩ (z \ x) := H gg, simp at H,
                      exact or.elim HCg2.2 (λ gge, or.inl gge) (λ ggz, or.inr ⟨H hgg ggz, ggz⟩) } },
                clear HCg2,
                exact exists.elim (exists_mem_of_ne_empty HCgzx)
                  (by { intros h0 hh0, rw [mem_inter] at hh0,
                  exact exists.elim (hTfC h0 hh0.2)
                    (λ Ch0 HCh0, exists.elim HCh0 $ λ hCh0circ hCh0T,
                      have hCgneCh0 : Cg ≠ Ch0 :=
                        λ H, have hh0Ch0 : h0 ∉ Ch0 := λ HH, (mem_erase.mp $
                          mem_of_subset hCh0T HH).1 rfl, (H.symm ▸ hh0Ch0) hh0.1,
                      have hCh0sub : Ch0 ⊆ insert e z :=
                        subset.trans hCh0T (erase_subset h0 $ insert e z),
                      have heCgCh0 : e ∈ Cg ∩ Ch0 :=
                        by { simp, split,
                          { by_contra heCg, have hCgz : Cg ⊆ z :=
                              (erase_eq_of_not_mem heCg) ▸ (subset_insert_iff.mp hCgsub),
                            exact hz.1 Cg HCg1 hCgz },
                          { by_contra heCh0, have hCh0z : Ch0 ⊆ z :=
                              (erase_eq_of_not_mem heCh0) ▸ (subset_insert_iff.1 hCh0sub),
                            exact hz.1 Ch0 hCh0circ hCh0z } },
                      exists.elim (C.circuit_elim HCg1 hCh0circ hCgneCh0 heCgCh0) $
                        λ CC ⟨hCCcirc, hCCCguCh0⟩,
                          have hCCz : CC ⊆ z :=
                            by { rw [subset_iff],
                            intros t ht,
                            rw [subset_iff] at hCCCguCh0,
                            have htCguCh0 := hCCCguCh0 ht, simp at htCguCh0,
                            rw [subset_iff] at hCgsub hCh0sub,
                            have orCg : t ∈ Cg → t ∈ z :=
                              λ htCg, or.elim (mem_insert.mp $ hCgsub htCg)
                                (λ H, false.elim $ htCguCh0.1 H) id,
                            have orCh0 : t ∈ Ch0 → t ∈ z :=
                              λ htCh0, or.elim (mem_insert.mp $ hCh0sub htCh0)
                              (λ H, false.elim $ htCguCh0.1 H) id,
                            exact or.elim htCguCh0.2 orCg orCh0 },
                          hz.1 CC hCCcirc hCCz) }) }) }) }) })
end

def indep_of_circuits (C : circuits α) : indep α :=
⟨indep_indep_of_circuits C,
mem_filter.mpr
  ⟨empty_mem_powerset univ, λ c hc H, C.empty_not_mem_circuits $ (subset_empty.mp H) ▸ hc⟩,
I2_of_circuits C,
I3_of_circuits C⟩

instance circ_indep : has_coe (circuits α) (indep α) := ⟨indep_of_circuits⟩
instance indep_circ : has_coe (indep α) (circuits α) := ⟨circuits_of_indep⟩

/-- third part of Theorem 1.1.4 -/
theorem circ_indep_circ : ∀ C : circuits α, C = circuits_of_indep (indep_of_circuits C)
  | ⟨c₁, p₁, q₁, r₁⟩ :=
by simp [indep_of_circuits, circuits_of_indep, indep_indep_of_circuits, circuits_circ_of_indep,
  is_circuit, ext];
exact λ c, iff.intro
  (λ hc : c ∈ c₁, have ce : c ⊆ univ := subset_univ c,
  ⟨ce, ⟨λ _ H, (H c hc) $ subset.refl c, λ f hf,
    ⟨subset.trans (le_of_lt $ lt_iff_ssubset.mpr hf) ce,
    λ g hg H, have Hc : g < c := lt_of_le_of_lt (le_iff_subset.mpr H) $ lt_iff_ssubset.mpr hf,
      have r : g = c := q₁ hg hc $ le_of_lt Hc, (not_le_of_lt Hc) $ le_of_eq r.symm⟩⟩⟩) $
  λ hc, have ∃ c_1 ∈ c₁, c_1 ⊆ c := by { have := not_forall.mp (hc.2.1 hc.1), simpa },
  exists.elim this $ λ c' H, exists.elim H $ by { intros hc' hcc',
    by_cases h : c = c', { exact h.symm ▸ hc' },
      { have hc'lt : c' ⊂ c := lt_of_le_of_ne (le_iff_subset.mpr hcc') (ne.symm h),
        have : c' ∉ c₁ := mt ((hc.2.2 c' hc'lt).2 c') (not_not.mpr $ subset.refl c'),
        exact false.elim (this hc') } }

theorem indep_circ_indep (M : indep α) : M = indep_of_circuits (circuits_of_indep M) :=
suffices M.indep = (indep_of_circuits $ circuits_of_indep M).indep, from eq_of_indep_eq this,
begin
  simp [circuits_of_indep, indep_of_circuits, circuits_circ_of_indep, indep_indep_of_circuits, ext],
  intro I,
  have hI : I ∈ M.indep → I ⊆ univ := λ H, subset_univ I,
  rw [←and_iff_right_of_imp hI, and_congr_right],
  intro hIE, have := not_iff_not_of_iff (dep_iff_circuit_subset I M),
  simp at this, rw [this, forall_congr],
  exact λ a, ⟨λ h h₁ h₂ h₃, (h h₃) h₂, λ h h₁ h₂, h (subset.trans h₁ hIE) h₂ h₁⟩
end

/-- Proposition 1.1.6 -/
theorem existsu_circuit_of_dep_of_insert_indep {I : finset α} {e : α} {m : indep α}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  ∃ c, c ∈ circuits_circ_of_indep m ∧ c ⊆ insert e I ∧ e ∈ c ∧
  ∀ c', c' ∈ circuits_circ_of_indep m → c' ⊆ insert e I → c' = c :=
by simp [circuits_circ_of_indep];
exact have hIE : I ⊆ univ, from subset_univ I,
have hIeE : insert e I ⊆ univ, from subset_univ (insert e I),
have hc : _, from (dep_iff_circuit_subset (insert e I) m).mp hIe,
exists.elim hc $ λ c hEc, exists.elim hEc $ λ hceI hccirc,
  have hcE : c ⊆ univ := subset_univ c,
  have hecirc : ∀ c' ⊆ insert e I, is_circuit c' m → e ∈ c' :=
    by { intros c' hc'eI hc'circ,
    have h₁ := subset_insert_iff.mp hc'eI,
    by_contra h,
    have h₂ := (erase_eq_of_not_mem h).symm,
    have h₃ : c' ⊆ I := calc
    c' = erase c' e : h₂
    ... ⊆ I : h₁,
    exact (dep_iff_circuit_subset I m).mpr (exists.intro c' $ exists.intro h₃ $ hc'circ) hI },
  have hec : e ∈ c := hecirc c hceI hccirc,
  exists.intro c $ by { exact ⟨⟨hcE, hccirc⟩, ⟨hceI,⟨hec, by { intros c' hc'E hc'circ hc'eI,
    have hec' : e ∈ c' := hecirc c' hc'eI hc'circ,
    have hcuc'eI : erase (c ∪ c') e ⊆ I := by simp [subset_iff] at hceI hc'eI ⊢;
      exact λ a hane ha, or.elim ha (λ H, or.elim (hceI H) (λ H, false.elim $ hane H) id)
        (λ H, or.elim (hc'eI H) (λ H, false.elim $ hane H) id),
    have : erase (c ∪ c') e ∈ m.indep := m.indep_of_subset_indep hI hcuc'eI,
    by_contra h,
    have C3 := C3_of_indep m c c' e, simp [circuits_circ_of_indep] at C3,
    exact exists.elim (C3 hcE hccirc hc'E hc'circ (ne.symm h) hec hec')
      (λ c₀ hc₀, (dep_iff_circuit_subset I m).mpr (exists.intro c₀ $ exists.intro
        (subset.trans hc₀.2 hcuc'eI) hc₀.1.2) hI) }⟩⟩⟩ }

section encodable
variable [encodable α]

--set_option trace.class_instances true
def circuit_of_dep_of_insert_indep {I : finset α} {e : α} {m : indep α}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) : finset α :=
encodable.choose (existsu_circuit_of_dep_of_insert_indep hI hIe)

local notation `cdii` := circuit_of_dep_of_insert_indep

def circuit_of_dep_of_insert_indep_spec {I : finset α} {e : α} {m : indep α}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  cdii hI hIe ∈ circuits_circ_of_indep m ∧ cdii hI hIe ⊆ insert e I ∧
  e ∈ cdii hI hIe ∧ ∀ c', c' ∈ circuits_circ_of_indep m →
  c' ⊆ insert e I → c' = cdii hI hIe  :=
encodable.choose_spec (existsu_circuit_of_dep_of_insert_indep hI hIe)
--set_option trace.class_instances false

end encodable

-- § 1.2

def is_basis (x : finset α) (m : indep α) : Prop :=
x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)

instance decidable_basis (x : finset α) (m : indep α) : decidable (is_basis x m) :=
decidable_of_iff (x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)) $ by simp [is_basis]

/-- Lemma 1.2.1 -/
theorem bases_of_indep_card_eq {x y : finset α} {m : indep α} : is_basis x m → is_basis y m →
  card x = card y :=
begin
  intros hx hy,
  by_contra heq,
  wlog h : card x < card y using [x y, y x],
  exact lt_or_gt_of_ne heq,
  unfold is_basis at *,
  exact exists.elim (m.indep_exch hx.1 hy.1 h) (λ e ⟨he1, he2⟩,
    have hememx : e ∉ x := (mem_sdiff.mp he1).2,
    (hx.2 (insert e x) $ ssubset_insert hememx) he2)
end

theorem exists_basis_containing_indep {I : finset α} {m : indep α} (h : I ∈ m.indep) :
  ∃ B : finset α, I ⊆ B ∧ is_basis B m :=
let F := (m.indep).filter (λ a, I ⊆ a) in
have FI : I ∈ F := mem_filter.mpr ⟨h, subset.refl I⟩,
exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem FI) $
  λ B HB, exists.elim HB $ by { clear HB, intros HBF Hg, simp at HBF,
    have hBB : is_basis B m := ⟨HBF.1, λ y hBy hyI,
      have hxsy : I ⊆ y := le_of_lt $ lt_of_le_of_lt (le_iff_subset.mpr HBF.2) $
        lt_iff_ssubset.mpr hBy,
      have hyF : y ∈ F := mem_filter.mpr ⟨hyI, hxsy⟩,
      lt_irrefl (card B) $ lt_of_lt_of_le (card_lt_card hBy) $ Hg y hyF⟩,
    exact exists.intro B ⟨HBF.2, hBB⟩ }

section encodable
variable [encodable α]

def basis_containing_indep {I : finset α} {m : indep α} (h : I ∈ m.indep) :
  finset α :=
encodable.choose $ exists_basis_containing_indep h

local notation `bci` := basis_containing_indep

def basis_containing_indep_spec {I : finset α} {m : indep α} (h : I ∈ m.indep) :
  I ⊆ bci h ∧ is_basis (bci h) m :=
encodable.choose_spec $ exists_basis_containing_indep h

end encodable

theorem dep_of_card_gt_card_basis {x B : finset α} {m : indep α} (hB : is_basis B m)
  (hcard : card B < card x) : x ∉ m.indep :=
λ hxI, exists.elim (exists_basis_containing_indep hxI) $ λ B' hB',
  ne_of_lt (lt_of_lt_of_le hcard $ card_le_of_subset hB'.1) $ bases_of_indep_card_eq hB hB'.2

theorem card_of_indep_le_card_basis {x B : finset α} {m : indep α} (hx : x ∈ m.indep)
  (hB : is_basis B m) : card x ≤ card B :=
by by_contra h; exact dep_of_card_gt_card_basis hB (lt_of_not_ge h) hx

variable (α)
structure bases :=
(bases : finset (finset α))
-- (B1)
(bases_not_empty : bases ≠ ∅)
-- (B2)
(basis_exch {x y e} (hx : x ∈ bases) (hy : y ∈ bases) (he : e ∈ x \ y)
    : ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ bases)
--attribute [class] bases

instance bases_repr [has_repr α] (E : finset α) : has_repr (bases α) :=
⟨λ b, has_repr.repr b.bases⟩

variable {α}
theorem eq_of_base_eq : ∀ {B₁ B₂ : bases α}, B₁.1 = B₂.1 → B₁ = B₂
  | ⟨b₁, p₁, q₁⟩ ⟨b₂, p₂, q₂⟩ h :=
by simpa

def bases_bases_of_indep (m : indep α) : finset (finset α) :=
(powerset univ).filter (λ S, is_basis S m)

lemma B1_of_indep (m : indep α) : bases_bases_of_indep m ≠ ∅ :=
by simp [is_basis, ext, bases_bases_of_indep];
exact λ h, exists.elim (max_fun_of_ne_empty card $ ne_empty_of_mem m.empty_mem_indep)
  (λ a ha, exists.elim ha $ λ ha1 hg, (h a (subset_univ a) ha1) $
    λ F Fcontainsa Findep, not_le_of_lt (card_lt_card Fcontainsa) $ hg F Findep)

/- Lemma 1.2.2 -/
lemma B2_of_indep (m : indep α) : ∀ (x y : finset α) (e : α), x ∈ bases_bases_of_indep m →
  y ∈ bases_bases_of_indep m → e ∈ x \ y →
  ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ bases_bases_of_indep m :=
by simp [is_basis, bases_bases_of_indep];
exact λ x y e hxE hxI hx hyE hyI hy hex hey,
  have hxr : erase x e ∈ m.indep := m.indep_of_subset_indep hxI $ erase_subset e x,
  have hxB : is_basis x m := ⟨hxI, hx⟩, have hyB : is_basis y m := ⟨hyI, hy⟩,
  have hcard : card (erase x e) < card y := calc
    card (erase x e) < card x : card_lt_card $ erase_ssubset hex
    ... = card y : bases_of_indep_card_eq hxB hyB,
  exists.elim (m.indep_exch hxr hyI hcard) $
    by { clear hxr hyI hcard hyB, intros a ha,
      have ha1 := mem_sdiff.mp ha.1,
      have hae : a ≠ e := λ hae, hey $ hae ▸ ha1.1,
      have hax : a ∉ x := by simp at ha1; exact ha1.2 hae,
      have hcx : card x > 0 := card_pos.mpr (ne_empty_of_mem hex),
      have hayycard : card (insert a $ erase x e) = card x := calc
        card (insert a $ erase x e) = nat.pred (card x) + 1 : by rw [card_insert_of_not_mem ha1.2,
            card_erase_of_mem hex]
        ... = card x : nat.succ_pred_eq_of_pos hcx,
      exact exists.intro a ⟨⟨ha1.1, hax⟩, subset_univ (insert a (erase x e)), ha.2,
        λ _ hayy, dep_of_card_gt_card_basis hxB $ hayycard ▸ (card_lt_card hayy)⟩ }

def bases_of_indep (m : indep α) : bases α :=
⟨bases_bases_of_indep m,
B1_of_indep m,
B2_of_indep m⟩

/-- Lemma 1.2.4 -/
theorem bases_card_eq {x y : finset α} {b : bases α} (hx : x ∈ b.bases) (hy : y ∈ b.bases) :
  card x = card y :=
begin
  by_contra heq,
  wlog h : card y < card x using [x y, y x],
  exact lt_or_gt_of_ne (ne.symm heq), clear heq,
  let F : finset (finset α × finset α) := (finset.product b.bases b.bases).filter
    (λ e : finset α × finset α, card e.1 < card e.2),
  have hyx : (y, x) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, h⟩, clear hy hx,
  exact exists.elim (min_fun_of_ne_empty (λ f : finset α × finset α, card (f.2 \ f.1)) $
      ne_empty_of_mem hyx)
    (λ a ha, exists.elim ha $ by { clear hyx ha,
      intros haF Ha, replace haF := mem_filter.mp haF,
      have hab : a.1 ∈ b.bases ∧ a.2 ∈ b.bases := mem_product.mp haF.1,
      exact exists.elim (exists_sdiff_of_card_lt haF.2)
        (λ e he, exists.elim (b.basis_exch hab.2 hab.1 he) $ λ aa ⟨haa1, haa2⟩,
          by { simp at haa1,
          let a2 : finset α := insert aa (erase a.2 e),
          have haani : aa ∉ erase a.2 e := λ h, haa1.2 (mem_erase.mp h).2,
          have hea2 : e ∈ a.2 := (mem_sdiff.mp he).1,
          have hpos : 0 < card a.2 := card_pos.mpr (ne_empty_of_mem hea2),
          have hcarda2 : card a.1 < card a2 := by rw [card_insert_of_not_mem haani,
            card_erase_of_mem hea2, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos hpos];
            exact haF.2, clear haani hpos,
          have : e ∉ a2 := λ hh, or.elim (mem_insert.mp hh)
            (λ h4, haa1.2 $ h4 ▸ hea2) $ λ h5, (mem_erase.mp h5).1 rfl,
          have hcard : card (a2 \ a.1) < card (a.2 \ a.1) :=
            suffices a2 \ a.1 ⊂ a.2 \ a.1, from card_lt_card this,
            by rw ssubset_iff;
            exact exists.intro e ⟨λ h0, this (mem_sdiff.mp h0).1,
              by { rw subset_iff,
              intros A hA, rw mem_insert at hA,
              exact or.elim hA (λ hA1, hA1.symm ▸ he)
                (by { intro hA2, rw [mem_sdiff, mem_insert] at hA2,
                exact mem_sdiff.mpr ⟨or.elim hA2.1 (λ h6, false.elim $ hA2.2 $ h6.symm ▸ haa1.1) $
                  λ h7, (mem_erase.mp h7).2, hA2.2⟩ }) }⟩,
          have ha2F : (a.1, a2) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hab.1, haa2⟩, hcarda2⟩,
          exact not_le_of_lt hcard (Ha (a.1, a2) ha2F) }) })
end

def indep_indep_of_bases (b : bases α) : finset (finset α) :=
(powerset univ).filter (λ x, ∃ a ∈ b.bases, x ⊆ a)

/-- first part of Theorem 1.2.3 -/
def indep_of_bases (b : bases α) : indep α :=
⟨indep_indep_of_bases b,
mem_filter.mpr ⟨empty_mem_powerset univ, exists.elim (exists_mem_of_ne_empty b.bases_not_empty) $
    λ a ha, exists.intro a $ exists.intro ha $ empty_subset a⟩,
begin
  intros x y hx hxy, simp [indep_indep_of_bases] at *,
  exact ⟨subset.trans hxy hx.1,
    exists.elim hx.2 $ λ a ha, exists.intro a ⟨ha.1, subset.trans hxy ha.2⟩⟩
end,
begin
  intros x y hx hy hcard, unfold indep_indep_of_bases at *,
  let F := (b.bases).filter (λ S, S ⊆ y),
  by_contra h, simp at *,
  exact exists.elim hx.2 (λ b1 hb1, exists.elim hy.2 $ λ b2 hb2, exists.elim
    (min_fun_of_ne_empty (λ f, card (f \ (y ∪ b1))) $ ne_empty_of_mem $ mem_filter.mpr hb2) $
    λ B2 hEB2, exists.elim hEB2 $ by { clear hb2 b2 hEB2,
      intros hB2filt hB2min, replace hB2filt : B2 ∈ b.bases ∧ y ⊆ B2 := mem_filter.mp hB2filt,
      have hysdiff : y \ b1 = y \ x := by simp [ext];
        exact λ gg, ⟨λ hgg, ⟨hgg.1, λ hggnx, hgg.2 $ mem_of_subset hb1.2 hggnx⟩,
          λ hgg, ⟨hgg.1, λ ggb1, h gg hgg.1 hgg.2 (insert_subset.mpr
          ⟨mem_of_subset hy.1 hgg.1, hx.1⟩) b1 hb1.1 $ insert_subset.mpr ⟨ggb1, hb1.2⟩⟩⟩,
      have hB2yub1: B2 \ (y ∪ b1) = ∅ := by by_contra H;
        exact exists.elim (exists_mem_of_ne_empty H) (by { clear H,
          intros X hX, simp [not_or_distrib] at hX,
          have hXB2b1 : X ∈ B2 \ b1 := by simp; exact ⟨hX.1, hX.2.2⟩,
          exact exists.elim (b.basis_exch hB2filt.1 hb1.1 hXB2b1)
            (λ Y ⟨hYb1B2, hYbases⟩, by { simp at hYb1B2 hXB2b1,
              have hssubY : insert Y (erase B2 X) \ (y ∪ b1) ⊂  B2 \ (y ∪ b1) :=
                by rw [ssubset_iff];
                exact exists.intro X (by simp [subset_iff, not_or_distrib];
                  exact ⟨λ hXY, false.elim $ hYb1B2.2 (hXY ▸ hXB2b1.1),
                  λ gg hgg, or.elim hgg (λ ggx, ggx.symm ▸ hX) $ λ ggor2, or.elim ggor2.1
                    (λ ggY, false.elim $ (ggY ▸ ggor2.2.2) hYb1B2.1) $
                      λ ggXB2, ⟨ggXB2.2, ggor2.2⟩⟩),
              replace hssubY := card_lt_card hssubY,
              have hysubY : y ⊆ insert Y (erase B2 X) := by simp [subset_iff];
                exact λ gg hgg, or.inr ⟨λ ggx, hX.2.1 $ ggx ▸ hgg, mem_of_subset hB2filt.2 hgg⟩,
              exact not_lt_of_le (hB2min (insert Y $ erase B2 X) $ mem_filter.mpr
                  ⟨hYbases, hysubY⟩) hssubY }) }), clear hB2min,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hB2yub1, simp at hB2yub1,
      have hB2b1y : B2 \ b1 = y \ b1 := by simp [ext];
        exact λ gg, ⟨λ hgg, ⟨or.elim (hB2yub1 hgg.1) id $ λ hb1, false.elim $ hgg.2 hb1, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hB2filt.2 hgg.1, hgg.2⟩⟩,
      rw [hysdiff] at hB2b1y, clear hysdiff,
      have hb1xuB2 : b1 \ (x ∪ B2) = ∅ := by by_contra H;
        exact exists.elim (exists_mem_of_ne_empty H)
          (by { intros X hX, simp [not_or_distrib] at hX,
          exact exists.elim (b.basis_exch hb1.1 hB2filt.1 $ mem_sdiff.mpr ⟨hX.1, hX.2.2⟩)
            (by { intros Y hY, simp at hY,
            have hYyx : Y ∈ y ∧ Y ∉ x := mem_sdiff.mp (hB2b1y ▸ (mem_sdiff.mpr hY.1)),
            have hxYsub : insert Y x ⊆ insert Y (erase b1 X) := by simp [subset_iff];
              exact λ gg hgg, or.elim hgg (λ ggY, or.inl ggY) $ λ ggx, or.inr ⟨λ ggX, hX.2.1 $
                ggX ▸ ggx, mem_of_subset hb1.2 ggx⟩,
            exact h Y hYyx.1 hYyx.2 (subset_univ (insert Y x)) (insert Y $ erase b1 X)
              hY.2 hxYsub }) }),
      clear h hx hy,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hb1xuB2, simp at hb1xuB2,
      have hb1B2 : b1 \ B2 = x \ B2 := by simp [ext];
        exact λ gg, ⟨λ hgg, ⟨or.elim (hb1xuB2 hgg.1) id $ λ ggB2, false.elim $ hgg.2 ggB2, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hb1.2 hgg.1, hgg.2⟩⟩, clear hb1xuB2,
      replace hb1B2 : b1 \ B2 ⊆ x \ y := hb1B2.symm ▸ (sdiff_subset_sdiff (subset.refl x)
          hB2filt.2),
      have hcardeq : card b1 = card B2 := bases_card_eq hb1.1 hB2filt.1,
      have hcardb1B2 : card (b1 \ B2) = card (B2 \ b1) := calc
        card (b1 \ B2) = card b1 - card (b1 ∩ B2) : card_sdiff b1 B2
        ... = card B2 - card (B2 ∩ b1) : by rw [hcardeq, inter_comm]
        ... = card (B2 \ b1) : by rw ←card_sdiff B2 b1,
      have hcardcontra0 : card (y \ x) ≤ card (x \ y) := calc
        card (y \ x) = card (B2 \ b1) : by rw hB2b1y
        ... = card (b1 \ B2) : by rw hcardb1B2
        ... ≤ card (x \ y) : card_le_of_subset hb1B2,
      rw [card_sdiff y x, card_sdiff x y, inter_comm] at hcardcontra0,
      have hcardcontra : card y ≤ card x := nat.le_of_le_of_sub_le_sub_right
          (card_le_of_subset $ @inter_subset_left _ _ x y) hcardcontra0,
      exact not_lt_of_le hcardcontra hcard })
end⟩

instance base_indep : has_coe (bases α) (indep α) := ⟨indep_of_bases⟩
instance indep_base : has_coe (indep α) (bases α) := ⟨bases_of_indep⟩

/-- second part of Theorem 1.2.3 -/
theorem base_indep_base (B : bases α) : B = bases_of_indep (indep_of_bases B) :=
suffices B.bases = (bases_of_indep $ indep_of_bases B).bases, from eq_of_base_eq this,
by simp [indep_of_bases, bases_of_indep, indep_indep_of_bases, is_basis, ext, bases_bases_of_indep];
exact λ b, iff.intro
  (λ hb, have hB : b ⊆ univ := subset_univ b,
    ⟨hB, ⟨⟨hB, exists.intro b ⟨hb, subset.refl b⟩⟩, λ b' hbb' _ _ hx H,
    (ne_of_lt $ lt_of_lt_of_le (card_lt_card hbb') $ card_le_of_subset H) $ bases_card_eq hb hx⟩⟩) $
  λ hb, exists.elim hb.2.1.2 $ λ a ha, have a ⊆ univ := subset_univ a, by { by_cases h : a = b,
      { exact h ▸ ha.1 },
      { have hba : b ⊂ a := lt_iff_ssubset.mp (lt_of_le_of_ne (le_iff_subset.mpr ha.2) $ ne.symm h),
        exact false.elim (hb.2.2 a hba this a ha.1 $ subset.refl a) } }

theorem indep_base_indep (M : indep α) : M = indep_of_bases (bases_of_indep M) :=
suffices M.indep = (indep_of_bases $ bases_of_indep M).indep, from eq_of_indep_eq this,
by simp [indep_of_bases, bases_of_indep, indep_indep_of_bases, is_basis, ext, bases_bases_of_indep];
exact λ I, iff.intro (λ hI, ⟨subset_univ I,
  exists.elim (exists_basis_containing_indep hI) $ λ B hB, by unfold is_basis at hB;
    exact exists.intro B ⟨⟨subset_univ B, hB.2⟩, hB.1⟩⟩) $ λ hI, exists.elim hI.2 $
      λ B hB, M.indep_of_subset_indep hB.1.2.1 hB.2

/-- Corollary 1.2.6 -/
theorem existsu_fund_circ_of_basis {m : indep α} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ univ \ B) : ∃ C, C ∈ circuits_circ_of_indep m ∧ C ⊆ insert e B ∧
  ∀ C' ∈ circuits_circ_of_indep m, C' ⊆ insert e B → C' = C :=
begin
  unfold is_basis at hB, simp at he,
  have : insert e B ∉ m.indep := hB.2 (insert e B) (ssubset_insert he),
  replace := existsu_circuit_of_dep_of_insert_indep hB.1 this,
  exact exists.elim this (λ C ⟨hCcirc, HC⟩, exists.intro C $
    ⟨hCcirc, ⟨HC.1, λ C' hC'circ hC', HC.2.2 C' hC'circ hC'⟩⟩)
end

section encodable

def fund_circ_of_basis [encodable α] {m : indep α} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ univ \ B) : finset α :=
encodable.choose (existsu_fund_circ_of_basis hB he)

def fund_circ_of_basis_spec [encodable α] {m : indep α} {B : finset α} (hB : is_basis B m) {e : α}
  (he : e ∈ univ \ B) : fund_circ_of_basis hB he ∈ circuits_circ_of_indep m ∧
  fund_circ_of_basis hB he  ⊆ insert e B ∧ ∀ C' ∈ circuits_circ_of_indep m, C' ⊆ insert e B →
  C' = fund_circ_of_basis hB he :=
encodable.choose_spec (existsu_fund_circ_of_basis hB he)

end encodable

-- § 1.3

def finset_embed {X : finset α} (S : finset {x // x ∈ X}) : finset α :=
S.map $ function.embedding.subtype _

lemma finset_embed_inj {X : finset α} : function.injective
  (λ (S : finset {x // x ∈ X}), finset_embed S):=
begin
  unfold function.injective,
  intros S T h,
  simp [ext] at h ⊢,
  intros a ha,
  simp [finset_embed, function.embedding.subtype] at h,
  exact iff.intro (λ H, exists.elim ((h a).mp (exists.intro ha H)) (λ ha_, id))
    (λ H, exists.elim ((h a).mpr (exists.intro ha H)) (λ ha_, id))
end

instance finset_embed_coe (X : finset α) : has_coe (finset {x : α // x ∈ X}) (finset α) :=
⟨finset_embed⟩

instance finset_finset_embed_coe (X : finset α) : has_coe (finset (finset {x : α // x ∈ X}))
  (finset (finset α)) :=
⟨λ (S : finset (finset {a // a ∈ X})), S.map $ ⟨finset_embed, finset_embed_inj⟩⟩

lemma finset_embed_coe_def {X : finset α} (S : finset {x // x ∈ X}) : ↑S = finset_embed S :=
rfl

/-lemma finset_embed_mem_univ {X : finset α} (x : finset {a // a ∈ X}) : (↑x : α) ∈ X :=
begin
end-/

lemma finset_embed_subset_univ {X : finset α} (S : finset {a // a ∈ X}) : ↑S ⊆ X :=
by simp [subset_iff, finset_embed_coe_def, finset_embed, function.embedding.subtype];
exact λ _ ha _, ha

lemma finset_embed_mem {X : finset α} {S : finset {a : α // a ∈ X}} {x : {a : α // a ∈ X}} :
  x ∈ S ↔ x.val ∈ (↑S : finset α) :=
by simp [finset_embed_coe_def, finset_embed, function.embedding.subtype];
  exact iff.intro (λ h, ⟨x.2, mem_def.mp h⟩) (λ h, h.2)

/-lemma finset_embed_finset_mem {X : finset α} {S : finset (finset {a : α // a ∈ X})}
  {x : finset {a : α // a ∈ X}} : x ∈ S ↔ ↑x ∈ (↑S) :=
sorry-/
/-
lemma aux : insert e ↑x = ↑(insert e x) := sorry-/

lemma finset_embed_subset {X : finset α} {x y : finset {a // a ∈ X}} :
  x ⊆ y ↔ ↑x ⊆ (↑y : finset α) :=
by simp [subset_iff, finset_embed_coe_def, finset_embed, function.embedding.subtype];
  exact iff.intro (λ h a ha H, exists.intro ha (h a ha H))
    (λ h a ha H, exists.elim (h ha H) (λ ha_ hay, hay))

lemma finset_embed_card {X : finset α} (x : finset {a // a ∈ X}) : card x = card (↑x : finset α) :=
by rw [finset_embed_coe_def, finset_embed];
exact (map_eq_image (function.embedding.subtype _) x).symm ▸
  (card_image_of_injective x (function.embedding.subtype _).2).symm

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134578668 -/
def indep_of_restriction (m : indep α) (X : finset α) : finset (finset {x : α // x ∈ X}) :=
(m.indep).filter_map $ λ I, if h : _ then some
  ⟨I.1.pmap (λ x h', ⟨x, h'⟩) h,
    multiset.nodup_pmap (λ _ _ _ _, subtype.mk_eq_mk.1) I.2⟩ else none

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134721936 -/
def {u v} indep.filter_map {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β]
  [fintype α] [fintype β] (f : α → option β) (m : indep α) : indep β :=
{ indep := m.indep.image (filter_map f),
  empty_mem_indep := mem_image.2 ⟨∅, m.empty_mem_indep, rfl⟩,
  indep_of_subset_indep := λ x y, begin
    rw [mem_image, mem_image],
    rintro ⟨x, hx, rfl⟩ xy,
    refine ⟨x.filter (λ a, ∃ b ∈ f a, b ∈ y),
      m.indep_of_subset_indep hx (filter_subset _), _⟩,
    ext b, simp; split,
    { rintro ⟨a, ⟨ha, b', hb', hy⟩, hb⟩,
      rcases option.some_inj.1 (hb.symm.trans hb'),
      exact hy },
    { intro hb,
      rcases mem_filter_map.1 (xy hb) with ⟨a, ha, ab⟩,
      exact ⟨a, ⟨ha, b, ab, hb⟩, ab⟩ }
  end,
  indep_exch := λ x y, begin
    rw [mem_image, mem_image],
    rintro ⟨x, xi, rfl⟩ ⟨y, yi, rfl⟩ xy,
    rcases exists_subset_filter_map_eq f x with ⟨z, zx, hz, cz⟩,
    rcases exists_subset_filter_map_eq f y with ⟨w, wy, hw, cw⟩,
    have zi := m.indep_of_subset_indep xi zx,
    have wi := m.indep_of_subset_indep yi wy,
    rw [hz, cz, hw, cw] at xy, rw [hz, hw], clear xi zx hz x yi wy hw y,
    induction h : card (w \ z) generalizing z,
    { have := ext.1 (card_eq_zero.1 h), simp at this,
      exact (not_le_of_gt xy (card_le_of_subset this)).elim },
    rcases m.indep_exch zi wi xy with ⟨a, ha, ii⟩, simp at ha,
    rcases mem_of_card_filter_map cw ha.1 with ⟨b, ab⟩,
    by_cases bz : b ∈ filter_map f z,
    { rcases mem_filter_map.1 bz with ⟨a', ha', fa'⟩,
      let z' := erase (insert a z) a',
      have az' : a ∈ z',
      { refine mem_erase.2 ⟨mt _ ha.2, mem_insert_self _ _⟩,
        rintro rfl, exact ha' },
      have inz : insert a' z' = insert a z,
      { rw [insert_erase (mem_insert_of_mem ha')] },
      have zi' : z' ∈ m.indep :=
        m.indep_of_subset_indep ii (erase_subset _ _),
      have bz' : b ∈ filter_map f z' :=
        mem_filter_map.2 ⟨a, az', ab⟩,
      have hz' : z'.filter_map f = z.filter_map f,
      { rw [← insert_eq_of_mem bz', ← filter_map_insert_some f fa',
          inz, filter_map_insert_some f ab, insert_eq_of_mem bz] },
      have cz' : card z' = card z,
      { rw [← add_right_inj 1, ← card_insert_of_not_mem (not_mem_erase _ _),
          inz, card_insert_of_not_mem ha.2] },
      replace ih := ih z', rw [hz', cz'] at ih,
      refine ih cz zi' xy ((add_right_inj 1).1 $ eq.trans _ h),
      rw [← card_insert_of_not_mem (λ h, (mem_sdiff.1 h).2 az')],
      congr, ext c, simp [not_imp_comm]; split,
      { rintro (rfl | ⟨h₁, h₂⟩),
        { exact ha },
        { refine ⟨h₁, λ h₃, h₂ (λ h₄, _) (or.inr h₃)⟩,
          subst c,
          rcases inj_of_card_filter_map cw ha.1 h₁ ab fa',
          exact ha.2 h₃ } },
      { rintro ⟨h₁, h₂⟩,
        refine or_iff_not_imp_left.2 (λ h₃, ⟨h₁, _⟩),
        rintro h₄ (rfl | h₅),
        { exact h₃ rfl }, { exact h₂ h₅ } } },
    { exact ⟨b, mem_sdiff.2 ⟨mem_filter_map.2 ⟨_, ha.1, ab⟩, bz⟩,
        mem_image.2 ⟨_, ii, by rw [filter_map_insert_some f ab]⟩⟩ },
  end }

lemma mem_restriction {m : indep α} {X : finset α} {x : finset {y : α // y ∈ X}} :
x ∈ indep_of_restriction m X ↔ ↑x ∈ m.indep /-∧ ↑x ⊆ X -- just use finset_embed_subset_univ -/ :=
begin
  simp [indep_of_restriction, filter_map, finset_embed_coe_def, finset_embed,
    function.embedding.subtype, map_eq_image],
  split,
  { intro h,
  exact exists.elim h (by {
    intros a ha,
    have := m.indep.val,
    sorry
  })
  },
  sorry
end

def restriction (m : indep α) (X : finset α) : indep {x : α // x ∈ X} :=
⟨indep_of_restriction m X,
mem_restriction.mpr m.empty_mem_indep,
λ x y hx hyx, have hx' : ↑x ∈ m.indep := mem_restriction.mp hx,
  have hyx' : ↑y ⊆ (↑x : finset α) := finset_embed_subset.mp hyx,
  mem_restriction.mpr (m.indep_of_subset_indep hx' hyx'),
by { intros x y hx hy hcard,
  have hx' : _ := mem_restriction.mp hx, have hy' : _ := mem_restriction.mp hy,
  have hcard' : card (↑x : finset α) < card ↑y := calc
    card (↑x : finset α) = card x : (finset_embed_card x).symm
    ... < card y : hcard
    ... = card ↑y : finset_embed_card y,
  have H : _ := m.indep_exch hx' hy' hcard',
  exact exists.elim H (by { intros e he, simp at he,
    have He : e ∈ X := mem_of_subset (finset_embed_subset_univ y) he.1.1,
    let e' := subtype.mk e He,
    have heyx : e' ∈ y \ x := mem_sdiff.mpr ⟨finset_embed_mem.mpr he.1.1,
      λ H, he.1.2 $ finset_embed_mem.mp H⟩,
    have heinsert : ↑(insert e' x) ∈ m.indep :=
      by { have : (↑(insert e' x) : finset α) = insert e ↑x :=
        by simp [ext, finset_embed_coe_def, finset_embed, function.embedding.subtype],
      exact this.symm ▸ he.2 },
    have H : insert e' x ∈ indep_of_restriction m X :=
      mem_restriction.mpr heinsert,
    exact exists.intro e' ⟨heyx, H⟩
  })}⟩

-- what about {x : α // x ∉ X} ?
def deletion (m : indep α) (X : finset α) : indep {x : α // x ∈ univ \ X} :=
restriction m (univ \ X)

notation m `¦` hxe := restriction m hxe
notation m `\` hxe := deletion m hxe

lemma restriction_subset_restriction (X : finset α) (m : indep α) :
  ↑(m ¦ X).indep ⊆ m.indep :=
by { simp [restriction, subset_iff, mem_restriction],  }

#exit

lemma restriction_trans {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ E) (m : indep E) :
  (m ¦ subset.trans hXY hY) = ((m ¦ hY) ¦ hXY) :=
by simp [restriction, indep_of_restriction, ext];
exact λ I, iff.intro (λ h, ⟨⟨h.1, subset.trans h.2 hXY⟩, h.2⟩) $ λ h, ⟨h.1.1, h.2⟩

lemma subset_restriction_indep {X Y : finset α} {m : indep E} (hX : X ∈ m.indep) (hXY : X ⊆ Y)
  (hY : Y ⊆ E) : X ∈ (m ¦ hY).indep :=
by simp [restriction, indep_of_restriction]; exact ⟨hX, hXY⟩

/-def spans (X : finset α) {Y : finset α} (hY : Y ⊆ E) (m : indep E) : Prop :=
X ∈ bases_bases_of_indep (m ¦ hY)-/

lemma exists_basis_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) :
  ∃ B, B ∈ bases_bases_of_indep (m ¦ hXE) :=
exists_mem_of_ne_empty $ B1_of_indep (m ¦ hXE)

/-lemma inter_of_span_of_subset_span {m : indep E} {X Y bX bY : finset α} {hXE : X ⊆ E}
  (hbX : spans bX hXE m) {hYE : Y ⊆ E} (hbY : spans bY hYE m) (hbXbY : bX ⊆ bY) : bY ∩ X = bX :=
sorry-/

section encodable
variable [encodable α]

def basis_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) : finset α :=
encodable.choose $ exists_basis_of_subset hXE m

def basis_of_subset_spec {X : finset α} (hXE : X ⊆ E) (m : indep E) :
  basis_of_subset hXE m ∈ bases_bases_of_indep (m ¦ hXE) :=
encodable.choose_spec $ exists_basis_of_subset hXE m

notation `𝔹` := basis_of_subset
notation `𝔹ₛ` := basis_of_subset_spec

def rank_of_subset {X : finset α} (hXE : X ⊆ E) (m : indep E) : ℕ :=
card $ 𝔹 hXE m

notation `𝓇` := rank_of_subset

lemma R2_of_indep (m : indep E) {X Y : finset α} (hXY : X ⊆ Y) (hYE : Y ⊆ E) :
  𝓇 (subset.trans hXY hYE) m ≤ 𝓇 hYE m :=
let hXE : X ⊆ E := subset.trans hXY hYE in let bX := 𝔹 hXE m in let bY := 𝔹 hYE m in
have bXs : _ := 𝔹ₛ hXE m, have bYs : _ := 𝔹ₛ hYE m,
by simp [bases_bases_of_indep] at bXs bYs; unfold rank_of_subset;
have hBX : bX ∈ (m ¦ hYE).indep := mem_of_subset (restriction_subset_restriction hXY (m ¦ hYE))
  ((restriction_trans hXY hYE m) ▸ bXs.2.1);
exact exists.elim (exists_basis_containing_indep hBX) (λ B hB, calc
  card bX ≤ card B : card_le_of_subset hB.1
  ... = card bY : bases_of_indep_card_eq hB.2 bYs.2)

/-- Lemma 1.3.1 -/
lemma R3_of_indep (m : indep E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) :
  𝓇 (union_subset hX hY) m +
  𝓇 (subset.trans (@inter_subset_left _ _ X Y) hX) m ≤
  𝓇 hX m + 𝓇 hY m :=
begin
  have hXXuY : X ⊆ X ∪ Y := @subset_union_left _ _ X Y,
  have hYXuY : Y ⊆ X ∪ Y := @subset_union_right _ _ X Y,
  have hXiYX : X ∩ Y ⊆ X := @inter_subset_left _ _ X Y,
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  have hXiY : X ∩ Y ⊆ E := subset.trans hXiYX hX,
  let bXuY := 𝔹 hXuY m, let bXiY := 𝔹 hXiY m,
  let bX := 𝔹 hX m, let bY := 𝔹 hY m,
  unfold rank_of_subset,
  have bXuYs := 𝔹ₛ hXuY m, have bXiYs := 𝔹ₛ hXiY m,
  have bXs := 𝔹ₛ hX m, have bYs := 𝔹ₛ hY m,
  simp [bases_bases_of_indep] at bXuYs bXiYs bXs bYs,
  have rXiY : 𝓇 hXiY m = card bXiY := by simp [rank_of_subset],
  have hiu : X ∩ Y ⊆ X ∪ Y := subset.trans hXiYX hXXuY,
  have hbXiY : bXiY ∈ (m ¦ hXuY).indep := mem_of_subset
    (restriction_subset_restriction hiu (m ¦ hXuY)) ((restriction_trans hiu hXuY m) ▸ bXiYs.2.1),
  have HbbXiY := exists_basis_containing_indep hbXiY,
  exact exists.elim HbbXiY (by { intros B hB,
    have rXuY : 𝓇 hXuY m = card B := by simp [rank_of_subset];
      exact bases_of_indep_card_eq bXuYs.2 hB.2,
    have hBXuY : B ⊆ X ∪ Y := mem_powerset.mp ((m ¦ hXuY).indep_subset_powerset_ground hB.2.1),
    have hBX : B ∩ X ∈ (m ¦ hX).indep := have hsub : _ := restriction_trans hXXuY hXuY m,
      have hBX : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ @inter_subset_left _ _ B X),
      hsub.symm ▸ (subset_restriction_indep hBX (@inter_subset_right _ _ B X) hXXuY),
    have hBY : B ∩ Y ∈ (m ¦ hY).indep := have hsub : _ := restriction_trans hYXuY hXuY m,
      have hBY : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ @inter_subset_left _ _ B Y),
      hsub.symm ▸ (subset_restriction_indep hBY (@inter_subset_right _ _ B Y) hYXuY),
    have hBXr : card (B ∩ X) ≤ 𝓇 hX m := by unfold rank_of_subset;
      exact card_of_indep_le_card_basis hBX bXs.2,
    have hBYr : card (B ∩ Y) ≤ 𝓇 hY m := by unfold rank_of_subset;
      exact card_of_indep_le_card_basis hBY bYs.2,
    have hinter : (B ∩ X) ∩ (B ∩ Y) = B ∩ X ∩ Y := by simp,
    have hBXiY : B ∩ X ∩ Y = bXiY :=
      by { have hsub : B ∩ X ∩ Y ⊆ bXiY :=
        by { by_contra h,
        exact exists.elim (exists_mem_of_ne_empty $ (mt subset_iff_sdiff_eq_empty.mpr) h)
          (by { intros a ha, rw [mem_sdiff, inter_assoc, mem_inter] at ha, unfold is_basis at bXiYs,
          have := ssubset_insert ha.2,
          have hbXiYsubXiY : insert a bXiY ⊆ X ∩ Y:= insert_subset.mpr ⟨ha.1.2, bXiYs.1⟩,
          have hrestrict : (m ¦ hXiY) = (m ¦ hXuY ¦ hiu) := restriction_trans hiu hXuY m,
          have hindep : insert a bXiY ∈ (m ¦ hXiY).indep := hrestrict.symm ▸
            (subset_restriction_indep ((m ¦ hXuY).indep_of_subset_indep hB.2.1
            $ insert_subset.mpr ⟨ha.1.1, hB.1⟩) hbXiYsubXiY hiu),
          exact bXiYs.2.2 (insert a bXiY) hbXiYsubXiY this hindep }) },
      have hsuper : bXiY ⊆ B ∩ X ∩ Y :=
        by { rw [inter_assoc],
        have := inter_subset_inter_of_subset hB.1 (X ∩ Y),
        have h : bXiY ∩ (X ∩ Y) = bXiY := inter_of_subset bXiYs.1,
        exact h ▸ this },
      exact subset.antisymm hsub hsuper },
    exact calc 𝓇 hX m + 𝓇 hY m ≥ card (B ∩ X) + card (B ∩ Y) : add_le_add hBXr hBYr
    ... = card ((B ∩ X) ∪ (B ∩ Y)) + card ((B ∩ X) ∩ (B ∩ Y)) : card_union_inter (B ∩ X) (B ∩ Y)
    ... = card (B ∩ (X ∪ Y)) + card (B ∩ X ∩ Y) : by rw [←inter_distrib_left, hinter]
    ... = card B + card bXiY : by rw [inter_of_subset hBXuY, hBXiY]
    ... = 𝓇 hXuY m + 𝓇 hXiY m : by rw [rXuY, rXiY] })
end

end encodable

structure rank (ground : finset α) :=
(r {X : finset α} (hX : X ⊆ ground) : ℕ)
-- (R1)
(bounded {X : finset α} (hX : X ⊆ ground) : 0 ≤ r hX ∧ r hX ≤ card X)
-- (R2)
(order_preserving {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ ground) : r (subset.trans hXY hY) ≤ r hY)
-- (R3)
(submodular {X Y : finset α} (hX : X ⊆ ground) (hY : Y ⊆ ground) :
r (union_subset hX hY) + r (subset.trans (@inter_subset_left _ _ X Y) hX) ≤ r hX + r hY)

section encodable
variable [encodable α]

def rank_of_indep (m : indep E) : rank E :=
⟨λ X hX, rank_of_subset hX m,
λ X hX, ⟨dec_trivial, (by { have := basis_of_subset_spec hX m, simp [bases_bases_of_indep] at this,
  exact card_le_of_subset this.1 })⟩,
λ X Y hXY hY, R2_of_indep m hXY hY,
λ X Y hX hY, R3_of_indep m hX hY⟩

end encodable

structure rank_R2_R3 (ground : finset α) :=
(r {X : finset α} (hX : X ⊆ ground) : ℕ)
-- (R2)
(order_preserving {X Y : finset α} (hXY : X ⊆ Y) (hY : Y ⊆ ground) : r (subset.trans hXY hY) ≤ r hY)
-- (R3)
(submodular {X Y : finset α} (hX : X ⊆ ground) (hY : Y ⊆ ground) :
r (union_subset hX hY) + r (subset.trans (@inter_subset_left _ _ X Y) hX) ≤ r hX + r hY)

lemma congr_for_rank (rk : rank_R2_R3 E ) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) (h : X = Y) :
rk.r hX = rk.r hY :=
by congr; exact h

-- Lemma 1.3.3
lemma rank_union_lemma (rk : rank_R2_R3 E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E)
  (hy : ∀ y, ∀ (h : y ∈ Y \ X), rk.r (by { simp at h,
    exact insert_subset.mpr ⟨mem_of_subset hY h.1, hX⟩ }) = rk.r hX) :
  rk.r (union_subset hX hY) = rk.r hX :=
begin
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  induction h : (Y \ X) using finset.induction with a S ha ih generalizing X Y,
  { congr, have H := congr_arg (λ x, X ∪ x) h, simp at H,
    exact (union_eq_union_sdiff X Y).symm ▸ H },
  { have h₁ : rk.r hX + rk.r hX ≥ rk.r hXuY + rk.r hX :=
    by { have haa : a ∈ Y \ X := h.substr (mem_insert_self a S),
    have haX : insert a X ⊆ E := insert_subset.mpr ⟨mem_of_subset hY (mem_sdiff.mp haa).1, hX⟩,
    have hins : insert a S ⊆ E := h ▸ subset.trans (sdiff_subset Y X) hY,
    have hS : S ⊆ E := subset.trans (subset_insert a S) hins,
    have hXS : X ∪ S ⊆ E := union_subset hX hS,
    have hrins : rk.r haX = rk.r hX := hy a haa, simp at haa,
    have hrS : rk.r hXS = rk.r hX := by {
      exact ih hX hS (by { intros y Hy, have : y ∈ Y \ X := by { simp at Hy,
        simp [ext] at h, exact mem_sdiff.mpr ((h y).mpr $ or.inr Hy.1) }, exact hy y this })
        hXS (by simp [ext] at h ⊢; exact λ y, iff.intro (λ Hy, Hy.1)
        $ λ Hy, ⟨Hy, ((h y).mpr $ or.inr Hy).2⟩) },
    have hXuSiaX : (X ∪ S) ∩ insert a X ⊆ E := (subset.trans (@inter_subset_right _ _ (X ∪ S)
      (insert a X)) haX),
    have hr₁ : rk.r (union_subset hXS haX) = rk.r hXuY :=
      by { exact congr_for_rank rk (union_subset hXS haX) hXuY (by simp [ext] at h ⊢;
      exact λ x, iff.intro (λ hx, or.elim hx (λ hxa, or.inr $ hxa.substr haa.1) $
        λ H, or.elim H (by { intro hxS, exact or.inr ((h x).mpr $ or.inr hxS).1}) $
          by {exact (λ hxX, or.inl hxX) }) $
        λ hx, or.elim hx (by {intro hxX, exact or.inr (or.inr hxX)}) $
          by { intro hxY, by_cases hxX : x ∈ X,
            { exact or.inr (or.inr hxX) },
            { exact or.elim ((h x).mp ⟨hxY, hxX⟩) (λ H, or.inl H)
              (λ HS, or.inr $ or.inl HS) } }) },
    have hr₂ : rk.r hXuSiaX = rk.r hX := by congr; simp [ext];
      exact λ x, iff.intro (λ hx, or.elim hx.1 (or.elim hx.2
        (λ H₁ H₂, false.elim $ ha $ H₁.subst H₂) $ λ h _, h) id) (λ hx, ⟨or.inr hx, or.inr hx⟩),
    calc rk.r hX + rk.r hX = rk.r hXS + rk.r haX : by rw [hrS, hrins]
    ... ≥ rk.r (union_subset hXS haX) + rk.r hXuSiaX : rk.submodular (union_subset hX hS) haX
    ... = _ : by rw [hr₁, hr₂] },
  replace h₁ := le_of_add_le_add_right h₁,
  have h₂ : rk.r hX ≤ rk.r hXuY := rk.order_preserving (@subset_union_left _ _ X Y) hXuY,
  exact nat.le_antisymm h₁ h₂ }
end

def indep_of_rank (r : rank E) : indep E :=
⟨sorry,
sorry,
sorry,
sorry,
sorry⟩

end matroid