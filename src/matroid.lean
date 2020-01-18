/-
Matroids, after Chapter 1 of Oxley, Matroid Theory, 1992.
-/
import data.finset tactic.wlog data.equiv.list tactic.find

variables {α : Type*} {β : Type*}
/- For mathlib?: -/
/- Everything from here to inter_of_subsete is by Mario Carneiro:
https://gist.github.com/digama0/edc2a9fe4d468c3921c87650eea5b77a -/
namespace multiset
open nat

@[simp] theorem card_filter_map_le {α β} {f : α → option β}
  (s : multiset α) : card (filter_map f s) ≤ card s :=
multiset.induction_on s (nat.zero_le _) begin
  intros a s IH,
  cases h : f a,
  { rw [filter_map_cons_none _ _ h, card_cons],
    exact le_succ_of_le IH, },
  { rw [filter_map_cons_some _ _ _ h, card_cons, card_cons],
    exact succ_le_succ IH, },
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
by { simp only [filter_map, exists_prop, multiset.mem_filter_map, multiset.mem_to_finset], refl, }

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
  { simp only [filter_map, multiset.ndinsert_of_not_mem h,
      multiset.filter_map_cons_none _ _ hf, finset.insert_val], },
end

theorem filter_map_insert_some {α β} [decidable_eq α] [decidable_eq β]
  (f : α → option β) {a : α} {s : finset α} {b} (hf : f a = some b) :
  filter_map f (insert a s) = insert b (filter_map f s) :=
begin
  by_cases a ∈ s,
  { rw [insert_eq_of_mem h, insert_eq_of_mem],
    exact mem_filter_map.2 ⟨_, h, hf⟩, },
  { simp only [filter_map, multiset.ndinsert_of_not_mem h,
      multiset.filter_map_cons_some _ _ _ hf, multiset.to_finset_cons, finset.insert_val], },
end

theorem mem_of_card_filter_map {α β} [decidable_eq α] [decidable_eq β] {f : α → option β} {s : finset α}
  (h : card (s.filter_map f) = card s) {a} (ha : a ∈ s) : ∃ b, b ∈ f a :=
begin
  cases h' : f a with b, swap, {exact ⟨b, rfl⟩},
  refine (not_succ_le_self (card (erase s a)) (_ : _ + 1 ≤ _)).elim,
  rw [← insert_erase ha, filter_map_insert_none f h',
    card_insert_of_not_mem (not_mem_erase _ _)] at h, rw ← h,
  apply card_filter_map_le,
end

theorem inj_of_card_filter_map {α β} [decidable_eq α] [decidable_eq β] {f : α → option β} {s : finset α}
  (H : card (s.filter_map f) = card s) {a a'} (ha : a ∈ s) (ha' : a' ∈ s)
    {b} (h1 : b ∈ f a) (h2 : b ∈ f a') : a = a' :=
begin
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
  refine finset.induction_on s ⟨∅, by { simp only [finset.empty_subset, finset.card_empty,
    exists_prop_of_true, finset.filter_map_empty, and_self, eq_self_iff_true] }⟩ _,
  rintro a s as ⟨t, ss, st, ct⟩,
  cases h : f a with b,
  { refine ⟨t, subset.trans ss (subset_insert _ _), _, ct⟩,
    simpa only [filter_map_insert_none f h] },
  simp only [filter_map_insert_some f h],
  by_cases h' : b ∈ filter_map f s,
  { simp only [h', exists_prop, insert_eq_of_mem],
    exact ⟨t, subset.trans ss (subset_insert _ _), st, ct⟩ },
  { refine ⟨insert a t, _⟩,
    have ha := mt (@ss _) as,
    rw [filter_map_insert_some f h],
    refine ⟨insert_subset_insert _ ss, by rw st, _⟩,
    rw [← st, card_insert_of_not_mem h', st, ct, card_insert_of_not_mem ha], }
end

def finset_embed {X : finset α} (S : finset {x // x ∈ X}) : finset α :=
S.map $ function.embedding.subtype _

lemma finset_embed_inj {X : finset α} : function.injective
  (λ (S : finset {x // x ∈ X}), finset_embed S):=
begin
  unfold function.injective,
  intros S T h,
  simp only [ext, subtype.forall] at h ⊢,
  intros a ha,
  simp only [finset_embed, function.embedding.subtype, exists_prop,
    exists_and_distrib_right, exists_eq_right, function.embedding.coe_fn_mk, mem_map,
    subtype.exists] at h,
  exact iff.intro (λ H, exists.elim ((h a).mp (exists.intro ha H)) (λ ha_, id))
    (λ H, exists.elim ((h a).mpr (exists.intro ha H)) (λ ha_, id)),
end

instance finset_embed_coe (X : finset α) : has_coe (finset {x : α // x ∈ X}) (finset α) :=
⟨finset_embed⟩

def finset_finset_embed {X : finset α} (S : finset (finset {x // x ∈ X})) : finset (finset α) :=
S.map $ ⟨finset_embed, finset_embed_inj⟩

instance finset_finset_embed_coe (X : finset α) : has_coe (finset (finset {x : α // x ∈ X}))
  (finset (finset α)) :=
⟨finset_finset_embed⟩

-- need some basic theorems about finset_finset_embed_coe

lemma finset_embed_coe_def {X : finset α} (S : finset {x // x ∈ X}) : ↑S = finset_embed S :=
rfl

lemma finset_finset_embed_coe_def {X : finset α} (S : finset (finset {x // x ∈ X})) : ↑S = finset_finset_embed S :=
rfl

/-lemma finset_embed_mem_univ {X : finset α} (x : finset {a // a ∈ X}) : (↑x : α) ∈ X :=
begin
end-/

lemma finset_embed_subset_univ {X : finset α} (S : finset {a // a ∈ X}) : ↑S ⊆ X :=
by { simp only [subset_iff, finset_embed_coe_def, finset_embed, function.embedding.subtype,
    exists_prop, exists_and_distrib_right, exists_eq_right, function.embedding.coe_fn_mk,
    mem_map, subtype.exists, exists_imp_distrib],
  exact λ _ ha _, ha, }

lemma finset_embed_mem {X : finset α} {S : finset {a : α // a ∈ X}} {x : {a : α // a ∈ X}} :
  x ∈ S ↔ x.val ∈ (↑S : finset α) :=
by { simp only [finset_embed_coe_def, finset_embed, function.embedding.subtype,
    exists_prop, exists_and_distrib_right, subtype.eta, exists_eq_right,
    function.embedding.coe_fn_mk, mem_map, subtype.exists],
  exact iff.intro (λ h, ⟨x.2, mem_def.mp h⟩) (λ h, h.2), }

/-lemma finset_embed_finset_mem {X : finset α} {S : finset (finset {a : α // a ∈ X})}
  {x : finset {a : α // a ∈ X}} : x ∈ S ↔ ↑x ∈ (↑S) :=
sorry-/
/-
lemma aux : insert e ↑x = ↑(insert e x) := sorry-/

lemma finset_embed_subset {X : finset α} {x y : finset {a // a ∈ X}} :
  x ⊆ y ↔ ↑x ⊆ (↑y : finset α) :=
by { simp only [subset_iff, finset_embed_coe_def, finset_embed, function.embedding.subtype,
    exists_prop, exists_and_distrib_right, exists_eq_right, function.embedding.coe_fn_mk,
    mem_map, subtype.forall, subtype.exists, exists_imp_distrib],
  exact iff.intro (λ h a ha H, exists.intro ha (h a ha H))
    (λ h a ha H, exists.elim (h ha H) (λ ha_ hay, hay)), }

lemma finset_embed_card [decidable_eq α] {X : finset α} (x : finset {a // a ∈ X}) : card x = card (↑x : finset α) :=
by { rw [finset_embed_coe_def, finset_embed],
  exact (map_eq_image (function.embedding.subtype _) x).symm ▸
    (card_image_of_injective x (function.embedding.subtype _).2).symm, }

section prestrict
variables [decidable_eq α] [fintype α]

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134578668 -/
def prestrict (X : finset α) (I : finset α) : option (finset {x : α // x ∈ X}) :=
if h : _ then some
  ⟨I.1.pmap (λ x h', ⟨x, h'⟩) h,
    multiset.nodup_pmap (λ _ _ _ _, subtype.mk_eq_mk.1) I.2⟩ else none

lemma prestrict_eq_none {X : finset α} (I : finset α) : prestrict X I = none ↔ ¬ I ⊆ X :=
begin
  split,
  { intros h hIX,
    by_cases H : ∀ a, a ∈ I.val → a ∈ X,
    { change dite _ _ _ = none at h,
      rw dif_pos H at h,
      cases h, },
    { rcases not_forall.1 H with ⟨x, hx⟩,
      rw [not_imp, ←mem_def] at hx,
      exact hx.2 (hIX hx.1), }, },
  { intro hIX,
    exact dif_neg hIX, },
end

lemma prestrict_eq_some_aux {X : finset α} {I : finset α} (h : ∀ a, a ∈ I.val → a ∈ X) :
  let I' : finset {x // x ∈ X} :=
    {val := multiset.pmap (λ x h', ⟨x, h'⟩) (I.val) h,
    nodup := prestrict._proof_1 X I h} in
  ↑I' = I :=
begin
  intro I',
  rw [←val_inj, finset_embed_coe_def, finset_embed, map_val, multiset.map_pmap, le_antisymm_iff],
  split,
  { have hnodup := multiset.nodup_pmap _ I.2,
    rw [multiset.le_iff_subset hnodup, multiset.subset_iff],
    { intros x hx,
      rw multiset.mem_pmap at hx,
      rcases hx with ⟨a, haI, H⟩,
      convert haI,
      subst H,
      refl, },
    intros a ha b hb H,
    have hinj : (⟨a, ha⟩ : {x // x ∈ X}) = ⟨b, hb⟩ := (function.embedding.subtype _).2 H,
    exact subtype.mk_eq_mk.1 hinj, },
  { rw [multiset.le_iff_subset I.2, multiset.subset_iff],
    intros x hx,
    rw multiset.mem_pmap,
    use [x, hx],
    refl, },
end

lemma prestrict_eq_some_of_subset {X : finset α} {I : finset α} (h : I ⊆ X)
  : ∃ I', prestrict X I = some I' ∧ ↑I' = I :=
begin
  let I' := _,
  have : prestrict X I = some I' := dif_pos h,
  use [I', this],
  exact prestrict_eq_some_aux h,
end

lemma subset_of_prestrict_eq_some {X : finset α} {I : finset α} {I' : finset {x : α // x ∈ X}}
  (h : prestrict X I = some I') : I ⊆ X ∧ ↑I' = I :=
begin
  by_cases H : ∀ a, a ∈ I.val → a ∈ X,
  { split,
    { exact H, },
    { change dite _ _ _ = _ at h,
      rw [dif_pos H, option.some_inj] at h,
      subst h,
      exact prestrict_eq_some_aux H, }, },
  { exfalso,
    change dite _ _ _ = _ at h,
    rw dif_neg H at h,
    cases h, },
end

def prestrict_subset {X Y : finset α} (h : X ⊆ Y) : finset {x // x ∈ Y} :=
sorry

end prestrict

variable [decidable_eq α]

lemma inter_of_subset {A B : finset α} (h : A ⊆ B) : A ∩ B = A :=
lattice.inf_of_le_left h

lemma subset_iff_sdiff_eq_empty {x y : finset α} : x ⊆ y ↔ x \ y = ∅ :=
by simp only [sdiff_eq_filter, eq_empty_iff_forall_not_mem, subset_iff, not_and,
  not_not, finset.mem_filter]

lemma empty_sdiff (E : finset α) : E \ ∅ = E :=
by simp only [ext, finset.not_mem_empty, and_true, iff_self, finset.mem_sdiff,
  not_false_iff, forall_true_iff]

lemma sdiff_subset (A B : finset α): A \ B ⊆ A :=
(empty_sdiff A).subst $ sdiff_subset_sdiff (subset.refl A) $ empty_subset B

lemma sdiff_eq_sdiff_inter (A B : finset α) : A \ B = A \ (A ∩ B) :=
by { simp only [ext, not_and, mem_sdiff, mem_inter],
  exact λ a, iff.intro (λ h, ⟨h.1, λ x, h.2⟩) (λ h, ⟨h.1, h.2 h.1⟩), }

lemma card_eq_inter_sdiff (A B : finset α) : card A = card (A ∩ B) + card (A \ B) :=
begin
  have hA : A \ B ∪ A ∩ B = A := by { simp only [ext, mem_union, union_comm, mem_sdiff, mem_inter],
    exact λ a, iff.intro (λ ha, or.elim ha (λ H, H.1) (λ H, H.1))
      (by { intro ha, by_cases h : a ∈ B, { exact or.inl ⟨ha, h⟩ }, { exact or.inr ⟨ha, h⟩ } }) },
  have : disjoint (A \ B) (A ∩ B) := by simp only [disjoint, empty_subset, inf_eq_inter,
    inter_empty, sdiff_inter_self, inter_left_comm, le_iff_subset],
  replace this := card_disjoint_union this, rwa [hA, add_comm] at this,
end

lemma card_sdiff_eq (A B : finset α) : card (A \ B) = card A - card (A ∩ B) :=
(nat.sub_eq_of_eq_add $ card_eq_inter_sdiff A B).symm

lemma card_union_inter (A B : finset α) : card A + card B = card (A ∪ B) + card (A ∩ B) :=
begin
  have hBA : card B = card (B \ A) + card (A ∩ B) := inter_comm B A ▸
    (add_comm (card (B ∩ A)) (card (B \ A))) ▸ (card_eq_inter_sdiff B A),
  have Hdis : disjoint A (B \ A) := by simp only [disjoint, empty_subset, inf_eq_inter,
    inter_sdiff_self, le_iff_subset],
  have H : card A + card (B \ A) = card (A ∪ B) :=
    (congr_arg card $ union_sdiff_self_eq_union.symm).substr (card_disjoint_union Hdis).symm,
  calc
  card A + card B = card A + card (B \ A) + card (A ∩ B) : by rw [add_assoc, hBA]
  ... = card (A ∪ B) + card (A ∩ B) : by rw H,
end

/- proof by Kenny Lau https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/choosing.20from.20difference.20of.20finsets/near/133624012 -/
lemma exists_sdiff_of_card_lt {x y : finset α} (hcard : card x < card y) : ∃ e : α, e ∈ y \ x :=
suffices ∃ e ∈ y, e ∉ x, by simpa only [exists_prop, finset.mem_sdiff],
by_contradiction $ λ H, not_le_of_lt hcard $ card_le_of_subset $ by simpa only [not_exists,
  exists_prop, not_and, not_not] using H

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
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, min_le_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

section inst

variables {F : finset α} {Q : finset α → Prop} [decidable_pred Q] {P : α → Prop} [decidable_pred P]

instance decidable_not_forall (c₁ : finset (finset α)) :
  decidable (∃ x : finset α, ¬(x ∈ c₁ → ¬Q x)) :=
decidable_of_iff (∃ x ∈ c₁, Q x) $ by simp only [exists_prop, not_forall_not]

instance decidable_exists_and_mem : decidable (∃ e, e ∈ F ∧ P e) :=
decidable_of_iff (∃ e ∈ F, P e) $ by simp only [exists_prop]

end inst

end finset

open finset

-- § 1.1

namespace matroid

variables (E : Type*) [decidable_eq E] [fintype E]

/-- `indep E` is the type of matroids (in the independent set representation)
with ground set `E` (encoded in Lean as a fintype). -/
structure of_indep :=
(indep : finset (finset E))
-- (I1)
(empty_mem_indep : ∅ ∈ indep)
-- (I2)
(indep_of_subset_indep {x y} (hx : x ∈ indep) (hyx : y ⊆ x) : y ∈ indep)
-- (I3)
(indep_exch {x y : finset E} (hx : x ∈ indep) (hy : y ∈ indep) (hcard : card x < card y)
    : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep)


namespace of_indep

instance repr [has_repr E] : has_repr (of_indep E) :=
⟨λ m, has_repr.repr m.indep⟩

variable {E}

theorem eq_of_indep_eq : ∀ {M₁ M₂ : of_indep E}, M₁.1 = M₂.1 → M₁ = M₂
  | ⟨I₁, p₁, q₁, r₁⟩ ⟨I₂, p₂, q₂, r₂⟩ h :=
by simpa only []

/-- A circuit of a matroid is a minimal dependent subset of the ground set -/
def is_circuit (x : finset E) (m : of_indep E) : Prop :=
x ∉ m.indep ∧ ∀ y, y ⊂ x → y ∈ m.indep

/-- proof by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finsets.2C.20decidable_mem.2C.20and.20filter/near/133708937 -/
instance decidable_circuit (x : finset E) (m : of_indep E) : decidable (is_circuit x m) :=
decidable_of_iff (x ∉ m.indep ∧ ∀ y ∈ (powerset x).erase x, y ∈ m.indep)
begin
  simp only [is_circuit, has_ssubset.ssubset, mem_powerset, and_imp, mem_erase],
  refine and_congr iff.rfl (forall_congr $ λ y, _),
  refine ⟨λ H h₁ h₂, H (mt _ h₂) h₁, λ H h₁ h₂, H h₂ $ mt _ h₁⟩,
  { rintro rfl, refl }, { exact subset.antisymm h₂, },
end

instance decidable_circuit_subset (x : finset E) (m : of_indep E) :
  decidable (∃ (y : finset E) (H : y ⊆ x), is_circuit y m) :=
decidable_of_iff (∃ (y : finset E) (H : y ∈ powerset x), is_circuit y m) $
  by simp only [exists_prop, mem_powerset]

/- should I make this definition reducible? I don't know when to use attributes... -/
def circuits_circuits (m : of_indep E) : finset (finset E) :=
(powerset univ).filter (λ S, is_circuit S m)

lemma C2 (m : of_indep E) (x y : finset E) (hx : x ∈ circuits_circuits m)
  (hy : y ∈ circuits_circuits m) (hxy : x ⊆ y) : x = y :=
begin
  simp only [circuits_circuits, is_circuit, mem_filter] at hx hy hxy,
  have hnxy : ¬x ⊂ y := λ h, hx.2.1 $ hy.2.2 x h,
  rw ←lt_iff_ssubset at hnxy,
  rw [←le_iff_subset, le_iff_eq_or_lt] at hxy,
  cases hxy,
  { exact hxy, },
  { exact (hnxy hxy).elim, },
end

theorem dep_iff_circuit_subset (x : finset E) (m : of_indep E) :
  x ∉ m.indep ↔ ∃ y ⊆ x, is_circuit y m :=
begin
  split,
  { intro hxd,
    rcases min_fun_of_ne_empty card (ne_empty_of_mem $
      mem_filter.mpr ⟨mem_powerset.mpr $ subset.refl x, hxd⟩) with ⟨a, ha, hamin⟩,
    have hax : a ⊆ x := mem_powerset.mp (mem_filter.mp ha).1,
    use [a, hax], split,
    { exact (mem_filter.mp ha).2, },
    { intros y hy, by_contra h,
      refine not_le_of_lt (card_lt_card hy) _,
      refine hamin y (mem_filter.mpr ⟨_, h⟩),
      refine mem_powerset.mpr (subset.trans _ hax),
      exact (le_of_lt $ lt_iff_ssubset.mpr hy), } },
  { rintros ⟨a, ⟨hax, hacirc⟩⟩ hxi,
    exact hacirc.1 (m.indep_of_subset_indep hxi hax), },
end

/-- Lemma 1.1.3 -/
lemma C3 (m : of_indep E) (x y : finset E) (e : E) (hx : x ∈ m.circuits_circuits)
  (hy : y ∈ m.circuits_circuits) (hxny : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ m.circuits_circuits ∧ z ⊆ erase (x ∪ y) e :=
begin
  have hxmy : x \ y ≠ ∅ := mt subset_iff_sdiff_eq_empty.mpr (mt (m.C2 x y hx hy) hxny),
  rcases exists_mem_of_ne_empty hxmy with ⟨a, ha⟩, clear hxny hxmy,
  simp only [circuits_circuits, mem_powerset, mem_filter, mem_sdiff, mem_inter]
    at ha hx hy he,
  have hxai : erase x a ∈ m.indep := by { unfold is_circuit at hx,
    exact hx.2.2 (erase x a) (erase_ssubset ha.1) },
  let F := (powerset (x ∪ y)).filter (λ S, erase x a ⊆ S ∧ S ∈ m.indep),
  have hxaF : erase x a ∈ F := mem_filter.2 ⟨mem_powerset.mpr $ subset.trans (erase_subset a x) $
    subset_union_left x y, ⟨subset.refl _, hxai⟩⟩, clear hxai,
  rcases (max_fun_of_ne_empty card $ ne_empty_of_mem hxaF) with ⟨I, ⟨hIF, hI⟩⟩, clear hxaF,
  have hIFindep : I ∈ m.indep := (mem_filter.mp hIF).2.2,
  have hIdep : _ → I ∉ m.indep := (dep_iff_circuit_subset I m).2,
  have hIFxa : erase x a ⊆ I := (mem_filter.mp hIF).2.1,
  have hIxuy : I ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hIF).1,
  have haniI : a ∉ I :=
    λ H, have hxI : x ⊆ I := (insert_erase ha.1) ▸ insert_subset.mpr ⟨H, hIFxa⟩,
      have ∃ A ⊆ I, is_circuit A m := exists.intro x (exists.intro hxI hx.2),
      hIdep this hIFindep,
  have hEg : ∃ g ∈ y, g ∉ I :=
    by { have hIdep2 := mt hIdep, simp only [not_exists, exists_prop, not_and, not_not]
      at hIdep2,
    have hyI0 := mt (hIdep2 hIFindep y), simp only [not_not] at hyI0,
    have hYI : ¬y ⊆ I := hyI0 hy.2,
    have this := exists_mem_of_ne_empty (mt subset_iff_sdiff_eq_empty.mpr hYI),
    simp only [mem_sdiff] at this, simpa only [exists_prop], },
  rcases hEg with ⟨g, ⟨hgy, hgnI⟩⟩, clear hIdep,
  have hga : g ≠ a := λ H, ha.2 (H ▸ hgy),
  have hIag : I ⊆ erase (erase (x ∪ y) a) g :=
    subset_iff.mpr (λ xx hxx, mem_erase.mpr ⟨λ hgg, hgnI $ hgg ▸ hxx,
      mem_erase.mpr ⟨λ hgga, haniI $ hgga ▸ hxx, mem_of_subset hIxuy hxx⟩⟩),
  have haxuy : a ∈ x ∪ y := mem_union_left y ha.1,
  have hcardxye : card (erase (x ∪ y) a) = nat.pred (card (x ∪ y)) :=
    card_erase_of_mem haxuy,
  have hpcard : nat.pred (card (x ∪ y)) > 0 := by { rw ←hcardxye,
    exact card_pos.mpr (ne_empty_of_mem $ mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), },
  have hcard : card I < card (erase (x ∪ y) e) :=
    calc card I ≤ card (erase (erase (x ∪ y) a) g) : card_le_of_subset hIag
    ... = nat.pred (nat.pred (card (x ∪ y))) : by rw [card_erase_of_mem
      (mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), hcardxye]
    ... < card (erase (x ∪ y) e) :
      by { rw [card_erase_of_mem (mem_union_left y he.1),
      ←nat.succ_pred_eq_of_pos hpcard], exact nat.lt_succ_self _, },
  clear hga hIag haxuy hcardxye hpcard he,
  by_contra h, simp only [circuits_circuits, mem_powerset, not_exists, and_imp,
    mem_filter, not_and] at h,
  have : (∀ x_1 : finset E, x_1 ⊆ erase (x ∪ y) e → ¬is_circuit x_1 m) :=
    λ x1 hx1, (mt $ h x1 $ subset_univ x1) $ not_not.mpr hx1,
  have hindep := mt (dep_iff_circuit_subset (erase (x ∪ y) e) m).mp,
  simp only [not_exists, exists_prop, not_and, not_not] at hindep,
  replace hindep : erase (x ∪ y) e ∈ m.indep := hindep this,
  rcases (m.indep_exch hIFindep hindep hcard) with ⟨El, ⟨hElxy, hElindep⟩⟩,
  have hElF : insert El I ∈ F := mem_filter.mpr ⟨mem_powerset.mpr
    (insert_subset.mpr ⟨(mem_erase.mp (mem_sdiff.mp hElxy).1).2, hIxuy⟩),
    ⟨subset.trans hIFxa (subset_insert El I), hElindep⟩⟩,
  have hcardEl : card I < card (insert El I) :=
    by { rw card_insert_of_not_mem (mem_sdiff.mp hElxy).2,
    exact lt_add_one (card I), },
  exact not_lt.mpr (hI (insert El I) hElF) hcardEl,
end

end of_indep

open of_indep
variable (E)

structure of_circuits :=
(circuits : finset (finset E))
-- (C1)
(empty_not_mem_circuits : ∅ ∉ circuits)
-- (C2)
(circuits_eq_of_subset {x y} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ⊆ y) : x = y)
-- (C3)
(circuit_elim {x y e} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits ∧ z ⊆ erase (x ∪ y) e)
--attribute [class] circuits

namespace of_circuits

instance repr [has_repr E] : has_repr (of_circuits E) :=
⟨λ c, has_repr.repr c.circuits⟩

variable {E}

theorem eq_of_circ_eq : ∀ {C₁ C₂ : of_circuits E}, C₁.1 = C₂.1 → C₁ = C₂
  | ⟨c₁, p₁, q₁, r₁⟩ ⟨c₂, p₂, q₂, r₂⟩ h :=
by simpa only []

end of_circuits

namespace of_indep

variable {E}

def circuits (m : of_indep E) : of_circuits E :=
{ circuits := m.circuits_circuits,
  empty_not_mem_circuits :=
    begin
      simp only [circuits_circuits, is_circuit, mem_filter, not_and],
      intros h h1, exfalso,
      exact h1 m.empty_mem_indep,
    end,
  circuits_eq_of_subset := m.C2,
  circuit_elim := m.C3 }

end of_indep

namespace of_circuits
open of_indep
variable {E}

/- make reducible? -/
def indep_indep (C : of_circuits E) : finset (finset E) :=
(powerset univ).filter (λ S, ∀ c ∈ C.circuits, ¬c ⊆ S)

/-- first part of Theorem 1.1.4 -/
lemma I2 (C : of_circuits E) (x y : finset E) : x ∈ C.indep_indep → y ⊆ x →
  y ∈ C.indep_indep :=
begin
  simp only [indep_indep, mem_powerset, and_imp, mem_filter],
  exact λ hxE hx hxy, ⟨subset.trans hxy hxE, λ c hc H, hx c hc $ subset.trans H hxy⟩,
end

/-- second part of Theorem 1.1.4 -/
lemma I3 (C : of_circuits E) (x y : finset E) (hx : x ∈ C.indep_indep)
  (hy : y ∈ C.indep_indep) (hcardxy : card x < card y)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ C.indep_indep :=
begin
  unfold indep_indep at ⊢,
  simp only [indep_indep, mem_powerset, mem_filter] at hx hy,
  by_contra h,
  simp only [mem_powerset, not_exists, and_imp, mem_filter, not_and, mem_sdiff] at h,
  let F := (powerset $ x ∪ y).filter (λ S, (∀ c ∈ C.circuits, ¬c ⊆ S) ∧ card x < card S),
  have hyF : y ∈ F := mem_filter.mpr ⟨mem_powerset.mpr $ subset_union_right x y,
    ⟨hy.2, hcardxy⟩⟩,
  rcases (min_fun_of_ne_empty (λ f, card (x \ f)) $ ne_empty_of_mem hyF) with ⟨z, ⟨hz, hminz⟩⟩,
  clear hcardxy hyF,
  have hzxuy : z ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hz).1,
  replace hz := (mem_filter.mp hz).2,
  rcases (exists_sdiff_of_card_lt hz.2) with ⟨a, ha⟩,
  rw mem_sdiff at ha,
  have hxsdiffz : x \ z ≠ ∅ :=
    by { intro H,
    have Hxsubz : x ⊆ z := subset_iff_sdiff_eq_empty.mpr H,
    have hay : a ∈ y := or.elim (mem_union.mp $ mem_of_subset hzxuy ha.1)
      (λ Hax, false.elim $ ha.2 Hax) id,
    have haindep : insert a x ∈ C.indep_indep := C.I2 z (insert a x)
      (by { simp only [indep_indep, mem_powerset, mem_filter],
      exact ⟨subset.trans hzxuy $ union_subset hx.1 hy.1, hz.1⟩, })
      (insert_subset.mpr ⟨ha.1, Hxsubz⟩),
    simp only [indep_indep, mem_powerset, mem_filter] at haindep,
    exact h a hay ha.2 haindep.1 haindep.2, },
  rcases (exists_mem_of_ne_empty hxsdiffz) with ⟨e, he⟩,
  clear h ha hxsdiffz,
  rw mem_sdiff at he,
  let T : E → finset E := λ f, erase (insert e z) f,
  have hTf1 : ∀ f, f ∈ z \ x → T f ⊆ x ∪ y :=
    by { intros f hf, rw [mem_sdiff] at hf,
    rw [subset_iff],
    intros gg hgg, simp only [mem_insert, mem_erase, ne.def] at hgg,
    simp only [mem_union],
    rcases hgg.2 with rfl | hggz,
    { exact or.inl he.1, },
    exact (mem_union.mp $ mem_of_subset hzxuy hggz) },
  have hTf2 : ∀ f, f ∈ z \ x → card (x \ T f) < card (x \ z) :=
    by { intros f hf, rw mem_sdiff at hf,
    suffices H : x \ T f ⊂ x \ z, exact card_lt_card H,
    by { simp only [ssubset_iff, exists_prop, mem_insert, not_forall_not, not_and,
                    mem_sdiff, mem_erase],
      use e, split,
      { intro _, split,
        { intro hef, exact hf.2 (hef ▸ he.1), },
        { exact or.inl rfl, } },
      { rw [subset_iff],
        intros gg hgg,
        simp only [mem_insert, not_and, mem_sdiff, mem_erase, ne.def] at hgg,
        have ggnef : gg ≠ f := by { intro ggef,
          rcases hgg with gge | H,
          { exact ((gge.symm ▸ he.2) $ ggef.substr hf.1), },
          { exact (ggef.substr hf.2) H.1, } },
        have he0 : e ∈ x \ z := mem_sdiff.mpr he,
        rcases hgg with gge | H,
        { exact gge.symm ▸ he0, },
        { exact mem_sdiff.mpr ⟨H.1, λ ggz, (H.2 ggnef) $ or.inr ggz⟩, } } } },
  have hTfindep : ∀ f, f ∈ z \ x → T f ∉ C.indep_indep :=
    by { intros f hf,
    simp only [indep_indep, mem_powerset, mem_filter, not_and],
    intros hTfE H,
    have HTf1 : T f ⊆ x ∪ y := hTf1 f hf,
    have HTf2 : card (x \ T f) < card (x \ z) := hTf2 f hf,
    rw mem_sdiff at hf,
    have HTfcard : card z = card (T f) :=
      by { simp only [card_erase_of_mem (mem_insert.mpr $ or.inr hf.1),
      card_insert_of_not_mem he.2, mem_insert, card_insert_of_not_mem, nat.pred_succ], },
    replace HTfcard : card x < card (T f) := HTfcard ▸ hz.2,
    have : T f ∈ F := mem_filter.mpr ⟨mem_powerset.mpr HTf1, ⟨H, HTfcard⟩⟩,
    exact not_lt.mpr (hminz (T f) this) HTf2, },
  have hTfC : ∀ f, f ∈ z \ x → ∃ c ∈ C.circuits, c ⊆ T f :=
    by { intros f hf,
    have : T f ∉ C.indep_indep := hTfindep f hf,
      simp only [indep_indep, mem_powerset, mem_filter, not_and] at this,
    have hfc := this (subset.trans (hTf1 f hf) $ union_subset hx.1 hy.1),
    by_contra H, simp only [not_exists, exists_prop, not_and] at H, contradiction, },
  rcases (exists_sdiff_of_card_lt hz.2) with ⟨g, hg⟩,
  rcases (hTfC g hg) with ⟨Cg, ⟨HCg1, HCg2⟩⟩,
  clear hTf1 hTf2 hTfindep hg hy hminz hzxuy,
  have hCgsub : Cg ⊆ insert e z := subset.trans HCg2 (erase_subset g $ insert e z),
  rw [subset_iff] at HCg2,
  have HCgzx : Cg ∩ (z \ x) ≠ ∅ := by { intro H,
    suffices : Cg ⊆ x, from hx.2 Cg HCg1 this,
    suffices H1 : Cg ⊆ erase (insert e (x ∩ z)) g, from
    suffices H2 : erase (insert e (x ∩ z)) g ⊆ x, from
    subset.trans H1 H2,
    show erase (insert e (x ∩ z)) g ⊆ x, by { rw [subset_iff],
      intros gg hgg,
      simp only [mem_insert, mem_erase, mem_inter] at hgg,
      rcases hgg.2 with gge | ggxggz,
      { exact gge.symm ▸ he.1, },
      { exact ggxggz.1, } },
    show Cg ⊆ erase (insert e (x ∩ z)) g, by
      { rw [subset_iff],
      intros gg hgg,
      replace HCg2 : gg ∈ T g := HCg2 hgg,
      simp only [mem_insert, mem_erase, mem_inter] at HCg2 ⊢,
      split,
      { exact HCg2.1, },
      { rw eq_empty_iff_forall_not_mem at H,
        replace H : gg ∉ Cg ∩ (z \ x) := H gg,
        simp only [not_and, mem_sdiff, not_not, mem_inter] at H,
        rcases HCg2.2 with gge | ggz,
        { exact or.inl gge, },
        { exact or.inr ⟨H hgg ggz, ggz⟩, } } } },
  clear HCg2 he hx,
  rcases (exists_mem_of_ne_empty HCgzx) with ⟨h0, hh0⟩, clear HCgzx,
  rw [mem_inter] at hh0,
  rcases (hTfC h0 hh0.2) with ⟨Ch0, ⟨hCh0circ, hCh0T⟩⟩, clear hTfC,
  have hCgneCh0 : Cg ≠ Ch0 :=
    λ H, have hh0Ch0 : h0 ∉ Ch0 := λ HH, (mem_erase.mp $
      mem_of_subset hCh0T HH).1 rfl, (H.symm ▸ hh0Ch0) hh0.1,
  have hCh0sub : Ch0 ⊆ insert e z :=
    subset.trans hCh0T (erase_subset h0 $ insert e z),
  have heCgCh0 : e ∈ Cg ∩ Ch0 :=
    by { rw mem_inter, split,
      { by_contra heCg, have hCgz : Cg ⊆ z :=
          (erase_eq_of_not_mem heCg) ▸ (subset_insert_iff.mp hCgsub),
        exact hz.1 Cg HCg1 hCgz },
      { by_contra heCh0, have hCh0z : Ch0 ⊆ z :=
          (erase_eq_of_not_mem heCh0) ▸ (subset_insert_iff.1 hCh0sub),
        exact hz.1 Ch0 hCh0circ hCh0z } },
  rcases (C.circuit_elim HCg1 hCh0circ hCgneCh0 heCgCh0) with ⟨CC, ⟨hCCcirc, hCCCguCh0⟩⟩,
  clear HCg1 hCh0circ hCgneCh0 heCgCh0,
  have hCCz : CC ⊆ z :=
    by { rw [subset_iff],
    intros t ht,
    rw [subset_iff] at hCCCguCh0,
    have htCguCh0 := hCCCguCh0 ht,
      simp only [mem_union, mem_erase] at htCguCh0,
    rw [subset_iff] at hCgsub hCh0sub,
    rcases htCguCh0.2 with htCg | htCh0,
    { rcases (mem_insert.mp $ hCgsub htCg) with Hte | Htz,
      { exfalso, exact htCguCh0.1 Hte, },
      { exact Htz, } },
    { rcases (mem_insert.mp $ hCh0sub htCh0) with Hte | Htz,
      { exfalso, exact htCguCh0.1 Hte },
      { exact Htz, } } },
  exact hz.1 CC hCCcirc hCCz,
end

def indep (C : of_circuits E) : of_indep E :=
{ indep := C.indep_indep,
  empty_mem_indep := mem_filter.mpr
    ⟨empty_mem_powerset univ, λ c hc H, C.empty_not_mem_circuits $ (subset_empty.mp H) ▸ hc⟩,
  indep_of_subset_indep := C.I2,
  indep_exch := C.I3 }

/- Not sure if these instances are a good idea... -/
-- instance circ_indep : has_coe (circuits E) (indep E) := ⟨indep_of_circuits⟩
-- instance indep_circ : has_coe (indep E) (circuits E) := ⟨circuits_of_indep⟩

/-- third part of Theorem 1.1.4 -/
theorem circ_indep_circ : ∀ C : of_circuits E, C = C.indep.circuits
  | ⟨c₁, p₁, q₁, r₁⟩ :=
begin
  simp only [of_circuits.indep, of_indep.circuits, indep_indep,
  circuits_circuits, is_circuit, ext, mem_filter, mem_powerset, and_imp, not_and],
  intro c,
  split,
  { intro hc,
    have ce : c ⊆ univ := subset_univ c,
    simp only [ce, true_and, forall_prop_of_true, not_forall, not_not],
    split,
    { use [c, hc], refl },
    { intros f hf, split,
      { exact subset.trans (le_of_lt $ lt_iff_ssubset.mpr hf) ce, },
      { intros g hg H,
        have Hc : g < c := lt_of_le_of_lt (le_iff_subset.mpr H) (lt_iff_ssubset.mpr hf),
        have r : g = c := q₁ hg hc (le_of_lt Hc),
        exact (not_le_of_lt Hc) (le_of_eq r.symm), } } },
  { rintro ⟨hc, ⟨Hc1, Hc2⟩⟩,
    have : ∃ c' ∈ c₁, c' ⊆ c := by { have := not_forall.mp (Hc1 hc),
    simpa only [exists_prop, not_forall_not] },
    rcases this with ⟨c', ⟨hc', hcc'⟩⟩,
    by_cases h : c = c',
    { exact h.symm ▸ hc' },
    { have hc'lt : c' ⊂ c := lt_of_le_of_ne (le_iff_subset.mpr hcc') (ne.symm h),
      have : c' ∉ c₁ := mt ((Hc2 c' hc'lt).2 c') (not_not.mpr $ subset.refl c'),
      exact (this hc').elim, } },
end

end of_circuits

namespace of_indep
open of_circuits
variable {E}

theorem indep_circ_indep (M : of_indep E) : M = M.circuits.indep :=
suffices M.indep = M.circuits.indep.indep, from eq_of_indep_eq this,
begin
  simp only [of_indep.circuits, of_circuits.indep, circuits_circuits, indep_indep,
    ext, mem_powerset, and_imp, mem_filter],
  intro I,
  have hI : I ∈ M.indep → I ⊆ univ := λ H, subset_univ I,
  rw [←and_iff_right_of_imp hI, and_congr_right],
  intro hIE, have := not_iff_not_of_iff (dep_iff_circuit_subset I M),
  simp only [not_exists, exists_prop, not_and, not_not] at this,
  rw [this, forall_congr],
  exact λ a, ⟨λ h h₁ h₂ h₃, (h h₃) h₂, λ h h₁ h₂, h (subset.trans h₁ hIE) h₂ h₁⟩,
end

/-- Proposition 1.1.6 -/
theorem existsu_circuit_of_dep_of_insert {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  ∃ c, c ∈ m.circuits_circuits ∧ c ⊆ insert e I ∧ e ∈ c ∧
  ∀ c', c' ∈ m.circuits_circuits → c' ⊆ insert e I → c' = c :=
begin
  simp only [circuits_circuits, mem_powerset, and_imp, mem_filter],
  have hIE : I ⊆ univ, from subset_univ I,
  have hc : ∃ (y : finset E) (H : y ⊆ insert e I), is_circuit y m,
    from (dep_iff_circuit_subset (insert e I) m).mp hIe, clear hIe,
  rcases hc with ⟨c, ⟨hceI, hccirc⟩⟩,
  have hcE : c ⊆ univ := subset_univ c,
  have hecirc : ∀ c' ⊆ insert e I, is_circuit c' m → e ∈ c' :=
    by { intros c' hc'eI hc'circ,
      have h₁ := subset_insert_iff.mp hc'eI,
      by_contra h,
      have h₂ := (erase_eq_of_not_mem h).symm,
      have h₃ : c' ⊆ I := calc
      c' = erase c' e : h₂
      ... ⊆ I : h₁,
      refine (dep_iff_circuit_subset I m).mpr _ hI,
      use [c', h₃], exact hc'circ, },
  have hec : e ∈ c := hecirc c hceI hccirc,
  use c,
  split, { exact ⟨hcE, hccirc⟩, }, { split, { exact hceI, }, { split, { exact hec, },
  { intros c' hc'E hc'circ hc'eI,
  have hec' : e ∈ c' := hecirc c' hc'eI hc'circ,
  have hcuc'eI : erase (c ∪ c') e ⊆ I :=
    by { simp only [subset_iff, and_imp, mem_union, mem_insert, mem_erase, ne.def]
      at hceI hc'eI ⊢,
      rintros a hane (H | H),
      { rcases (hceI H) with H' | H', { exact (hane H').elim, }, { exact H', } },
      { rcases (hc'eI H) with H' | H', { exact (hane H').elim ,}, { exact H', } } },
  have : erase (c ∪ c') e ∈ m.indep := m.indep_of_subset_indep hI hcuc'eI,
  by_contra h,
  have C3 := m.C3 c c' e,
    simp only [circuits_circuits, mem_powerset, and_imp,
      filter_congr_decidable, mem_filter, mem_inter] at C3,
  rcases (C3 hcE hccirc hc'E hc'circ (ne.symm h) hec hec') with ⟨c₀, ⟨⟨hc₀, hc₀circ⟩, hc₀erase⟩⟩,
  refine (dep_iff_circuit_subset I m).mpr _ hI,
  use [c₀, subset.trans hc₀erase hcuc'eI], exact hc₀circ, } } },
end

section encodable
variable [encodable E]

def circuit_of_dep_of_insert_indep {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) : finset E :=
encodable.choose (existsu_circuit_of_dep_of_insert hI hIe)

local notation `cdii` := circuit_of_dep_of_insert_indep

lemma circuit_of_dep_of_insert_indep_spec {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  cdii hI hIe ∈ m.circuits_circuits ∧ cdii hI hIe ⊆ insert e I ∧
  e ∈ cdii hI hIe ∧ ∀ c', c' ∈ m.circuits_circuits →
  c' ⊆ insert e I → c' = cdii hI hIe :=
encodable.choose_spec (existsu_circuit_of_dep_of_insert hI hIe)

end encodable

end of_indep

-- § 1.2

namespace of_indep
variable {E}

def is_basis (x : finset E) (m : of_indep E) : Prop :=
x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)

instance decidable_basis (x : finset E) (m : of_indep E) : decidable (is_basis x m) :=
decidable_of_iff (x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)) $
  by simp only [is_basis, iff_self, finset.mem_powerset]

/-- Lemma 1.2.1 -/
theorem bases_of_indep_card_eq {x y : finset E} {m : of_indep E} : is_basis x m → is_basis y m →
  card x = card y :=
begin
  intros hx hy,
  by_contra heq,
  wlog h : card x < card y using [x y, y x],
  { exact lt_or_gt_of_ne heq, },
  unfold is_basis at hx hy,
  rcases (m.indep_exch hx.1 hy.1 h) with ⟨e, ⟨he1, he2⟩⟩,
  have hememx : e ∉ x := (mem_sdiff.mp he1).2,
  exact (hx.2 (insert e x) $ ssubset_insert hememx) he2,
end

theorem exists_basis_containing_indep {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  ∃ B : finset E, I ⊆ B ∧ is_basis B m :=
begin
  let F := (m.indep).filter (λ a, I ⊆ a),
  have FI : I ∈ F := mem_filter.mpr ⟨h, subset.refl I⟩,
  rcases (max_fun_of_ne_empty card $ ne_empty_of_mem FI) with ⟨B, ⟨HBF, Hg⟩⟩,
  rw mem_filter at HBF,
  have hBB : is_basis B m := ⟨HBF.1, λ y hBy hyI,
    have hxsy : I ⊆ y := le_of_lt $ lt_of_le_of_lt (le_iff_subset.mpr HBF.2) $
      lt_iff_ssubset.mpr hBy,
    have hyF : y ∈ F := mem_filter.mpr ⟨hyI, hxsy⟩,
    lt_irrefl (card B) $ lt_of_lt_of_le (card_lt_card hBy) $ Hg y hyF⟩,
  use B, exact ⟨HBF.2, hBB⟩,
end

section encodable

variable [encodable E]

def basis_containing_indep {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  finset E :=
encodable.choose $ exists_basis_containing_indep h

local notation `bci` := basis_containing_indep

lemma basis_containing_indep_spec {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  I ⊆ bci h ∧ is_basis (bci h) m :=
encodable.choose_spec $ exists_basis_containing_indep h

end encodable

theorem dep_of_card_gt_card_basis {x B : finset E} {m : of_indep E} (hB : is_basis B m)
  (hcard : card B < card x) : x ∉ m.indep :=
begin
  intro hxI,
  rcases (exists_basis_containing_indep hxI) with ⟨B', ⟨hxB', hB'basis⟩⟩,
  refine ne_of_lt (lt_of_lt_of_le hcard $ card_le_of_subset hxB') _,
  exact bases_of_indep_card_eq hB hB'basis,
end

theorem card_of_indep_le_card_basis {x B : finset E} {m : of_indep E} (hx : x ∈ m.indep)
  (hB : is_basis B m) : card x ≤ card B :=
begin
  by_contra h,
  exact dep_of_card_gt_card_basis hB (lt_of_not_ge h) hx,
end

end of_indep

variable (E)

structure of_bases :=
(bases : finset (finset E))
-- (B1)
(bases_not_empty : bases ≠ ∅)
-- (B2)
(basis_exch {x y e} (hx : x ∈ bases) (hy : y ∈ bases) (he : e ∈ x \ y)
    : ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ bases)
--attribute [class] bases

namespace of_bases

instance bases_repr [has_repr E] : has_repr (of_bases E) :=
⟨λ b, has_repr.repr b.bases⟩

variable {E}

theorem eq_of_base_eq : ∀ {B₁ B₂ : of_bases E}, B₁.1 = B₂.1 → B₁ = B₂
  | ⟨b₁, p₁, q₁⟩ ⟨b₂, p₂, q₂⟩ h :=
by simpa only []

end of_bases

namespace of_indep

variable {E}

def bases_bases (m : of_indep E) : finset (finset E) :=
(powerset univ).filter (λ S, is_basis S m)

lemma B1 (m : of_indep E) : m.bases_bases ≠ ∅ :=
begin
  simp only [is_basis, bases_bases, ext, ne.def, mem_filter, mem_powerset,
    not_mem_empty, not_and, iff_false],
  intro h,
  rcases max_fun_of_ne_empty card (ne_empty_of_mem m.empty_mem_indep) with ⟨a, ⟨ha1, hg⟩⟩,
  refine (h a (subset_univ a) ha1) _,
  intros F Fcontainsa Findep,
  refine not_le_of_lt (card_lt_card Fcontainsa) _,
  exact hg F Findep,
end

/- Lemma 1.2.2 -/
lemma B2 (m : of_indep E) : ∀ (x y : finset E) (e : E), x ∈ m.bases_bases →
  y ∈ m.bases_bases → e ∈ x \ y →
  ∃ a, a ∈ y \ x ∧ insert a (erase x e) ∈ m.bases_bases :=
begin
  simp only [is_basis, bases_bases, filter_and, mem_filter, mem_sdiff,
  mem_powerset, and_imp],
  intros x y e hxE hxI hx hyE hyI hy hex hey,
  have hxr : erase x e ∈ m.indep := m.indep_of_subset_indep hxI (erase_subset e x),
  have hxB : is_basis x m := ⟨hxI, hx⟩, have hyB : is_basis y m := ⟨hyI, hy⟩,
  have hcard : card (erase x e) < card y := calc
    card (erase x e) < card x : card_lt_card $ erase_ssubset hex
    ... = card y : bases_of_indep_card_eq hxB hyB,
  rcases (m.indep_exch hxr hyI hcard) with ⟨a, ha⟩,
  clear hxr hyI hcard hyB,
  have ha1 := mem_sdiff.mp ha.1,
  have hae : a ≠ e := λ hae, hey $ hae ▸ ha1.1,
  have hax : a ∉ x := by { simp only [not_and, mem_erase, ne.def] at ha1, exact ha1.2 hae },
  have hcx : card x > 0 := card_pos.mpr (ne_empty_of_mem hex),
  have hayycard : card (insert a $ erase x e) = card x := calc
    card (insert a $ erase x e) = nat.pred (card x) + 1 : by rw [card_insert_of_not_mem ha1.2,
        card_erase_of_mem hex]
    ... = card x : nat.succ_pred_eq_of_pos hcx,
  use a, simp only [ha1.1, hax, true_and, not_false_iff, ha.2, subset_univ],
  intros y' hayy,
  refine dep_of_card_gt_card_basis hxB _,
  exact hayycard ▸ (card_lt_card hayy),
end

def bases (m : of_indep E) : of_bases E :=
{ bases := bases_bases m,
  bases_not_empty := m.B1,
  basis_exch := m.B2 }

end of_indep

namespace of_bases
open of_indep
variable {E}

/-- Lemma 1.2.4 -/
theorem bases_card_eq {x y : finset E} {b : of_bases E} (hx : x ∈ b.bases) (hy : y ∈ b.bases) :
  card x = card y :=
begin
  by_contra heq,
  wlog h : card y < card x using [x y, y x],
  exact lt_or_gt_of_ne (ne.symm heq), clear heq,
  let F : finset (finset E × finset E) := (finset.product b.bases b.bases).filter
    (λ e : finset E × finset E, card e.1 < card e.2),
  have hyx : (y, x) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, h⟩, clear hy hx,
  exact exists.elim (min_fun_of_ne_empty (λ f : finset E × finset E, card (f.2 \ f.1)) $
      ne_empty_of_mem hyx)
    (λ a ha, exists.elim ha $ by { clear hyx ha,
      intros haF Ha, replace haF := mem_filter.mp haF,
      have hab : a.1 ∈ b.bases ∧ a.2 ∈ b.bases := mem_product.mp haF.1,
      exact exists.elim (exists_sdiff_of_card_lt haF.2)
        (λ e he, exists.elim (b.basis_exch hab.2 hab.1 he) $ λ aa ⟨haa1, haa2⟩,
          by { rw mem_sdiff at haa1,
          let a2 : finset E := insert aa (erase a.2 e),
          have haani : aa ∉ erase a.2 e := λ h, haa1.2 (mem_erase.mp h).2,
          have hea2 : e ∈ a.2 := (mem_sdiff.mp he).1,
          have hpos : 0 < card a.2 := card_pos.mpr (ne_empty_of_mem hea2),
          have hcarda2 : card a.1 < card a2 := by { rw [card_insert_of_not_mem haani,
            card_erase_of_mem hea2, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos hpos],
            exact haF.2 }, clear haani hpos,
          have : e ∉ a2 := λ hh, or.elim (mem_insert.mp hh)
            (λ h4, haa1.2 $ h4 ▸ hea2) $ λ h5, (mem_erase.mp h5).1 rfl,
          have hcard : card (a2 \ a.1) < card (a.2 \ a.1) :=
            suffices a2 \ a.1 ⊂ a.2 \ a.1, from card_lt_card this,
            by { rw ssubset_iff,
            exact exists.intro e ⟨λ h0, this (mem_sdiff.mp h0).1,
              by { rw subset_iff,
              intros A hA, rw mem_insert at hA,
              exact or.elim hA (λ hA1, hA1.symm ▸ he)
                (by { intro hA2, rw [mem_sdiff, mem_insert] at hA2,
                exact mem_sdiff.mpr ⟨or.elim hA2.1 (λ h6, false.elim $ hA2.2 $ h6.symm ▸ haa1.1) $
                  λ h7, (mem_erase.mp h7).2, hA2.2⟩ }) }⟩ },
          have ha2F : (a.1, a2) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hab.1, haa2⟩, hcarda2⟩,
          exact not_le_of_lt hcard (Ha (a.1, a2) ha2F) }) })
end

def indep_indep (b : of_bases E) : finset (finset E) :=
(powerset univ).filter (λ x, ∃ a ∈ b.bases, x ⊆ a)

/-- first part of Theorem 1.2.3 -/
def indep (b : of_bases E) : of_indep E :=
{ indep := b.indep_indep,
  empty_mem_indep := mem_filter.mpr ⟨empty_mem_powerset univ,
    exists.elim (exists_mem_of_ne_empty b.bases_not_empty) $
      λ a ha, exists.intro a $ exists.intro ha $ empty_subset a⟩,
  indep_of_subset_indep := begin
      intros x y hx hxy,
      simp only [indep_indep, mem_powerset, filter_congr_decidable,
        exists_prop, mem_filter] at hx ⊢,
      split, { exact subset.trans hxy hx.1, },
      { rcases hx.2 with ⟨a, ha⟩, use a, exact ⟨ha.1, subset.trans hxy ha.2⟩, },
    end,
  indep_exch := begin
    intros x y hx hy hcard, unfold indep_indep at hx hy ⊢,
    let F := (b.bases).filter (λ S, S ⊆ y),
    by_contra h, simp only [mem_powerset, not_exists, and_imp, filter_congr_decidable,
      exists_prop, mem_filter, not_and, mem_sdiff] at hx hy h,
    rcases hx.2 with ⟨b1, ⟨hb1bases, hxb1⟩⟩,
    rcases hy.2 with ⟨b2, hb2⟩,
    have := (min_fun_of_ne_empty (λ f, card (f \ (y ∪ b1))) $
      ne_empty_of_mem $ mem_filter.mpr hb2),
    rcases this with ⟨B2, ⟨hB2filt, hB2min⟩⟩, clear hb2 b2,
    replace hB2filt : B2 ∈ b.bases ∧ y ⊆ B2 := mem_filter.mp hB2filt,
    have hysdiff : y \ b1 = y \ x := by { simp only [ext, mem_sdiff],
      exact λ gg, ⟨λ hgg, ⟨hgg.1, λ hggnx, hgg.2 $ mem_of_subset hxb1 hggnx⟩,
        λ hgg, ⟨hgg.1, λ ggb1, h gg hgg.1 hgg.2 (insert_subset.mpr
        ⟨mem_of_subset hy.1 hgg.1, hx.1⟩) b1 hb1bases $ insert_subset.mpr ⟨ggb1, hxb1⟩⟩⟩, },
    have hB2yub1: B2 \ (y ∪ b1) = ∅ := by { by_contra H,
      rcases (exists_mem_of_ne_empty H) with ⟨X, hX⟩, clear H,
      simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
      have hXB2b1 : X ∈ B2 \ b1 := by { rw mem_sdiff, exact ⟨hX.1, hX.2.2⟩ },
      rcases (b.basis_exch hB2filt.1 hb1bases hXB2b1) with ⟨Y, ⟨hYb1B2, hYbases⟩⟩,
      rw mem_sdiff at hYb1B2 hXB2b1,
      have hssubY : insert Y (erase B2 X) \ (y ∪ b1) ⊂  B2 \ (y ∪ b1) :=
        by { rw [ssubset_iff],
        use X,
        simp only [subset_iff, not_or_distrib, mem_union, mem_insert, not_and, mem_sdiff,
          not_not, mem_erase, not_true, or_false, ne.def, false_and, or_false,
          eq_self_iff_true],
        exact ⟨λ hXY, (hYb1B2.2 $ hXY ▸ hXB2b1.1).elim,
        λ gg hgg, or.elim hgg (λ ggx, ggx.symm ▸ hX) $ λ ggor2, or.elim ggor2.1
          (λ ggY, false.elim $ ((ggY ▸ ggor2.2.2) hYb1B2.1)) $
            λ ggXB2, ⟨ggXB2.2, ggor2.2⟩⟩, },
      replace hssubY := card_lt_card hssubY,
      have hysubY : y ⊆ insert Y (erase B2 X) := by {
        simp only [subset_iff, mem_insert, mem_erase, ne.def],
        exact λ gg hgg, or.inr ⟨λ ggx, hX.2.1 $ ggx ▸ hgg, mem_of_subset hB2filt.2 hgg⟩ },
      exact not_lt_of_le (hB2min (insert Y $ erase B2 X) $ mem_filter.mpr
          ⟨hYbases, hysubY⟩) hssubY }, clear hB2min,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hB2yub1, simp only [mem_union] at hB2yub1,
      have hB2b1y : B2 \ b1 = y \ b1 := by { simp only [ext, mem_sdiff],
        exact λ gg, ⟨λ hgg, ⟨or.elim (hB2yub1 hgg.1) id $ λ hb1, false.elim $ hgg.2 hb1, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hB2filt.2 hgg.1, hgg.2⟩⟩ },
      rw [hysdiff] at hB2b1y, clear hysdiff,
      have hb1xuB2 : b1 \ (x ∪ B2) = ∅ := by { by_contra H,
        rcases (exists_mem_of_ne_empty H) with ⟨X, hX⟩,
        simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
        rcases (b.basis_exch hb1bases hB2filt.1 $ mem_sdiff.mpr ⟨hX.1, hX.2.2⟩) with ⟨Y, hY⟩,
        rw mem_sdiff at hY,
        have hYyx : Y ∈ y ∧ Y ∉ x := mem_sdiff.mp (hB2b1y ▸ (mem_sdiff.mpr hY.1)),
        have hxYsub : insert Y x ⊆ insert Y (erase b1 X) := by {
          simp only [subset_iff, mem_insert, mem_erase, ne.def],
          exact λ gg hgg, or.elim hgg (λ ggY, or.inl ggY) $ λ ggx, or.inr ⟨λ ggX, hX.2.1 $
            ggX ▸ ggx, mem_of_subset hxb1 ggx⟩ },
        exact h Y hYyx.1 hYyx.2 (subset_univ (insert Y x)) (insert Y $ erase b1 X) hY.2 hxYsub, },
      clear h hx hy,
      rw [←subset_iff_sdiff_eq_empty, subset_iff] at hb1xuB2, simp only [mem_union] at hb1xuB2,
      have hb1B2 : b1 \ B2 = x \ B2 := by { simp only [ext, mem_sdiff],
        exact λ gg, ⟨λ hgg, ⟨or.elim (hb1xuB2 hgg.1) id $ λ ggB2, false.elim $ hgg.2 ggB2, hgg.2⟩,
            λ hgg, ⟨mem_of_subset hxb1 hgg.1, hgg.2⟩⟩ }, clear hb1xuB2,
      replace hb1B2 : b1 \ B2 ⊆ x \ y := hb1B2.symm ▸ (sdiff_subset_sdiff (subset.refl x)
          hB2filt.2),
      have hcardeq : card b1 = card B2 := bases_card_eq hb1bases hB2filt.1,
      have hcardb1B2 : card (b1 \ B2) = card (B2 \ b1) := calc
        card (b1 \ B2) = card b1 - card (b1 ∩ B2) : card_sdiff_eq b1 B2
        ... = card B2 - card (B2 ∩ b1) : by rw [hcardeq, inter_comm]
        ... = card (B2 \ b1) : by rw ←card_sdiff_eq B2 b1,
      have hcardcontra0 : card (y \ x) ≤ card (x \ y) := calc
        card (y \ x) = card (B2 \ b1) : by rw hB2b1y
        ... = card (b1 \ B2) : by rw hcardb1B2
        ... ≤ card (x \ y) : card_le_of_subset hb1B2,
      rw [card_sdiff_eq y x, card_sdiff_eq x y, inter_comm] at hcardcontra0,
      have hcardcontra : card y ≤ card x := nat.le_of_le_of_sub_le_sub_right
          (card_le_of_subset $ inter_subset_left x y) hcardcontra0,
      exact not_lt_of_le hcardcontra hcard,
    end }

-- instance base_indep : has_coe (bases E) (indep E) := ⟨indep_of_bases⟩
-- instance indep_base : has_coe (indep E) (bases E) := ⟨bases_of_indep⟩

/-- second part of Theorem 1.2.3 -/
theorem base_indep_base (B : of_bases E) : B = B.indep.bases :=
suffices B.bases = B.indep.bases.bases, from eq_of_base_eq this,
begin
  simp only [of_bases.indep, of_indep.bases, indep_indep, is_basis,
  ext, bases_bases, mem_filter, mem_powerset, not_and, not_exists, exists_prop],
  intro b, split,
  { intro hb,
    have hB : b ⊆ univ := subset_univ b,
    split,
    { exact hB, },
    { split, { split, { exact hB, }, { use b, exact ⟨hb, subset.refl b⟩, } },
      { intros b' hbb' _ _ hx H,
        exact (ne_of_lt $ lt_of_lt_of_le (card_lt_card hbb') $ card_le_of_subset H)
          (bases_card_eq hb hx) } } },
  { rintro ⟨_, ⟨⟨_, hbexists⟩, hb⟩⟩, rcases hbexists with ⟨a, ⟨habases, hba⟩⟩,
    have : a ⊆ univ := subset_univ a,
    by_cases h : a = b,
    { exact h ▸ habases, },
    { have hba' : b ⊂ a := lt_iff_ssubset.mp (lt_of_le_of_ne (le_iff_subset.mpr hba) $ ne.symm h),
      exact (hb a hba' this a habases $ subset.refl a).elim, } },
end

end of_bases

namespace of_indep
open of_bases
variable {E}

theorem indep_base_indep (M : of_indep E) : M = M.bases.indep :=
suffices M.indep = M.bases.indep.indep, from eq_of_indep_eq this,
begin
  simp only [of_bases.indep, of_indep.bases, indep_indep, is_basis,
  ext, bases_bases, mem_filter, mem_powerset, exists_prop],
  intro I, split,
  { intro hI, split,
    { exact subset_univ I, },
    { rcases (exists_basis_containing_indep hI) with ⟨B, hB⟩,
      unfold is_basis at hB,
      use B, exact ⟨⟨subset_univ B, hB.2⟩, hB.1⟩ } },
  { rintro ⟨hIuniv, hIexists⟩, rcases hIexists with ⟨B, ⟨⟨hBuniv, ⟨hBindep, hB'⟩⟩, hIB⟩⟩,
    exact M.indep_of_subset_indep hBindep hIB, },
end

/-- Corollary 1.2.6 -/
theorem existsu_fund_circ_of_basis {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : ∃ C, C ∈ m.circuits_circuits ∧ C ⊆ insert e B ∧
  ∀ C' ∈ m.circuits_circuits, C' ⊆ insert e B → C' = C :=
begin
  unfold is_basis at hB, rw mem_sdiff at he,
  have : insert e B ∉ m.indep := hB.2 (insert e B) (ssubset_insert he.2),
  replace := existsu_circuit_of_dep_of_insert hB.1 this,
  rcases this with ⟨C, ⟨hCcirc, ⟨HCinsert, ⟨_, HC⟩⟩⟩⟩,
  use C,
  exact ⟨hCcirc, ⟨HCinsert, λ C' hC'circ hC', HC C' hC'circ hC'⟩⟩,
end

section encodable

variable [encodable E]

def fund_circ_of_basis {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : finset E :=
encodable.choose (existsu_fund_circ_of_basis hB he)

lemma fund_circ_of_basis_spec {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : fund_circ_of_basis hB he ∈ m.circuits_circuits ∧
  fund_circ_of_basis hB he  ⊆ insert e B ∧ ∀ C' ∈ m.circuits_circuits, C' ⊆ insert e B →
  C' = fund_circ_of_basis hB he :=
encodable.choose_spec (existsu_fund_circ_of_basis hB he)

end encodable

end of_indep

-- § 1.3
namespace of_indep

variable {E}

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134578668 -/
def indep_of_restriction (m : of_indep E) (X : finset E) : finset (finset {x : E // x ∈ X}) :=
(m.indep).filter_map $ prestrict X
-- def indep_of_restriction (m : indep E) (X : finset E) : finset (finset E) :=
-- (m.indep).filter (λ I, I ⊆ X)

lemma mem_restriction {m : of_indep E} {X : finset E} {x : finset {y : E // y ∈ X}} :
x ∈ indep_of_restriction m X ↔ ↑x ∈ m.indep /-∧ ↑x ⊆ X -- just use finset_embed_subset_univ -/ :=
begin
  simp only [indep_of_restriction,
    function.embedding.subtype, function.embedding.coe_fn_mk,
    mem_filter_map],
  split,
  { rintro ⟨a, ⟨haindep, ha⟩⟩,
    convert haindep,
    rw option.mem_def at ha,
    exact (subset_of_prestrict_eq_some ha).2, },
  { intro h,
    use [↑x, h],
    rw option.mem_def,
    have hsub : ↑x ⊆ X := finset_embed_subset_univ x,
    rcases prestrict_eq_some_of_subset hsub with ⟨x', hx', H⟩,
    rw [hx', ←finset_embed_inj H], },
end

def restriction (m : of_indep E) (X : finset E) : of_indep {x : E // x ∈ X} :=
{ indep := indep_of_restriction m X,
  empty_mem_indep := mem_restriction.mpr m.empty_mem_indep,
  indep_of_subset_indep := λ x y hx hyx, have hx' : ↑x ∈ m.indep := mem_restriction.mp hx,
  have hyx' : ↑y ⊆ (↑x : finset E) := finset_embed_subset.mp hyx,
  mem_restriction.mpr (m.indep_of_subset_indep hx' hyx'),
  indep_exch := begin
    intros x y hx hy hcard,
    have hx' : _ := mem_restriction.mp hx, have hy' : _ := mem_restriction.mp hy,
    have hcard' : card (↑x : finset E) < card ↑y := calc
      card (↑x : finset E) = card x : (finset_embed_card x).symm
      ... < card y : hcard
      ... = card ↑y : finset_embed_card y,
    have H : _ := m.indep_exch hx' hy' hcard',
    rcases H with ⟨e, he⟩,
    rw mem_sdiff at he,
    have He : e ∈ X := mem_of_subset (finset_embed_subset_univ y) he.1.1,
    let e' := subtype.mk e He,
    have heyx : e' ∈ y \ x := mem_sdiff.mpr ⟨finset_embed_mem.mpr he.1.1,
      λ H, he.1.2 $ finset_embed_mem.mp H⟩,
    have heinsert : ↑(insert e' x) ∈ m.indep :=
      by { have : (↑(insert e' x) : finset E) = insert e ↑x :=
        by simp only [ext, finset_embed_coe_def, finset_embed, function.embedding.subtype,
          exists_prop, finset.mem_map, iff_self, exists_and_distrib_right, finset.map_insert,
          exists_eq_right, function.embedding.coe_fn_mk, finset.mem_insert, subtype.exists,
          forall_true_iff],
      exact this.symm ▸ he.2 },
    have H : insert e' x ∈ indep_of_restriction m X :=
      mem_restriction.mpr heinsert,
    exact exists.intro e' ⟨heyx, H⟩,
  end }

-- what about {x : E // x ∉ X} ?
def deletion (m : of_indep E) (X : finset E) : of_indep {x : E // x ∈ univ \ X} :=
restriction m (univ \ X)

notation m `¦` X := restriction m X
notation m `\` X := deletion m X

lemma restriction_subset_restriction (m : of_indep E) (X : finset E) :
  ↑(m ¦ X).indep ⊆ m.indep :=
begin
  rw [subset_iff],
  intros I hI,
  rw [finset_finset_embed_coe_def, finset_finset_embed] at hI,
  simp only [exists_prop, function.embedding.coe_fn_mk, mem_map] at hI,
  rcases hI with ⟨I', hI'indep, rfl⟩,
  simp only [restriction, indep_of_restriction, mem_filter_map] at hI'indep,
  rcases hI'indep with ⟨a, haindep, haI'⟩,
  rw [option.mem_def] at haI',
  convert haindep,
  have := subset_of_prestrict_eq_some haI',
  rw [←finset_embed_coe_def, this.2],
end

lemma restriction_trans {X Y : finset E} (hXY : X ⊆ Y) (m : of_indep E) :
  (m ¦ X) = ((m ¦ Y) ¦ X) :=
by { simp only [restriction, indep_of_restriction, ext, mem_filter],
  exact λ I, iff.intro (λ h, ⟨⟨h.1, subset.trans h.2 hXY⟩, h.2⟩) $ λ h, ⟨h.1.1, h.2⟩ }

lemma subset_restriction_indep {X Y : finset E} {m : of_indep E} (hX : X ∈ m.indep) (hXY : X ⊆ Y)
  : X ∈ (m ¦ Y).indep :=
by { simp only [restriction, indep_of_restriction, mem_filter], exact ⟨hX, hXY⟩ }

/-def spans (X : finset α) {Y : finset α} (hY : Y ⊆ E) (m : indep E) : Prop :=
X ∈ bases_bases_of_indep (m ¦ hY)-/

lemma exists_basis_of_subset (X : finset E) (m : of_indep E) :
  ∃ B, B ∈ (m ¦ X).bases_bases :=
exists_mem_of_ne_empty $ B1 (m ¦ X)

/-lemma inter_of_span_of_subset_span {m : indep E} {X Y bX bY : finset α} {hXE : X ⊆ E}
  (hbX : spans bX hXE m) {hYE : Y ⊆ E} (hbY : spans bY hYE m) (hbXbY : bX ⊆ bY) : bY ∩ X = bX :=
sorry-/

#exit

section encodable
variable [encodable α]

def basis_of_subset (X : finset E) (m : of_indep E) : finset α :=
encodable.choose $ exists_basis_of_subset X m

def basis_of_subset_spec {X : finset E} (m : of_indep E) :
  basis_of_subset X m ∈ (m ¦ X).bases_bases :=
encodable.choose_spec $ exists_basis_of_subset X m

notation `𝔹` := basis_of_subset
notation `𝔹ₛ` := basis_of_subset_spec

def rank_of_subset {X : finset E} (m : of_indep E) : ℕ :=
card $ 𝔹 hXE m

notation `𝓇` := rank_of_subset

lemma R2 (m : of_indep E) {X Y : finset α} (hXY : X ⊆ Y) :
  𝓇 (subset.trans hXY hYE) m ≤ 𝓇 hYE m :=
let hXE : X ⊆ E := subset.trans hXY hYE in let bX := 𝔹 hXE m in let bY := 𝔹 hYE m in
have bXs : _ := 𝔹ₛ hXE m, have bYs : _ := 𝔹ₛ hYE m,
by { simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter] at bXs bYs,
  unfold rank_of_subset,
  have hBX : bX ∈ (m ¦ hYE).indep := mem_of_subset (restriction_subset_restriction hXY (m ¦ hYE))
    ((restriction_trans hXY hYE m) ▸ bXs.2.1),
  exact exists.elim (exists_basis_containing_indep hBX) (λ B hB, calc
    card bX ≤ card B : card_le_of_subset hB.1
    ... = card bY : bases_of_indep_card_eq hB.2 bYs.2) }

/-- Lemma 1.3.1 -/
lemma R3 (m : of_indep E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) :
  𝓇 (union_subset hX hY) m +
  𝓇 (subset.trans (inter_subset_left X Y) hX) m ≤
  𝓇 hX m + 𝓇 hY m :=
begin
  have hXXuY : X ⊆ X ∪ Y := subset_union_left X Y,
  have hYXuY : Y ⊆ X ∪ Y := subset_union_right X Y,
  have hXiYX : X ∩ Y ⊆ X := inter_subset_left X Y,
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  have hXiY : X ∩ Y ⊆ E := subset.trans hXiYX hX,
  let bXuY := 𝔹 hXuY m, let bXiY := 𝔹 hXiY m,
  let bX := 𝔹 hX m, let bY := 𝔹 hY m,
  unfold rank_of_subset,
  have bXuYs := 𝔹ₛ hXuY m, have bXiYs := 𝔹ₛ hXiY m,
  have bXs := 𝔹ₛ hX m, have bYs := 𝔹ₛ hY m,
  simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter]
    at bXuYs bXiYs bXs bYs,
  have rXiY : 𝓇 hXiY m = card bXiY := by simp only [rank_of_subset],
  have hiu : X ∩ Y ⊆ X ∪ Y := subset.trans hXiYX hXXuY,
  have hbXiY : bXiY ∈ (m ¦ hXuY).indep := mem_of_subset
    (restriction_subset_restriction hiu (m ¦ hXuY)) ((restriction_trans hiu hXuY m) ▸ bXiYs.2.1),
  have HbbXiY := exists_basis_containing_indep hbXiY,
  exact exists.elim HbbXiY (by { intros B hB,
    have rXuY : 𝓇 hXuY m = card B := by { simp only [rank_of_subset],
      exact bases_of_indep_card_eq bXuYs.2 hB.2 },
    have hBXuY : B ⊆ X ∪ Y := mem_powerset.mp ((m ¦ hXuY).indep_subset_powerset_ground hB.2.1),
    have hBX : B ∩ X ∈ (m ¦ hX).indep := have hsub : _ := restriction_trans hXXuY hXuY m,
      have hBX : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ inter_subset_left B X),
      hsub.symm ▸ (subset_restriction_indep hBX (inter_subset_right B X) hXXuY),
    have hBY : B ∩ Y ∈ (m ¦ hY).indep := have hsub : _ := restriction_trans hYXuY hXuY m,
      have hBY : _ := ((m ¦ hXuY).indep_of_subset_indep hB.2.1 $ inter_subset_left B Y),
      hsub.symm ▸ (subset_restriction_indep hBY (inter_subset_right B Y) hYXuY),
    have hBXr : card (B ∩ X) ≤ 𝓇 hX m := by { unfold rank_of_subset,
      exact card_of_indep_le_card_basis hBX bXs.2 },
    have hBYr : card (B ∩ Y) ≤ 𝓇 hY m := by { unfold rank_of_subset,
      exact card_of_indep_le_card_basis hBY bYs.2 },
    have hinter : (B ∩ X) ∩ (B ∩ Y) = B ∩ X ∩ Y := by simp only [finset.inter_assoc,
      inter_right_comm, inter_self, inter_comm, inter_left_comm],
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
        have := inter_subset_inter_right hB.1,
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

def rank_of_indep (m : of_indep E) : rank E :=
⟨λ X hX, rank_of_subset hX m,
λ X hX, ⟨dec_trivial, (by { have := basis_of_subset_spec hX m,
  simp only [bases_bases_of_indep, mem_powerset, filter_congr_decidable, mem_filter] at this,
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
r (union_subset hX hY) + r (subset.trans (inter_subset_left X Y) hX) ≤ r hX + r hY)

lemma congr_for_rank (rk : rank_R2_R3 E ) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E) (h : X = Y) :
rk.r hX = rk.r hY :=
by { congr, exact h }

-- Lemma 1.3.3
lemma rank_union_lemma (rk : rank_R2_R3 E) {X Y : finset α} (hX : X ⊆ E) (hY : Y ⊆ E)
  (hy : ∀ y, ∀ (h : y ∈ Y \ X), rk.r (by { rw mem_sdiff at h,
    exact insert_subset.mpr ⟨mem_of_subset hY h.1, hX⟩ }) = rk.r hX) :
  rk.r (union_subset hX hY) = rk.r hX :=
begin
  have hXuY : X ∪ Y ⊆ E := union_subset hX hY,
  induction h : (Y \ X) using finset.induction with a S ha ih generalizing X Y,
  { congr, have H := congr_arg (λ x, X ∪ x) h,
    simp only [union_sdiff_self_eq_union, union_empty] at H, exact H },
  { have h₁ : rk.r hX + rk.r hX ≥ rk.r hXuY + rk.r hX :=
    by { have haa : a ∈ Y \ X := h.substr (mem_insert_self a S),
    have haX : insert a X ⊆ E := insert_subset.mpr ⟨mem_of_subset hY (mem_sdiff.mp haa).1, hX⟩,
    have hins : insert a S ⊆ E := h ▸ subset.trans (sdiff_subset Y X) hY,
    have hS : S ⊆ E := subset.trans (subset_insert a S) hins,
    have hXS : X ∪ S ⊆ E := union_subset hX hS,
    have hrins : rk.r haX = rk.r hX := hy a haa, rw mem_sdiff at haa,
    have hrS : rk.r hXS = rk.r hX := by {
      exact ih hX hS (by { intros y Hy, have : y ∈ Y \ X := by { rw mem_sdiff at Hy,
        simp only [ext, mem_insert, mem_sdiff] at h,
        exact mem_sdiff.mpr ((h y).mpr $ or.inr Hy.1) }, exact hy y this })
        hXS (by { simp only [ext, mem_insert, mem_sdiff] at h ⊢,
          exact λ y, iff.intro (λ Hy, Hy.1) $ λ Hy, ⟨Hy, ((h y).mpr $ or.inr Hy).2⟩ }) },
    have hXuSiaX : (X ∪ S) ∩ insert a X ⊆ E := (subset.trans (inter_subset_right (X ∪ S)
      (insert a X)) haX),
    have hr₁ : rk.r (union_subset hXS haX) = rk.r hXuY :=
      by { exact congr_for_rank rk (union_subset hXS haX) hXuY (by {
        simp only [ext, mem_union, union_comm, mem_insert, mem_sdiff, union_insert,
          union_self, union_assoc] at h ⊢,
      exact λ x, iff.intro (λ hx, or.elim hx (λ hxa, or.inr $ hxa.substr haa.1) $
        λ H, or.elim H (by { intro hxS, exact or.inr ((h x).mpr $ or.inr hxS).1}) $
          by {exact (λ hxX, or.inl hxX) }) $
        λ hx, or.elim hx (by {intro hxX, exact or.inr (or.inr hxX)}) $
          by { intro hxY, by_cases hxX : x ∈ X,
            { exact or.inr (or.inr hxX) },
            { exact or.elim ((h x).mp ⟨hxY, hxX⟩) (λ H, or.inl H)
              (λ HS, or.inr $ or.inl HS) } } }) },
    have hr₂ : rk.r hXuSiaX = rk.r hX := by { congr,
      simp only [ext, mem_union, union_comm, mem_insert, mem_inter],
      exact λ x, iff.intro (λ hx, or.elim hx.1 (or.elim hx.2
        (λ H₁ H₂, false.elim $ ha $ H₁.subst H₂) $ λ h _, h) id) (λ hx, ⟨or.inr hx, or.inr hx⟩) },
    calc rk.r hX + rk.r hX = rk.r hXS + rk.r haX : by rw [hrS, hrins]
    ... ≥ rk.r (union_subset hXS haX) + rk.r hXuSiaX : rk.submodular (union_subset hX hS) haX
    ... = _ : by rw [hr₁, hr₂] },
  replace h₁ := le_of_add_le_add_right h₁,
  have h₂ : rk.r hX ≤ rk.r hXuY := rk.order_preserving (subset_union_left X Y) hXuY,
  exact nat.le_antisymm h₁ h₂, },
end

def indep_of_rank (r : rank E) : indep E :=
⟨sorry,
sorry,
sorry,
sorry,
sorry⟩

end matroid
