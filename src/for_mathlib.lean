import data.finset data.equiv.list

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

lemma sdiff_empty (E : finset α) : E \ ∅ = E :=
by simp only [ext, finset.not_mem_empty, and_true, iff_self, finset.mem_sdiff,
  not_false_iff, forall_true_iff]

lemma sdiff_subset (A B : finset α): A \ B ⊆ A :=
(sdiff_empty A).subst $ sdiff_subset_sdiff (subset.refl A) $ empty_subset B

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

/- lemma card_union_inter (A B : finset α) : card A + card B = card (A ∪ B) + card (A ∩ B) :=
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
end-/

/- proof by Kenny Lau https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/choosing.20from.20difference.20of.20finsets/near/133624012 -/
lemma nonempty_sdiff_of_card_lt {x y : finset α} (hcard : card x < card y) : (y \ x).nonempty :=
suffices ∃ e ∈ y, e ∉ x, by simpa only [finset.nonempty, exists_prop, finset.mem_sdiff],
by_contradiction $ λ H, not_le_of_lt hcard $ card_le_of_subset $ by simpa only [not_exists,
  exists_prop, not_and, not_not] using H

lemma nonempty_of_mem {a : β} {F : finset β} (h : a ∈ F) : F.nonempty := nonempty_of_ne_empty $ ne_empty_of_mem h

/- proof by chris hughes
https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/maximal.20finset.20in.20finset.20of.20finsets/near/133905271 -/
lemma max_fun_of_nonempty {F : finset β} (func : β → ℕ) (h : F.nonempty) :
  ∃ x ∈ F, ∀ g ∈ F, func g ≤ func x :=
let ⟨n, hn⟩ := (max_of_nonempty (h.image _) : ∃ a, a ∈ finset.max (F.image func)) in
let ⟨x, hx₁, hx₂⟩ := mem_image.1 (mem_of_max hn) in
  ⟨x, hx₁, hx₂.symm ▸ λ g hg, le_max_of_mem (mem_image.2 ⟨g, hg, rfl⟩) hn⟩

lemma min_fun_of_nonempty {F : finset β} (func : β → ℕ) (h : F.nonempty) :
  ∃ x ∈ F, ∀ g ∈ F, func x ≤ func g :=
let ⟨n, hn⟩ := (min_of_nonempty (h.image _) : ∃ a, a ∈ finset.min (F.image func)) in
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
