import matroid

open finset nat

namespace matroid
variables {E : Type*} [decidable_eq E] [fintype E]

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134721936 -/
def {u v} of_indep.filter_map {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β]
  [fintype α] [fintype β] (f : α → option β) (m : of_indep α) : of_indep β :=
{ indep := m.indep.image (filter_map f),
  empty_mem_indep := mem_image.2 ⟨∅, m.empty_mem_indep, rfl⟩,
  indep_of_subset_indep := λ x y, begin
    rw [mem_image, mem_image],
    rintro ⟨x, hx, rfl⟩ xy,
    refine ⟨x.filter (λ a, ∃ b ∈ f a, b ∈ y),
      m.indep_of_subset_indep hx (filter_subset _), _⟩,
    ext b, simp only [filter_congr_decidable, exists_prop, mem_filter,
      mem_filter_map, option.mem_def], split,
    { rintro ⟨a, ⟨ha, b', hb', hy⟩, hb⟩,
      rcases option.some_inj.1 (hb.symm.trans hb'),
      exact hy, },
    { intro hb,
      rcases mem_filter_map.1 (xy hb) with ⟨a, ha, ab⟩,
      exact ⟨a, ⟨ha, b, ab, hb⟩, ab⟩, },
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
    { have := ext.1 (card_eq_zero.1 h),
      simp only [not_and, mem_sdiff, not_not, iff_false, not_mem_empty] at this,
      exact (not_le_of_gt xy (card_le_of_subset this)).elim, },
    rcases m.indep_exch zi wi xy with ⟨a, ha, ii⟩, rw mem_sdiff at ha,
    rcases mem_of_card_filter_map cw ha.1 with ⟨b, ab⟩,
    by_cases bz : b ∈ filter_map f z,
    { rcases mem_filter_map.1 bz with ⟨a', ha', fa'⟩,
      let z' := erase (insert a z) a',
      have az' : a ∈ z',
      { refine mem_erase.2 ⟨mt _ ha.2, mem_insert_self _ _⟩,
        rintro rfl, exact ha', },
      have inz : insert a' z' = insert a z,
      { rw [insert_erase (mem_insert_of_mem ha')], },
      have zi' : z' ∈ m.indep :=
        m.indep_of_subset_indep ii (erase_subset _ _),
      have bz' : b ∈ filter_map f z' :=
        mem_filter_map.2 ⟨a, az', ab⟩,
      have hz' : z'.filter_map f = z.filter_map f,
      { rw [← insert_eq_of_mem bz', ← filter_map_insert_some f fa',
          inz, filter_map_insert_some f ab, insert_eq_of_mem bz], },
      have cz' : card z' = card z,
      { rw [← add_right_inj 1, ← card_insert_of_not_mem (not_mem_erase _ _),
          inz, card_insert_of_not_mem ha.2], },
      replace ih := ih z', rw [hz', cz'] at ih,
      refine ih cz zi' xy ((add_right_inj 1).1 $ eq.trans _ h),
      rw [← card_insert_of_not_mem (λ h, (mem_sdiff.1 h).2 az')],
      congr, ext c, simp only [not_imp_comm, mem_insert, not_and, mem_sdiff, mem_erase, ne.def], split,
      { rintro (rfl | ⟨h₁, h₂⟩),
        { exact ha, },
        { refine ⟨h₁, λ h₃, h₂ (λ h₄, _) (or.inr h₃)⟩,
          subst c,
          rcases inj_of_card_filter_map cw ha.1 h₁ ab fa',
          exact ha.2 h₃, } },
      { rintro ⟨h₁, h₂⟩,
        refine or_iff_not_imp_left.2 (λ h₃, ⟨h₁, _⟩),
        rintro h₄ (rfl | h₅),
        { exact h₃ rfl, }, { exact h₂ h₅, } } },
    { exact ⟨b, mem_sdiff.2 ⟨mem_filter_map.2 ⟨_, ha.1, ab⟩, bz⟩,
        mem_image.2 ⟨_, ii, by rw [filter_map_insert_some f ab]⟩⟩, },
  end }

/-- This is not the right definition! This removes all elements of X from each independent set,
but we want to remove all independent sets that contain elements of X.

This definition is like looking at "augmented" independence (i.e. we look at
which additions to a set X preserve independence)
-/
def partial_restrict {X : finset E} (x : E) : option {x : E // x ∈ X} :=
if h : x ∈ X then some ⟨x, h⟩ else none

lemma partial_restrict_eq {X : finset E} (x : {x : E // x ∈ X}) :
partial_restrict x.val = some x :=
begin
  convert dif_pos _,
  exact (subtype.eta x x.property).symm,
end

lemma partial_restrict_inj {X : finset E} (x : E) (y : {x : E // x ∈ X}) :
(partial_restrict x) = some y ↔ x = y.val :=
begin
  split,
  { intro h,
    by_cases hX : x ∈ X,
    { let x' : {x : E // x ∈ X} := ⟨x, hX⟩,
      rw partial_restrict_eq x' at h,
      cases h' : h,
      refl, },
    exfalso,
    have : partial_restrict x = none := dif_neg hX,
    rw this at h,
    cases h, },
  { rintro rfl,
    exact partial_restrict_eq y, },
end

def restriction_aug (m : of_indep E) (X : finset E) : of_indep {x : E // x ∈ X} :=
m.filter_map $ partial_restrict

lemma indep_of_restriction_aug (m : of_indep E) (X : finset E) (i : (finset {x : E // x ∈ X})) :
  ↑i ∈ m.indep ∧ ↑i ⊆ X → i ∈ (restriction_aug m X).indep :=
begin
  simp only [restriction_aug, of_indep.filter_map, mem_image, exists_prop],
  -- conv_lhs { congr, funext,
  --   rw [subset.antisymm_iff, subset_iff, subset_iff], },
  -- split,
  -- { rintro ⟨a, haindep, ha⟩,
  --   -- replace ha1 := ha1 (ha2 i.property),
  --   split,
  --   { subst ha,
  --     -- This goal is false.
  --     rw [finset_embed_coe_def, finset_embed],
  --     -- have :
  --     -- have := mem_filter_map.1,
  --     -- rw ha at this,
  --     sorry, },
  --   { rw subset_iff,
  --     intros x hx,
  --     have := finset_embed_subset_univ i,
  --     exact mem_of_subset this hx, }, },
  rintros ⟨hindep, hX⟩,
  use [↑i, hindep],
  rw [subset.antisymm_iff, subset_iff, subset_iff],
  split,
  { intros x hx,
    rw mem_filter_map at hx,
    rcases hx with ⟨a, ha, H⟩,
    rw [option.mem_def, partial_restrict_inj] at H,
    rw H at ha,
    exact finset_embed_mem.2 ha, },
  { intros x hx,
    rw mem_filter_map,
    replace hx : x.val ∈ ↑i := finset_embed_mem.1 hx,
    use [x.val, hx],
    rw [option.mem_def, partial_restrict_eq], }
end

end matroid
