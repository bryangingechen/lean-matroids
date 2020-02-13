/-
Copyright (c) 2019-2020 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen (with help from Mario Carneiro, Chris Hughes,
Kenny Lau and others in the Leanprover Zulip chat room).
-/
import for_mathlib

/-!
Matroids, after Chapter 1 of Oxley, Matroid Theory, 1992.

We begin with the two axiomatizations of matroids defined in Whitney's 1935 paper:
- matroids from independent sets
- matroids from circuits

Everything in this file is under the `matroid` namespace, so we have named the two
structures `of_indep` and `of_circuits`, respectively, so that their fully-qualified
names are `matroid.of_indep` and `matroid.of_circuits`.

-/

open finset

/-! § 1.1 Independent sets and circuits.
-/

namespace matroid

variables (E : Type*) [decidable_eq E] [fintype E]

/-- `of_indep E` is the type of matroids in the independent set representation
with ground set `E` (encoded in Lean as a `fintype`).

It has the following fields:
- `indep : finset (finset E)` : the set of independent subsets of E
- `empty_mem_indep` : axiom (I1), the empty set is independent.
- `indep_of_subset_indep` : axiom (I2), subsets of independent sets are independent.
- `indep_exch` : axiom (I3), the exchange axiom. Given two independent sets `x`, `y` with `x.card < y.card`, there exists `e ∈ y \ x` such that `insert e x` is independent.
-/
structure of_indep :=
(indep : finset (finset E))
-- (I1)
(empty_mem_indep : ∅ ∈ indep)
-- (I2)
(indep_of_subset_indep {x y : finset E} (hx : x ∈ indep) (hyx : y ⊆ x) : y ∈ indep)
-- (I3)
(indep_exch {x y : finset E} (hx : x ∈ indep) (hy : y ∈ indep) (hcard : card x < card y)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ indep)

namespace of_indep

/-- independent set matroids are printed by printing their independent sets -/
instance repr [has_repr E] : has_repr (of_indep E) :=
⟨λ m, has_repr.repr m.indep⟩

variable {E}

/-- two independent set matroids are equal if their independent sets agree -/
lemma eq_of_indep_eq : ∀ {M₁ M₂ : of_indep E}, M₁.1 = M₂.1 → M₁ = M₂
  | ⟨I₁, p₁, q₁, r₁⟩ ⟨I₂, p₂, q₂, r₂⟩ h :=
by simpa only []

/-- A circuit of an independent set matroid is a minimal dependent subset of
the ground set, i.e. all of its proper subsets are independent. -/
def is_circuit (x : finset E) (m : of_indep E) : Prop :=
x ∉ m.indep ∧ ∀ y, y ⊂ x → y ∈ m.indep

/-- The property of being a circuit is decidable.

proof by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finsets.2C.20decidable_mem.2C.20and.20filter/near/133708937 -/
instance decidable_circuit (x : finset E) (m : of_indep E) : decidable (is_circuit x m) :=
decidable_of_iff (x ∉ m.indep ∧ ∀ y ∈ x.powerset.erase x, y ∈ m.indep)
begin
  simp only [is_circuit, has_ssubset.ssubset, mem_powerset, and_imp, mem_erase],
  refine and_congr iff.rfl (forall_congr $ λ y, _),
  refine ⟨λ H h₁ h₂, H (mt _ h₂) h₁, λ H h₁ h₂, H h₂ $ mt _ h₁⟩,
  { rintro rfl, refl }, { exact subset.antisymm h₂, },
end

/-- The property of containing a circuit as a subset is decidable -/
instance decidable_circuit_subset (x : finset E) (m : of_indep E) :
  decidable (∃ (y : finset E) (H : y ⊆ x), is_circuit y m) :=
decidable_of_iff (∃ (y : finset E) (H : y ∈ x.powerset), is_circuit y m) $
  by simp only [exists_prop, mem_powerset]

/-- the set of all circuits of the independent set matroid `m` -/
def circuits (m : of_indep E) : finset (finset E) :=
univ.powerset.filter (λ S, is_circuit S m)

/-- A subset of the ground set is dependent if and only if it is contained
in a circuit. -/
theorem dep_iff_circuit_subset (x : finset E) (m : of_indep E) :
  x ∉ m.indep ↔ ∃ y ⊆ x, is_circuit y m :=
begin
  split,
  { intro hxd,
    rcases min_fun_of_nonempty card (nonempty_of_mem $
      mem_filter.mpr ⟨mem_powerset.mpr $ subset.refl x, hxd⟩) with ⟨a, ha, hamin⟩,
    have hax : a ⊆ x := mem_powerset.mp (mem_filter.mp ha).1,
    use [a, hax], split,
    { exact (mem_filter.mp ha).2, },
    { intros y hy, by_contra h,
      refine not_le_of_lt (card_lt_card hy) _,
      refine hamin y (mem_filter.mpr ⟨_, h⟩),
      refine mem_powerset.mpr (subset.trans _ hax),
      exact (le_of_lt $ lt_iff_ssubset.mpr hy), }, },
  { rintros ⟨a, ⟨hax, hacirc⟩⟩ hxi,
    exact hacirc.1 (m.indep_of_subset_indep hxi hax), },
end

end of_indep

open of_indep
variable (E)

/-- `of_circuits E` is the type of matroids in the circuit representation with ground set `E` (encoded in Lean as a fintype).

It has the following fields:
- `circuits : finset (finset E)` : the set of circuits of E
- `empty_not_mem_circuits` : axiom (C1), the empty set is not a circuit.
- `circuits_eq_of_subset` : axiom (C2), if `x` and `y` are circuits and `x ⊆ y` then `x = y`.
- `circuit_elim` : axiom (C3), the (weak) circuit elimination axiom.
  Given two unequal circuits `x`, `y` and an element `e ∈ x ∩ y`, there exists a circuit `z ⊆ (x ∪ y).erase e`.
 -/
structure of_circuits :=
(circuits : finset (finset E))
-- (C1)
(empty_not_mem_circuits : ∅ ∉ circuits)
-- (C2)
(circuits_eq_of_subset {x y : finset E} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ⊆ y) : x = y)
-- (C3)
(circuit_elim {x y : finset E} {e : E} (hx : x ∈ circuits) (hy : y ∈ circuits) (hxy : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ circuits ∧ z ⊆ (x ∪ y).erase e)

namespace of_circuits

/-- circuit matroids are printed by printing their circuits -/
instance repr [has_repr E] : has_repr (of_circuits E) :=
⟨λ c, has_repr.repr c.circuits⟩

variable {E}

/-- two circuit matroids are equal if they have the same sets of circuits -/
lemma eq_of_circ_eq : ∀ {C₁ C₂ : of_circuits E}, C₁.1 = C₂.1 → C₁ = C₂
  | ⟨c₁, p₁, q₁, r₁⟩ ⟨c₂, p₂, q₂, r₂⟩ h :=
by simpa only []

end of_circuits

namespace of_indep

variable {E}

/-- "it is easy to see that..."
If x and y are members of m.circuits,  and x ⊆ y, then x = y.
-/
private lemma C2 (m : of_indep E) (x y : finset E) (hx : x ∈ m.circuits)
  (hy : y ∈ m.circuits) (hxy : x ⊆ y) : x = y :=
begin
  simp only [circuits, is_circuit, mem_filter] at hx hy hxy,
  have hnxy : ¬x ⊂ y := λ h, hx.2.1 $ hy.2.2 x h,
  rw [←le_iff_subset, le_iff_eq_or_lt] at hxy,
  cases hxy,
  { exact hxy, },
  { exact (hnxy hxy).elim, },
end

/-- Lemma 1.1.3. If `x` and `y` are distinct members of `m.circuits` and `e ∈ x ∩ y`,
then there is a member `z` of `m.circuits` such that `z ⊆ (x ∪ y).erase e` -/
private lemma C3 (m : of_indep E) (x y : finset E) (e : E) (hx : x ∈ m.circuits)
  (hy : y ∈ m.circuits) (hxny : x ≠ y) (he : e ∈ x ∩ y) :
  ∃ z, z ∈ m.circuits ∧ z ⊆ (x ∪ y).erase e :=
begin
  -- by C2, `y - x` is nonempty,
  have hxmy : (x \ y).nonempty := nonempty_of_ne_empty
    (mt subset_iff_sdiff_eq_empty.mpr (mt (C2 m x y hx hy) hxny)), clear hxny,
  -- so we can choose an element `a` from this set
  rcases hxmy with ⟨a, ha⟩,
  simp only [circuits, mem_powerset, mem_filter, mem_sdiff, mem_inter]
    at ha hx hy he,
  -- as `x` is a minimal dependent set, `x.erase a ∈ m.indep`
  have hxai : x.erase a ∈ m.indep := by { unfold is_circuit at hx,
    exact hx.2.2 (x.erase a) (erase_ssubset ha.1) },
  -- consider the set F of all subsets of `x ∪ y` which
  -- contain `x.erase a` and are independent
  let F := (x ∪ y).powerset.filter (λ S, x.erase a ⊆ S ∧ S ∈ m.indep),
  -- F contains `x.erase a`
  have hxaF : x.erase a ∈ F := mem_filter.2 ⟨mem_powerset.mpr $ subset.trans (x.erase_subset a) $
    subset_union_left x y, ⟨subset.refl _, hxai⟩⟩, clear hxai,
  -- hence F is nonempty and we can choose a maximal subset `I` from `F`
  rcases (max_fun_of_nonempty card $ nonempty_of_mem hxaF) with ⟨I, ⟨hIF, hI⟩⟩, clear hxaF,
  have hIxuy : I ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hIF).1,
  have hIFindep : I ∈ m.indep := (mem_filter.mp hIF).2.2,
  have hIFxa : x.erase a ⊆ I := (mem_filter.mp hIF).2.1,
  -- if we can find a subset of `I` that is a circuit, we have a contradiction
  have hIdep : _ → I ∉ m.indep := (dep_iff_circuit_subset I m).2,
  have haniI : a ∉ I := by { intro H,
    have hxI : x ⊆ I := (insert_erase ha.1) ▸ insert_subset.mpr ⟨H, hIFxa⟩,
    refine hIdep _ hIFindep,
    use [x, hxI], exact hx.2, }, clear hx,
  -- since `y` is a circuit, some element `g` of `y` is not in `I`
  have hEg : ∃ g ∈ y, g ∉ I :=
    by { have hIdep2 := mt hIdep, simp only [not_exists, exists_prop, not_and, not_not]
      at hIdep2,
    have hyI0 := mt (hIdep2 hIFindep y), simp only [not_not] at hyI0,
    have hYI : ¬y ⊆ I := hyI0 hy.2, clear hyI0,
    have : ∃ x, x ∈ y \ I := (nonempty_of_ne_empty (mt subset_iff_sdiff_eq_empty.mpr hYI)).bex,
    simp only [mem_sdiff] at this, simpa only [exists_prop], }, clear hy hIdep,
  rcases hEg with ⟨g, ⟨hgy, hgnI⟩⟩,
  -- as `a ∈ x.erase y`, `a` and `g` are distinct
  have hga : g ≠ a := λ H, ha.2 (H ▸ hgy),
  have hIag : I ⊆ ((x ∪ y).erase a).erase g :=
    subset_iff.mpr (λ xx hxx, mem_erase.mpr ⟨λ hgg, hgnI $ hgg ▸ hxx,
      mem_erase.mpr ⟨λ hgga, haniI $ hgga ▸ hxx, mem_of_subset hIxuy hxx⟩⟩),
  have haxuy : a ∈ x ∪ y := mem_union_left y ha.1, clear ha,
  have hcardxye : ((x ∪ y).erase a).card = (x ∪ y).card.pred :=
    card_erase_of_mem haxuy, clear haxuy,
  have hpcard : (x ∪ y).card.pred > 0 := by { rw ←hcardxye,
    exact card_pos.mpr (nonempty_of_mem $ mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), },
  -- we show the inequality `I.card < ((x ∪ y).erase e).card`
  have hcard : I.card < ((x ∪ y).erase e).card :=
    calc I.card ≤ (((x ∪ y).erase a).erase g).card : card_le_of_subset hIag
    ... = (x ∪ y).card.pred.pred : by rw [card_erase_of_mem
      (mem_erase.mpr ⟨hga, mem_union_right x hgy⟩), hcardxye]
    ... < ((x ∪ y).erase e).card :
      by { rw [card_erase_of_mem (mem_union_left y he.1),
      ←nat.succ_pred_eq_of_pos hpcard], exact nat.lt_succ_self _, },
  clear hga hIag hcardxye hpcard he hgy hgnI g,
  -- assume that `(x ∪ y).erase e` does not contain a circuit
  by_contra h, simp only [circuits, mem_powerset, not_exists, and_imp,
    mem_filter, not_and] at h,
  have : (∀ x' : finset E, x' ⊆ (x ∪ y).erase e → ¬is_circuit x' m) :=
    λ x1 hx1, (mt $ h x1 $ subset_univ x1) $ not_not.mpr hx1,
  -- then `(x ∪ y).erase e` is independent
  have hindep := mt (dep_iff_circuit_subset ((x ∪ y).erase e) m).mp,
  simp only [not_exists, exists_prop, not_and, not_not] at hindep,
  replace hindep : (x ∪ y).erase e ∈ m.indep := hindep this, clear this,
  -- now apply I3, taking `x` and `y` to be `I` and `(x ∪ y).erase e`, respectively
  rcases (m.indep_exch hIFindep hindep hcard) with ⟨El, ⟨hElxy, hElindep⟩⟩,
  clear hcard hIFindep hindep,
  -- the resulting independent set `insert El I` is in `F`
  have hElF : insert El I ∈ F := mem_filter.mpr ⟨mem_powerset.mpr
    (insert_subset.mpr ⟨(mem_erase.mp (mem_sdiff.mp hElxy).1).2, hIxuy⟩),
    ⟨subset.trans hIFxa (subset_insert El I), hElindep⟩⟩,
  -- and is larger than `I`
  have hcardEl : I.card < (insert El I).card :=
    by { rw card_insert_of_not_mem (mem_sdiff.mp hElxy).2,
    exact lt_add_one I.card, },
  -- which contradicts the maximality of `I`
  exact not_lt.mpr (hI (insert El I) hElF) hcardEl,
end

/-- `m.to_circuits` constructs the circuit matroid from the independent sets
matroid `m` -/
def to_circuits (m : of_indep E) : of_circuits E :=
{ circuits := m.circuits,
  empty_not_mem_circuits :=
    begin
      simp only [circuits, is_circuit, mem_filter, not_and],
      intros h h1, exfalso,
      exact h1 m.empty_mem_indep,
    end,
  circuits_eq_of_subset := C2 m,
  circuit_elim := C3 m }

@[simp] lemma to_circuits_circuits_eq_circuits (m : of_indep E) :
  m.to_circuits.circuits = m.circuits := rfl

end of_indep

namespace of_circuits
open of_indep
variable {E}

/-- all independent sets of the matroid `C` in the circuit representation.
These are the subsets of the ground set `E` which contain no circuit.
-/
def indep (C : of_circuits E) : finset (finset E) :=
univ.powerset.filter (λ S, ∀ c ∈ C.circuits, ¬c ⊆ S)

/-- first part of Theorem 1.1.4: Let `E` be a set and `C` be a collection of subsets
of `E` satisfying C1-C3. Let `I` be the collection of subsets of `E` that contain
no member of `C`. Then `(E,I)` satisfies C2 -/
private lemma I2 (C : of_circuits E) (x y : finset E) : x ∈ C.indep → y ⊆ x →
  y ∈ C.indep :=
begin
  simp only [indep, mem_powerset, and_imp, mem_filter],
  intros _ hx hxy, split, { exact subset_univ y, },
  { intros c hc H, exact hx c hc (subset.trans H hxy), },
end

/-- second part of Theorem 1.1.4; Let `E` be a set and `C` be a collection of subsets
of `E` satisfying C1-C3. Let `I` be the collection of subsets of `E` that contain
no member of `C`. Then `(E,I)` satisfies C3 -/
private lemma I3 (C : of_circuits E) (x y : finset E)
  -- Let `x` and `y` be members of `I` and `x.card < y.card`
  (hx : x ∈ C.indep) (hy : y ∈ C.indep) (hcardxy : x.card < y.card)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ C.indep :=
begin
  unfold indep at ⊢,
  simp only [indep, mem_powerset, mem_filter] at hx hy,
  -- assume I3 fails for the pair (x,y)
  by_contra h,
  simp only [mem_powerset, not_exists, and_imp, mem_filter, not_and, mem_sdiff] at h,
  -- consider the set `F` of all subsets of `x ∪ y` which are members of `I` with more elements than `x`
  let F := (x ∪ y).powerset.filter (λ S, (∀ c ∈ C.circuits, ¬c ⊆ S) ∧ x.card < S.card),
  -- `F` contains `y` and is nonempty
  have hyF : y ∈ F := mem_filter.mpr ⟨mem_powerset.mpr $ subset_union_right x y,
    ⟨hy.2, hcardxy⟩⟩,
  -- choose a subset `z` contained in `F` such that `(x \ z).card` is minimal
  rcases (min_fun_of_nonempty (λ f, (x \ f).card) $ nonempty_of_mem hyF) with ⟨z, ⟨hz, hminz⟩⟩,
  clear hcardxy hyF,
  have hzxuy : z ⊆ x ∪ y := mem_powerset.mp (mem_filter.mp hz).1,
  replace hz := (mem_filter.mp hz).2,
  -- let `a` be an element of `z \ x`
  rcases (nonempty_sdiff_of_card_lt hz.2) with ⟨a, ha⟩,
  rw mem_sdiff at ha,
  -- "since I3 fails, `x \ z` is nonempty"...
  have hxsdiffz : (x \ z).nonempty :=
    by { apply nonempty_of_ne_empty, intro H,
    have Hxsubz : x ⊆ z := subset_iff_sdiff_eq_empty.mpr H,
    have hay : a ∈ y := (mem_union.mp $ mem_of_subset hzxuy ha.1).elim
      (λ Hax, (ha.2 Hax).elim) id,
    have haindep : insert a x ∈ C.indep := I2 C z (insert a x)
      (by { simp only [indep, mem_powerset, mem_filter],
      exact ⟨subset_univ z, hz.1⟩, })
      (insert_subset.mpr ⟨ha.1, Hxsubz⟩),
    simp only [indep, mem_powerset, mem_filter] at haindep,
    -- [`h` is the negation of I3]
    exact h a hay ha.2 haindep.1 haindep.2, },
  -- choose an element `e` from `x \ z`
  rcases hxsdiffz with ⟨e, he⟩, clear h ha,
  rw mem_sdiff at he,
  -- for each `f`, let T_f be `(insert e z).erase f`
  let T : E → finset E := λ f, (insert e z).erase f,
  -- for each `f` in `z \ x`, `T f` is in `x ∪ y` and
  have hTf1 : ∀ f, f ∈ z \ x → T f ⊆ x ∪ y :=
    by { intros f hf, rw [mem_sdiff] at hf,
    rw [subset_iff],
    intros gg hgg, simp only [mem_insert, mem_erase, ne.def] at hgg,
    simp only [mem_union],
    rcases hgg.2 with rfl | hggz,
    { exact or.inl he.1, },
    exact (mem_union.mp $ mem_of_subset hzxuy hggz), },
  -- for each `f` in `z \ x`, we have `(x \ T f).card < (x \ z).card`
  have hTf2 : ∀ f, f ∈ z \ x → (x \ T f).card < (x \ z).card :=
    by { intros f hf, rw mem_sdiff at hf,
    suffices H : x \ T f ⊂ x \ z, exact card_lt_card H,
    by { simp only [ssubset_iff, exists_prop, mem_insert, not_forall_not, not_and,
                    mem_sdiff, mem_erase],
      use e, split,
      { intro _, split,
        { intro hef, exact hf.2 (hef ▸ he.1), },
        { exact or.inl rfl, }, },
      { rw [subset_iff],
        intros gg hgg,
        simp only [mem_insert, not_and, mem_sdiff, mem_erase, ne.def] at hgg,
        have ggnef : gg ≠ f := by { intro ggef,
          rcases hgg with gge | H,
          { exact ((gge.symm ▸ he.2) $ ggef.substr hf.1), },
          { exact (ggef.substr hf.2) H.1, }, },
        have he0 : e ∈ x \ z := mem_sdiff.mpr he,
        rcases hgg with gge | H,
        { exact gge.symm ▸ he0, },
        { exact mem_sdiff.mpr ⟨H.1, λ ggz, (H.2 ggnef) $ or.inr ggz⟩, }, }, }, },
  -- Therefore `T f` is not in `C.indep`
  have hTfindep : ∀ f, f ∈ z \ x → T f ∉ C.indep :=
    by { intros f hf,
    simp only [indep, mem_powerset, mem_filter, not_and],
    intros hTfE H,
    have HTf1 : T f ⊆ x ∪ y := hTf1 f hf,
    have HTf2 : (x \ T f).card < (x \ z).card := hTf2 f hf,
    rw mem_sdiff at hf,
    have HTfcard : z.card = (T f).card :=
      by { simp only [card_erase_of_mem (mem_insert.mpr $ or.inr hf.1),
      card_insert_of_not_mem he.2, mem_insert, card_insert_of_not_mem, nat.pred_succ], },
    replace HTfcard : x.card < (T f).card := HTfcard ▸ hz.2,
    have : T f ∈ F := mem_filter.mpr ⟨mem_powerset.mpr HTf1, ⟨H, HTfcard⟩⟩,
    exact not_lt.mpr (hminz (T f) this) HTf2, },
  -- so `T f` contains a member C_f of `C.circuits`
  have hTfC : ∀ f, f ∈ z \ x → ∃ c ∈ C.circuits, c ⊆ T f :=
    by { intros f hf,
    have : T f ∉ C.indep := hTfindep f hf,
      simp only [indep, mem_powerset, mem_filter, not_and] at this,
    have hfc := this (subset.trans (hTf1 f hf) $ union_subset hx.1 hy.1),
    by_contra H, simp only [not_exists, exists_prop, not_and] at H, contradiction, },
  -- Let `g` be an element of `z \ x`
  rcases (nonempty_sdiff_of_card_lt hz.2) with ⟨g, hg⟩,
  -- and let C_g be the circuit contained in T g
  rcases (hTfC g hg) with ⟨Cg, ⟨HCg1, HCg2⟩⟩,
  clear hTf1 hTf2 hTfindep hg hy hminz hzxuy,
  have hCgsub : Cg ⊆ insert e z := subset.trans HCg2 ((insert e z).erase_subset g),
  rw [subset_iff] at HCg2,
  have HCgzx : (Cg ∩ (z \ x)).nonempty := by {
    apply nonempty_of_ne_empty,
    -- if `Cg ∩ (z \ x) = ∅`,
    intro H,
    -- then `Cg ⊆ x` leads to a contradiction
    suffices : Cg ⊆ x, from hx.2 Cg HCg1 this,
    -- we show this by showing `Cg ⊆ (insert e (x ∩ z)).erase g`
    suffices H1 : Cg ⊆ (insert e (x ∩ z)).erase g, from
    -- and `(insert e (x ∩ z)).erase g ⊆ x`
    suffices H2 : (insert e (x ∩ z)).erase g ⊆ x, from
    subset.trans H1 H2,
    show (insert e (x ∩ z)).erase g ⊆ x, by { rw [subset_iff],
      intros gg hgg,
      simp only [mem_insert, mem_erase, mem_inter] at hgg,
      rcases hgg.2 with gge | ggxggz,
      { exact gge.symm ▸ he.1, },
      { exact ggxggz.1, }, },
    show Cg ⊆ (insert e (x ∩ z)).erase g, by
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
        { exact or.inr ⟨H hgg ggz, ggz⟩, }, }, }, },
  clear HCg2 he hx,
  -- therefore there is an element `h0` in `Cg ∩ (z \ x)`
  rcases HCgzx with ⟨h0, hh0⟩,
  rw [mem_inter] at hh0,
  -- let `Ch0` be the circuit contained in `T h0`
  rcases (hTfC h0 hh0.2) with ⟨Ch0, ⟨hCh0circ, hCh0T⟩⟩, clear hTfC,
  have hCgneCh0 : Cg ≠ Ch0 :=
    λ H, have hh0Ch0 : h0 ∉ Ch0 := λ HH, (mem_erase.mp $
      mem_of_subset hCh0T HH).1 rfl, (H.symm ▸ hh0Ch0) hh0.1,
  have hCh0sub : Ch0 ⊆ insert e z :=
    subset.trans hCh0T ((insert e z).erase_subset h0),
  -- now `e ∈ Cg ∩ Ch0`
  have heCgCh0 : e ∈ Cg ∩ Ch0 :=
    by { rw mem_inter, split,
      { by_contra heCg, have hCgz : Cg ⊆ z :=
          (erase_eq_of_not_mem heCg) ▸ (subset_insert_iff.mp hCgsub),
        exact hz.1 Cg HCg1 hCgz },
      { by_contra heCh0, have hCh0z : Ch0 ⊆ z :=
          (erase_eq_of_not_mem heCh0) ▸ (subset_insert_iff.1 hCh0sub),
        exact hz.1 Ch0 hCh0circ hCh0z }, },
  -- so C3 implies that there is a member `CC` of `C.circuits` such that `CC ⊆ (Cg ∪ Ch0).erase e`
  rcases (C.circuit_elim HCg1 hCh0circ hCgneCh0 heCgCh0) with ⟨CC, ⟨hCCcirc, hCCCguCh0⟩⟩,
  clear HCg1 hCh0circ hCgneCh0 heCgCh0,
  -- both `Cg` and `Ch0` are subsets of `insert e z`, so `CC ⊆ z`,
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
      { exact Htz, }, },
    { rcases (mem_insert.mp $ hCh0sub htCh0) with Hte | Htz,
      { exfalso, exact htCguCh0.1 Hte },
      { exact Htz, }, }, },
  -- which is a contradiction; we conclude that I3 holds.
  exact hz.1 CC hCCcirc hCCz,
end

def to_indep (C : of_circuits E) : of_indep E :=
{ indep := C.indep,
  empty_mem_indep := mem_filter.mpr
    ⟨empty_mem_powerset univ, λ c hc H, C.empty_not_mem_circuits $ (subset_empty.mp H) ▸ hc⟩,
  indep_of_subset_indep := I2 C,
  indep_exch := I3 C, }

/-- third part of Theorem 1.1.4: Let `E` be a set and `C` be a collection of subsets
of `E` satisfying C1-C3. Let `I` be the collection of subsets of `E` that contain
no member of `C`. Then `(E,I)` has `C` as its collection of circuits. -/
theorem circ_indep_circ : ∀ C : of_circuits E, C.to_indep.to_circuits = C
  | ⟨c₁, p₁, q₁, r₁⟩ :=
begin
  simp only [to_indep, to_circuits, of_circuits.indep,
  of_indep.circuits, is_circuit, ext, mem_filter, mem_powerset, and_imp, not_and],
  intro c,
  split,
  { rintro ⟨hc, ⟨Hc1, Hc2⟩⟩,
    have : ∃ c' ∈ c₁, c' ⊆ c := by { have := not_forall.mp (Hc1 hc),
    simpa only [exists_prop, not_forall_not], },
    rcases this with ⟨c', ⟨hc', hcc'⟩⟩,
    by_cases h : c = c',
    { exact h.symm ▸ hc' },
    { have hc'lt : c' ⊂ c := lt_of_le_of_ne (le_iff_subset.mpr hcc') (ne.symm h),
      have : c' ∉ c₁ := mt ((Hc2 c' hc'lt).2 c') (not_not.mpr $ subset.refl c'),
      exact (this hc').elim, }, },
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
        exact (not_le_of_lt Hc) (le_of_eq r.symm), }, }, },
end

end of_circuits

namespace of_indep
open of_circuits
variable {E}

/-- Let `M` be an independent set matroid and let `C` be `M.to_circuits`,
its circuit matroid. Then `C.to_indep`, its independent set matroid, is equal to
`M`. -/
theorem indep_circ_indep (M : of_indep E) : M.to_circuits.to_indep = M :=
suffices M.to_circuits.to_indep.indep = M.indep, from eq_of_indep_eq this,
begin
  simp only [to_circuits, to_indep, of_indep.circuits, of_circuits.indep,
    ext, mem_powerset, and_imp, mem_filter],
  intro I,
  have hI : I ∈ M.indep → I ⊆ univ := λ H, subset_univ I,
  rw [←and_iff_right_of_imp hI, and_congr_right],
  intro hIE, have := not_iff_not_of_iff (dep_iff_circuit_subset I M),
  simp only [not_exists, exists_prop, not_and, not_not] at this,
  rw [this, forall_congr],
  intro a, split,
  { intros h h₁ h₂, exact h (subset.trans h₁ hIE) h₂ h₁, },
  { intros h h₁ h₂ h₃, exact (h h₃) h₂, },
end

/-- the independent set matroids and circuit matroids on a ground set `E` are
equivalent (there are mutually inverse functions between them) -/
def indep_equiv_circ : of_indep E ≃ of_circuits E :=
{ to_fun := to_circuits,
  inv_fun := to_indep,
  left_inv := indep_circ_indep,
  right_inv := circ_indep_circ, }

/-- Proposition 1.1.6: Suppose that `I` is an independent set in a matroid `m` and
`e` is an element of `m` such that `I ∪ e` is dependent. Then `M` has a unique
circuit contained in `I ∪ e` and this circuit contains `e`. -/
theorem existsu_circuit_of_dep_of_insert {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  ∃ c, c ∈ m.circuits ∧ c ⊆ insert e I ∧ e ∈ c ∧
  ∀ c', c' ∈ m.circuits → c' ⊆ insert e I → c' = c :=
begin
  simp only [circuits, mem_powerset, and_imp, mem_filter],
  have hIE : I ⊆ univ, from subset_univ I,
  have hc : ∃ (y : finset E) (H : y ⊆ insert e I), is_circuit y m,
    from (dep_iff_circuit_subset (insert e I) m).mp hIe, clear hIe,
  -- evidently `insert e I` contains a circuit `c`
  rcases hc with ⟨c, ⟨hceI, hccirc⟩⟩,
  have hcE : c ⊆ univ := subset_univ c,
  -- moreover, every circuit contained in `insert e I` must contain `e`
  have hecirc : ∀ c' ⊆ insert e I, is_circuit c' m → e ∈ c' :=
    by { intros c' hc'eI hc'circ,
      have h₁ := subset_insert_iff.mp hc'eI,
      by_contra h,
      have h₂ := (erase_eq_of_not_mem h).symm,
      have h₃ : c' ⊆ I := calc
      c' = c'.erase e : h₂
      ... ⊆ I : h₁,
      refine (dep_iff_circuit_subset I m).mpr _ hI,
      use [c', h₃], exact hc'circ, },
  have hec : e ∈ c := hecirc c hceI hccirc,
  use c,
  split, { exact ⟨hcE, hccirc⟩, }, { split, { exact hceI, }, { split, { exact hec, },
  { intros c' hc'E hc'circ hc'eI,
  -- if `c'` is such a circuit
  have hec' : e ∈ c' := hecirc c' hc'eI hc'circ,
  -- we have `(c ∪ c').erase e ⊆ I`
  have hcuc'eI : (c ∪ c').erase e ⊆ I :=
    by { simp only [subset_iff, and_imp, mem_union, mem_insert, mem_erase, ne.def]
      at hceI hc'eI ⊢,
      rintros a hane (H | H),
      { rcases (hceI H) with H' | H', { exact (hane H').elim, }, { exact H', }, },
      { rcases (hc'eI H) with H' | H', { exact (hane H').elim ,}, { exact H', }, }, },
  have : (c ∪ c').erase e ∈ m.indep := m.indep_of_subset_indep hI hcuc'eI,
  -- and `c'` is distinct from `c`
  by_contra h,
  -- then by C3,
  have C3 := m.to_circuits.circuit_elim,
    simp only [to_circuits, circuits, mem_powerset, and_imp,
      filter_congr_decidable, mem_filter, mem_inter] at C3,
  -- `(c ∪ c').erase e` contains a circuit `c₀`
  rcases (C3 hcE hccirc hc'E hc'circ (ne.symm h) hec hec') with ⟨c₀, ⟨⟨hc₀, hc₀circ⟩, hc₀erase⟩⟩,
  -- this is a contradiction, since we just showed this was in `I`.
  refine (dep_iff_circuit_subset I m).mpr _ hI,
  use [c₀, subset.trans hc₀erase hcuc'eI], exact hc₀circ, }, }, },
end

section encodable
variable [encodable E]

def circuit_of_dep_of_insert_indep {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) : finset E :=
encodable.choose (existsu_circuit_of_dep_of_insert hI hIe)

local notation `cdii` := circuit_of_dep_of_insert_indep

lemma circuit_of_dep_of_insert_indep_spec {I : finset E} {e : E} {m : of_indep E}
  (hI : I ∈ m.indep) (hIe : insert e I ∉ m.indep) :
  cdii hI hIe ∈ m.circuits ∧ cdii hI hIe ⊆ insert e I ∧
  e ∈ cdii hI hIe ∧ ∀ c', c' ∈ m.circuits →
  c' ⊆ insert e I → c' = cdii hI hIe :=
encodable.choose_spec (existsu_circuit_of_dep_of_insert hI hIe)

end encodable

end of_indep

/-! § 1.2. Bases
 -/

namespace of_indep
variable {E}

/-- an independent set is a basis if it is maximal, i.e. all sets strictly
containing it are dependent. -/
def is_basis (x : finset E) (m : of_indep E) : Prop :=
x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)

/-- the property of being a basis is decidable -/
instance decidable_basis (x : finset E) (m : of_indep E) : decidable (is_basis x m) :=
decidable_of_iff (x ∈ m.indep ∧ (∀ y, x ⊂ y → y ∉ m.indep)) $
  by simp only [is_basis, iff_self, finset.mem_powerset]

/-- Lemma 1.2.1. If `x` and `y` are bases of a matroid `m`, then `x.card = y.card` -/
theorem bases_of_indep_card_eq {x y : finset E} {m : of_indep E} : is_basis x m → is_basis y m →
  card x = card y :=
begin
  intros hx hy,
  by_contra heq,
  wlog h : card x < card y using [x y, y x],
  { exact lt_or_gt_of_ne heq, },
  rcases (m.indep_exch hx.1 hy.1 h) with ⟨e, ⟨he1, he2⟩⟩,
  have hememx : e ∉ x := (mem_sdiff.mp he1).2,
  exact (hx.2 (insert e x) $ ssubset_insert hememx) he2,
end

/-- every independent set can be extended to a basis -/
theorem exists_basis_containing_indep {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  ∃ B : finset E, I ⊆ B ∧ is_basis B m :=
begin
  let F : finset (finset E) := m.indep.filter (λ a, I ⊆ a),
  have FI : I ∈ F := mem_filter.mpr ⟨h, subset.refl I⟩,
  rcases (max_fun_of_nonempty card $ nonempty_of_mem FI) with ⟨B, ⟨HBF, Hg⟩⟩,
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

/-- if the ground set is encodable, we can construct a basis containing an
independent set -/
def basis_containing_indep {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  finset E :=
encodable.choose $ exists_basis_containing_indep h

local notation `bci` := basis_containing_indep

lemma basis_containing_indep_spec {I : finset E} {m : of_indep E} (h : I ∈ m.indep) :
  I ⊆ bci h ∧ is_basis (bci h) m :=
encodable.choose_spec $ exists_basis_containing_indep h

end encodable

/-- any subset with cardinality greater than that of a basis is dependent -/
theorem dep_of_card_gt_card_basis {x B : finset E} {m : of_indep E} (hB : is_basis B m)
  (hcard : card B < card x) : x ∉ m.indep :=
begin
  intro hxI,
  rcases (exists_basis_containing_indep hxI) with ⟨B', ⟨hxB', hB'basis⟩⟩,
  refine ne_of_lt (lt_of_lt_of_le hcard $ card_le_of_subset hxB') _,
  exact bases_of_indep_card_eq hB hB'basis,
end

/-- the cardinality of any independent set is less than or equal to that of any
basis -/
theorem card_of_indep_le_card_basis {x B : finset E} {m : of_indep E} (hx : x ∈ m.indep)
  (hB : is_basis B m) : card x ≤ card B :=
begin
  by_contra h,
  exact dep_of_card_gt_card_basis hB (lt_of_not_ge h) hx,
end

end of_indep

variable (E)
/-- `of_bases E` is the type of matroids in the basis representation on the ground set
`E` (encoded in Lean as a `fintype`).

It has the following fields:
- `bases : finset (finset E)`: the set of bases
- `bases_not_empty`: axiom (B1), the set of bases is nonempty
- `basis_exch`: axiom (B2), a basis exchange axiom. If `x` and `y` are bases and
  `e ∈ x \ y` then there exists an element `a ∈ y \ x` such that `insert a (x.erase e)`
  is a basis.
-/
structure of_bases :=
(bases : finset (finset E))
-- (B1)
(bases_not_empty : bases.nonempty)
-- (B2)
(basis_exch {x y : finset E} {e : E} (hx : x ∈ bases) (hy : y ∈ bases) (he : e ∈ x \ y)
  : ∃ a, a ∈ y \ x ∧ insert a (x.erase e) ∈ bases)

namespace of_bases
/-- a basis matroid is printed by printing its bases -/
instance bases_repr [has_repr E] : has_repr (of_bases E) :=
⟨λ b, has_repr.repr b.bases⟩

variable {E}
/-- two basis matroids are equal if their bases are equal -/
lemma eq_of_base_eq : ∀ {B₁ B₂ : of_bases E}, B₁.1 = B₂.1 → B₁ = B₂
  | ⟨b₁, p₁, q₁⟩ ⟨b₂, p₂, q₂⟩ h :=
by simpa only []

end of_bases

namespace of_indep

variable {E}

/-- the set of all bases of an independent set matroid -/
def bases (m : of_indep E) : finset (finset E) :=
univ.powerset.filter (λ S, is_basis S m)

/-- if `m` is a matroid and `m.bases` its set of bases, then "by (I1)",
the set of bases is nonempty -/
private lemma B1 (m : of_indep E) : m.bases.nonempty :=
begin
  rcases max_fun_of_nonempty card (nonempty_of_mem m.empty_mem_indep)
    with ⟨a, ⟨ha1, hg⟩⟩,
  use a,
  simp only [bases, mem_filter, mem_powerset, not_and, iff_false,
    subset_univ, true_and, is_basis, ha1],
  intros F Fcontainsa Findep,
  refine not_le_of_lt (card_lt_card Fcontainsa) _,
  exact hg F Findep,
end

/- Lemma 1.2.2. If `x` and `y` are members of `m.bases` and `e ∈ x \ y` then
there is an element `a` of `y \ x` such that `insert a (x.erase e) ∈ m.bases` -/
private lemma B2 (m : of_indep E) : ∀ (x y : finset E) (e : E), x ∈ m.bases →
  y ∈ m.bases → e ∈ x \ y →
  ∃ a, a ∈ y \ x ∧ insert a (x.erase e) ∈ m.bases :=
begin
  simp only [bases, filter_and, mem_filter, mem_sdiff,
    mem_powerset, and_imp],
  intros x y e hxE hxB hyE hyB hex hey, clear hxE hyE,
  -- both `x.erase e` and `y` are independent sets
  have hxr : x.erase e ∈ m.indep := m.indep_of_subset_indep hxB.1 (erase_subset e x),
  -- moreover, `(x.erase e).card < y.card`,
  have hcard : (x.erase e).card < y.card := calc
    (x.erase e).card < x.card : card_lt_card $ erase_ssubset hex
    --  since by Lemma 1.2.1 (bases_of_indep_card_eq) `x.card = y.card`
    ... = y.card : bases_of_indep_card_eq hxB hyB,
  -- therefore by (I3), there is an element `a` of `y \ (x.erase e)`
  -- such that `insert a (x.erase e)` is independent
  rcases (m.indep_exch hxr hyB.1 hcard) with ⟨a, ha⟩,
  clear hxr hcard hyB,
  have ha1 := mem_sdiff.mp ha.1,
  -- since `a ≠ e` and `a ∉ x`
  have hae : a ≠ e := λ hae, hey $ hae ▸ ha1.1,
  have hax : a ∉ x := by { simp only [not_and, mem_erase, ne.def] at ha1, exact ha1.2 hae },
  have hcx : x.card > 0 := card_pos.mpr (nonempty_of_mem hex),
  -- `insert a (x.erase e)` is the same size as `x`
  have hayycard : (insert a $ x.erase e).card = x.card := calc
    (insert a $ x.erase e).card = x.card.pred + 1 : by rw [card_insert_of_not_mem ha1.2,
        card_erase_of_mem hex]
    ... = x.card : nat.succ_pred_eq_of_pos hcx,
  -- hence `insert a (x.erase e)` is a basis
  use a, simp only [ha1.1, hax, true_and, not_false_iff, ha.2, subset_univ, is_basis],
  intros y' hayy,
  refine dep_of_card_gt_card_basis hxB _,
  exact hayycard ▸ (card_lt_card hayy),
end

/-- `m.to_bases` is the basis matroid corresponding to the independent set matroid `m` -/
def to_bases (m : of_indep E) : of_bases E :=
{ bases := bases m,
  bases_not_empty := B1 m,
  basis_exch := B2 m }

end of_indep

namespace of_bases
open of_indep
variable {E}

/-- Lemma 1.2.4. The bases of a basis matroid  are equicardinal. -/
theorem bases_card_eq {x y : finset E} {b : of_bases E} (hx : x ∈ b.bases) (hy : y ∈ b.bases) :
  x.card = y.card :=
begin
  -- suppose `x` and `y` are distinct bases with `y.card < x.card`
  by_contra heq,
  wlog h : y.card < x.card using [x y, y x],
  { exact lt_or_gt_of_ne (ne.symm heq), }, clear heq,
  -- let `F` be the set of all such pairs
  let F : finset (finset E × finset E) := (b.bases.product b.bases).filter
    (λ e : finset E × finset E, card e.1 < card e.2),
  -- `F` is nonempty
  have hyx : (y, x) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, h⟩, clear hy hx,
  -- so we may select a pair `a` = `(a.1, a.2)` such that `(a.2 \ a.1).card` is minimal
  rcases (min_fun_of_nonempty (λ f : finset E × finset E, (f.2 \ f.1).card) $
      nonempty_of_mem hyx) with ⟨a, haF, Ha⟩,
  clear hyx,
  replace haF := mem_filter.mp haF,
  have hab : a.1 ∈ b.bases ∧ a.2 ∈ b.bases := mem_product.mp haF.1,
  -- clearly `a.2 \ a.1` is nonempty, so choose `e` in `a.2 \ a.1`
  rcases (nonempty_sdiff_of_card_lt haF.2) with ⟨e, he⟩,
  -- we can find an element `aa` of `a.1 \ a.2` so that `insert aa (a.2.erase e)` is a basis
  rcases (b.basis_exch hab.2 hab.1 he) with ⟨aa, haa1, haa2⟩,
  rw mem_sdiff at haa1,
  -- from now on we call `insert aa (a.2.erase e)` `a2`
  let a2 : finset E := insert aa (a.2.erase e),
  have haani : aa ∉ a.2.erase e := λ h, haa1.2 (mem_erase.mp h).2,
  have hea2 : e ∈ a.2 := (mem_sdiff.mp he).1,
  have hpos : 0 < a.2.card := card_pos.mpr (nonempty_of_mem hea2),
  -- evidently `a2.card > a.1.card`
  have hcarda2 : a.1.card < a2.card := by { rw [card_insert_of_not_mem haani,
    card_erase_of_mem hea2, ←nat.succ_eq_add_one, nat.succ_pred_eq_of_pos hpos],
    exact haF.2 }, clear haani hpos haF,
  have : e ∉ a2 := by { intro hh,
    rcases mem_insert.mp hh with rfl | hh,
    { exact haa1.2 hea2, },
    { rw mem_erase at hh, exact hh.1 rfl, }, }, clear hea2,
  -- and `(a2 \ a.1).card < (a.2 \ a.1).card`
  have hcard : (a2 \ a.1).card < (a.2 \ a.1).card :=
    suffices a2 \ a.1 ⊂ a.2 \ a.1, from card_lt_card this,
    by { rw ssubset_iff,
      use e,
      split,
      { intro h0, exact this (mem_sdiff.mp h0).1, },
      { rw subset_iff,
        intros A hA, rw mem_insert at hA,
        rcases hA with rfl | hA,
        { exact he, },
        { rw [mem_sdiff, mem_insert] at hA,
        refine mem_sdiff.mpr ⟨_, hA.2⟩,
        rcases hA.1 with rfl | hA,
        { simp only [true_and, true_or, mem_erase, eq_self_iff_true A] at hA,
          exfalso, exact hA haa1.1, },
        { exact (mem_erase.mp hA).2, }, }, }, }, clear he haa1 this,
  -- thus the choice of `a.1` and `a.2` is contradicted
  have ha2F : (a.1, a2) ∈ F := mem_filter.mpr ⟨mem_product.mpr ⟨hab.1, haa2⟩, hcarda2⟩,
  -- and the lemma is proved
  exact not_le_of_lt hcard (Ha (a.1, a2) ha2F)
end

/-- `b.indep` for `b` a basis matroid (type `of_bases E`) is the set of
all independent sets of `E`, i.e. all sets contained in elements of `b.bases` -/
def indep (b : of_bases E) : finset (finset E) :=
univ.powerset.filter (λ x, ∃ a ∈ b.bases, x ⊆ a)

/-- Part I3 of Lemma 1.2.3. Let `E` be a set and `b` be a basis matroid on `E`. Let
`b.indep` be the collection of subsets of `E` contained in some member of `b.bases`.
Then `b.indep` satisfies axiom I3. (For any two elements of `b.indep`, `x`, `y` with
`x.card < y.card`, there exists an element `e ∈ y \ x` such that
`insert e x ∈ b.indep`.) -/
private lemma I3 (b : of_bases E) (x y : finset E) (hx : x ∈ b.indep)
  (hy : y ∈ b.indep) (hcard : x.card < y.card)
  : ∃ e, e ∈ y \ x ∧ insert e x ∈ b.indep :=
begin
  unfold indep at hx hy ⊢,
  let F := b.bases.filter (λ S, S ⊆ y),
  -- suppose that I3 fails for `b.indep`, then
  by_contra h,
  -- `x` and `y` are elements of `b.indep` with `x.card < y.card` such that
  -- for all `e ∈ y \ x`, the set `insert e x ∉ b.indep`
  simp only [mem_powerset, not_exists, and_imp, filter_congr_decidable,
    exists_prop, mem_filter, not_and, mem_sdiff] at hx hy h,
  -- by definition, `b.bases` contain members `b1` and `b2` such that `x ⊆ b1` and `y ⊆ b2`
  rcases hx.2 with ⟨b1, ⟨hb1bases, hxb1⟩⟩, clear hx,
  rcases hy.2 with ⟨b2, hb2⟩, clear hy,
  -- assume that such a set `B2` is chosen so that `B2 \ (y ∪ b1)` is minimal
  have := (min_fun_of_nonempty (λ f, (f \ (y ∪ b1)).card) $
    nonempty_of_mem $ mem_filter.mpr hb2), clear hb2 b2,
  rcases this with ⟨B2, ⟨hB2filt, hB2min⟩⟩,
  replace hB2filt : B2 ∈ b.bases ∧ y ⊆ B2 := mem_filter.mp hB2filt,
  -- by the choice of `x` and `y`, `y \ b1 = y \ x` (1)
  have hysdiff : y \ b1 = y \ x := by { simp only [ext, mem_sdiff],
    intro gg,
    split,
    { rintros ⟨hggy, hggnb1⟩, split, { exact hggy, },
      { intro hggnx, exact hggnb1 (mem_of_subset hxb1 hggnx), }, },
    { rintros ⟨hggy, hggnx⟩, split, { exact hggy, },
      { intro hggnb1,
        have : ¬insert gg x ⊆ b1 := h gg hggy hggnx (subset_univ _) b1 hb1bases,
        exact this (insert_subset.mpr ⟨hggnb1, hxb1⟩), }, }, },
  have hB2yub1: B2 \ (y ∪ b1) = ∅ := by {
    -- now suppose `B2 \ (y ∪ b1)` is nonempty
    by_contra H,
    -- then we can choose an element `X` from this set
    rcases (nonempty_of_ne_empty H) with ⟨X, hX⟩, clear H,
    simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
    have hXB2b1 : X ∈ B2 \ b1 := by { rw mem_sdiff, exact ⟨hX.1, hX.2.2⟩ },
    -- by (B2) there is an element `Y` of `b1 \ B2` such that `insert Y (B2.erase X) ∈ b.bases`
    rcases (b.basis_exch hB2filt.1 hb1bases hXB2b1) with ⟨Y, ⟨hYb1B2, hYbases⟩⟩,
    rw mem_sdiff at hYb1B2 hXB2b1,
    -- but then `(insert Y (B2.erase X) \ (y ∪ b1)).card < (B2 \ (y ∪ b1)).card`,
    -- and the choice of B2 is contradicted
    have hssubY : insert Y (B2.erase X) \ (y ∪ b1) ⊂ B2 \ (y ∪ b1) :=
      by { rw [ssubset_iff],
      use X,
      simp only [subset_iff, not_or_distrib, mem_union, mem_insert, not_and, mem_sdiff,
        not_not, mem_erase, not_true, or_false, ne.def, false_and, or_false,
        eq_self_iff_true],
      split,
      { rintro rfl hXy, exact hYb1B2.1, },
      { rintro gg (rfl | ⟨rfl | ⟨hggnX, hggB2⟩, hggny, hggnb1⟩),
        { exact hX, },
        { exact (hggnb1 hYb1B2.1).elim, },
        { exact ⟨hggB2, hggny, hggnb1⟩, }, }, },
    replace hssubY := card_lt_card hssubY,
    have hysubY : y ⊆ insert Y (B2.erase X) := by {
      simp only [subset_iff, mem_insert, mem_erase, ne.def],
      exact λ gg hgg, or.inr ⟨λ ggx, hX.2.1 $ ggx ▸ hgg, mem_of_subset hB2filt.2 hgg⟩, },
    -- hence `B2 \ (y ∪ b1)` is empty
    exact not_lt_of_le (hB2min (insert Y $ B2.erase X) $ mem_filter.mpr
        ⟨hYbases, hysubY⟩) hssubY }, clear hB2min,
  rw [←subset_iff_sdiff_eq_empty, subset_iff] at hB2yub1, simp only [mem_union] at hB2yub1,
  -- and so `B2 \ b1 = y \ b1`
  have hB2b1y : B2 \ b1 = y \ b1 := by { simp only [ext, mem_sdiff],
    exact λ gg, ⟨λ hgg, ⟨(hB2yub1 hgg.1).elim id $ λ hb1, (hgg.2 hb1).elim, hgg.2⟩,
        λ hgg, ⟨mem_of_subset hB2filt.2 hgg.1, hgg.2⟩⟩ }, clear hB2yub1,
  -- Thus, by (1), `B2 \ b1 = y \ x`. (2)
  rw [hysdiff] at hB2b1y, clear hysdiff,
  -- Next we show that `b1 \ (x ∪ B2)` is empty.
  have hb1xuB2 : b1 \ (x ∪ B2) = ∅ := by {
    -- if not,
    by_contra H,
    -- then there is an element `X` in this set
    rcases (nonempty_of_ne_empty H) with ⟨X, hX⟩,
    simp only [not_or_distrib, mem_union, mem_sdiff] at hX,
    -- and an element `Y` in `B2 \ b1` so that `insert Y (b1.erase X) ∈ b.bases`.
    rcases (b.basis_exch hb1bases hB2filt.1 $ mem_sdiff.mpr ⟨hX.1, hX.2.2⟩) with ⟨Y, hY⟩,
    -- since `Y ∈ B2 \ b1`,
    rw mem_sdiff at hY,
    -- it follows by (2) that `Y ∈ y \ x`
    have hYyx : Y ∈ y ∧ Y ∉ x := mem_sdiff.mp (hB2b1y ▸ (mem_sdiff.mpr hY.1)),
    -- now `insert Y x ⊆ insert Y (b1.erase X)`,
    have hxYsub : insert Y x ⊆ insert Y (b1.erase X) := by {
      simp only [subset_iff, mem_insert, mem_erase, ne.def],
      exact λ gg hgg, or.elim hgg (λ ggY, or.inl ggY) $ λ ggx, or.inr ⟨λ ggX, hX.2.1 $
        ggX ▸ ggx, mem_of_subset hxb1 ggx⟩ },
    -- so `insert Y x ∈ b.indep`
    -- and so we have a contradiction to our assumption that (I3) fails
    -- we conclude that `b1 \ (x ∪ B2)` is empty
    exact h Y hYyx.1 hYyx.2 (subset_univ _) (insert Y $ b1.erase X) hY.2 hxYsub, },
  clear h,
  rw [←subset_iff_sdiff_eq_empty, subset_iff] at hb1xuB2, simp only [mem_union] at hb1xuB2,
  -- Hence `b1 \ B2 = x \ B2`.
  have hb1B2 : b1 \ B2 = x \ B2 := by { simp only [ext, mem_sdiff],
    exact λ gg, ⟨λ hgg, ⟨(hb1xuB2 hgg.1).elim id $ λ ggB2, (hgg.2 ggB2).elim, hgg.2⟩,
        λ hgg, ⟨mem_of_subset hxb1 hgg.1, hgg.2⟩⟩, }, clear hb1xuB2,
  -- Since the last set is contained in `x \ y` it follows that
  -- `b1 \ B2 ⊆ x \ y` (3)
  replace hb1B2 : b1 \ B2 ⊆ x \ y := hb1B2.symm ▸ (sdiff_subset_sdiff (subset.refl x)
      hB2filt.2),
  -- By Lemma 1.2.4, `b1.card = B2.card`,
  have hcardeq : b1.card = B2.card := bases_card_eq hb1bases hB2filt.1,
  -- so `(b1 \ B2).card = (B2 \ b1).card`.
  have hcardb1B2 : (b1 \ B2).card = (B2 \ b1).card := calc
    (b1 \ B2).card = b1.card - (b1 ∩ B2).card : card_sdiff_eq b1 B2
    ... = B2.card - (B2 ∩ b1).card : by rw [hcardeq, inter_comm]
    ... = (B2 \ b1).card : by rw ←card_sdiff_eq B2 b1,
  -- Therefore, by (2) and (3), `(y \ x).ccard ≤ (x \ y).card`,
  have hcardcontra0 : (y \ x).card ≤ (x \ y).card := calc
    (y \ x).card = (B2 \ b1).card : by rw hB2b1y
    ... = (b1 \ B2).card : by rw hcardb1B2
    ... ≤ (x \ y).card : card_le_of_subset hb1B2,
  rw [card_sdiff_eq y x, card_sdiff_eq x y, inter_comm] at hcardcontra0,
  -- so `y.card ≤ x.card`
  have hcardcontra : y.card ≤ x.card := nat.le_of_le_of_sub_le_sub_right
      (card_le_of_subset $ inter_subset_left x y) hcardcontra0,
  -- This contradiction completes the proof of (I3)
  exact not_lt_of_le hcardcontra hcard,
end

/-- first part of Theorem 1.2.3; Let `E` be a set and `b` be a basis matroid on `E`. Let
`b.indep` be the collection of subsets of `E` contained in some member of `b.bases`.
Then `b.to_indep` is an independent set matroid with type `of_indep E` -/
def to_indep (b : of_bases E) : of_indep E :=
{ indep := b.indep,
  empty_mem_indep := begin
      refine mem_filter.mpr ⟨empty_mem_powerset univ, _⟩,
      convert b.bases_not_empty,
      simp only [exists_prop, finset.empty_subset, and_true],
    end,
  indep_of_subset_indep := begin
      intros x y hx hxy,
      simp only [indep, mem_powerset, filter_congr_decidable,
        exists_prop, mem_filter] at hx ⊢,
      split, { exact subset.trans hxy hx.1, },
      { rcases hx.2 with ⟨a, ha1, ha2⟩, use [a, ha1], exact subset.trans hxy ha2, },
    end,
  indep_exch := I3 b, }

-- instance base_indep : has_coe (bases E) (indep E) := ⟨indep_of_bases⟩
-- instance indep_base : has_coe (indep E) (bases E) := ⟨bases_of_indep⟩

/-- second part of Theorem 1.2.3, Let `E` be a set and `b` be a basis matroid on `E`. Let
`b.indep` be the collection of subsets of `E` contained in some member of `b.bases`.
Then `b.to_indep` has `b.bases` as its set of bases -/
theorem bases_indep_bases (B : of_bases E) : B.to_indep.to_bases = B :=
suffices B.to_indep.to_bases.bases = B.bases, from eq_of_base_eq this,
begin
  simp only [to_indep, to_bases, of_bases.indep, is_basis,
  ext, of_indep.bases, mem_filter, mem_powerset, not_and, not_exists, exists_prop],
  intro b, split,
  { rintro ⟨_, ⟨⟨_, hbexists⟩, hb⟩⟩, rcases hbexists with ⟨a, ⟨habases, hba⟩⟩,
    have : a ⊆ univ := subset_univ a,
    by_cases h : a = b,
    { exact h ▸ habases, },
    { have hba' : b ⊂ a := lt_iff_ssubset.mp (lt_of_le_of_ne (le_iff_subset.mpr hba) $ ne.symm h),
      exact (hb a hba' this a habases $ subset.refl a).elim, }, },
  { intro hb,
    have hB : b ⊆ univ := subset_univ b,
    split,
    { exact hB, },
    { split, { split, { exact hB, }, { use b, exact ⟨hb, subset.refl b⟩, }, },
      { intros b' hbb' _ _ hx H,
        exact (ne_of_lt $ lt_of_lt_of_le (card_lt_card hbb') $ card_le_of_subset H)
          (bases_card_eq hb hx), }, }, },
end

end of_bases

namespace of_indep
open of_bases
variable {E}

/-- Let `M` be an independent set matroid and let `B` be `M.to_bases`,
its corresponding basis matroid. Then `B.to_indep`, its independent set matroid
is equal to `M`. -/
theorem indep_bases_indep (M : of_indep E) : M.to_bases.to_indep = M :=
suffices M.to_bases.to_indep.indep = M.indep, from eq_of_indep_eq this,
begin
  simp only [to_indep, to_bases, of_bases.indep, is_basis,
  ext, of_indep.bases, mem_filter, mem_powerset, exists_prop],
  intro I, split,
  { rintro ⟨hIuniv, hIexists⟩, rcases hIexists with ⟨B, ⟨⟨hBuniv, ⟨hBindep, hB'⟩⟩, hIB⟩⟩,
    exact M.indep_of_subset_indep hBindep hIB, },
  { intro hI, split,
    { exact subset_univ I, },
    { rcases (exists_basis_containing_indep hI) with ⟨B, hB⟩,
      unfold is_basis at hB,
      use B, exact ⟨⟨subset_univ B, hB.2⟩, hB.1⟩, }, },
end

/-- the independent set matroids and basis matroids on a ground set `E` are
equivalent (there are mutually inverse functions between them) -/
def indep_equiv_bases : of_indep E ≃ of_bases E :=
{ to_fun := to_bases,
  inv_fun := to_indep,
  left_inv := indep_bases_indep,
  right_inv := bases_indep_bases, }

/-- Corollary 1.2.6. Let `B` be a basis of a matroid `m`. If
`e ∈ (univ : finset E) \ B`, then `insert e B` contains a unique circuit `C`.
Moreover, `e ∈ C`. We call this the fundamental circuit of `e` with respect
to `B`. -/
theorem existsu_fund_circ_of_basis {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : ∃ C, C ∈ m.circuits ∧ C ⊆ insert e B ∧
  ∀ C' ∈ m.circuits, C' ⊆ insert e B → C' = C :=
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
/-- The fundamental circuit of a basis (see `existsu_fund_circ_of_basis`)
can be computed for an encodable ground set. -/
def fund_circ_of_basis {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : finset E :=
encodable.choose (existsu_fund_circ_of_basis hB he)

lemma fund_circ_of_basis_spec {m : of_indep E} {B : finset E} (hB : is_basis B m) {e : E}
  (he : e ∈ univ \ B) : fund_circ_of_basis hB he ∈ m.circuits ∧
  fund_circ_of_basis hB he  ⊆ insert e B ∧ ∀ C' ∈ m.circuits, C' ⊆ insert e B →
  C' = fund_circ_of_basis hB he :=
encodable.choose_spec (existsu_fund_circ_of_basis hB he)

end encodable

end of_indep

/-! § 1.3. Rank. -/
namespace of_indep

variable {E}

/-- def by Mario Carneiro https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/subject/finset.20of.20subtype.20from.20filter/near/134578668 -/
def indep_of_restriction (m : of_indep E) (X : finset E) : finset (finset {x : E // x ∈ X}) :=
m.indep.filter_map $ prestrict X
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
    use e', exact ⟨heyx, H⟩,
  end, }

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
  ∃ B, B ∈ (m ¦ X).bases :=
nonempty_of_ne_empty $ B1 (m ¦ X)

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
