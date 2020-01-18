/-
Examples of matroids.
-/
import matroid data.equiv.list

open finset

variables (k : ℕ) (E : Type*) [decidable_eq E] [fintype E]
namespace matroid
open of_indep of_circuits of_bases

/-- the loopy matroid on `E : finset α` is the matroid where every
element of `E` is a loop; equivalently, every subset of `E` is
dependent -/
def loopy : of_indep E :=
{ indep := {∅},
  empty_mem_indep := mem_singleton_self _,
  indep_of_subset_indep := λ x y h1 h2, mem_singleton.mpr $ subset_empty.mp $
    (mem_singleton.mp h1) ▸ h2,
  indep_exch := λ x y hx hy hcard, false.elim $ (nat.not_lt_zero $ card x) $
  card_empty.subst $ (mem_singleton.mp hy).subst hcard }

/-- the free matroid is the matroid where every subset
of the ground set is independent; sometimes called the trivial matroid -/
def free : of_indep E :=
{ indep := powerset univ,
  empty_mem_indep := empty_mem_powerset _,
  indep_of_subset_indep := λ x y h1 h2, mem_powerset.mpr $ subset.trans h2 $ mem_powerset.mp h1,
  indep_exch := λ x y hx hy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
    λ e exy, ⟨e, exy, mem_powerset.mpr $ insert_subset.mpr
      ⟨mem_of_subset (mem_powerset.mp hy) (mem_sdiff.mp exy).1, mem_powerset.mp hx⟩⟩ }

/-- the uniform matroid U_k on `E : finset α` is the matroid whose
independent sets are all subsets of `E` of size `k` or less; Example 1.2.7 in Oxley -/
def uniform (k : ℕ) : of_indep E :=
{ indep := (powerset univ).filter (λ x, card x ≤ k),
  empty_mem_indep := mem_filter.mpr ⟨empty_mem_powerset univ,
    (@card_empty $ finset E).symm ▸ nat.zero_le k⟩,
  indep_of_subset_indep := begin
    simp only [mem_powerset, and_imp, mem_filter],
    exact λ x y hx hcardx hy, ⟨subset.trans hy hx, le_trans (card_le_of_subset hy) hcardx⟩
  end,
  indep_exch := begin
    simp only [mem_powerset, and_imp, mem_filter, mem_sdiff],
    exact λ x y hx hcardx hy hcardy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
    λ e exy, ⟨e, ⟨mem_sdiff.mp exy, ⟨insert_subset.mpr ⟨mem_of_subset hy (mem_sdiff.mp exy).1, hx⟩,
      (card_insert_of_not_mem (mem_sdiff.mp exy).2).symm ▸
        nat.succ_le_of_lt $ nat.lt_of_lt_of_le hcard hcardy⟩⟩⟩
  end }

theorem loopy_eq_uniform_zero : loopy E = uniform E 0 :=
suffices (loopy E).indep = (uniform E 0).indep, from eq_of_indep_eq this,
by { simp only [loopy, uniform, ext, mem_powerset, mem_filter, card_eq_zero, le_zero_iff_eq,
    iff_false, insert_empty_eq_singleton, mem_singleton, not_mem_empty],
  intro a, rw ←eq_empty_iff_forall_not_mem,
  exact ⟨λ ha, ⟨ha.symm ▸ empty_subset univ, ha⟩, λ ha, ha.2⟩ }

theorem free_eq_uniform_card : free E = uniform E (card (univ : finset E)) :=
suffices (free E).indep = (uniform E (card univ)).indep, from eq_of_indep_eq this,
  by { simp only [free, uniform, ext, mem_powerset, mem_filter, empty_mem_powerset],
    exact λ a, ⟨λ ha, ⟨ha, card_le_of_subset ha⟩, λ ha, ha.1⟩ }

#eval uniform (fin 4) 2

#eval ((uniform (fin 4) 2).is_basis {1,3} : bool)
#eval ((uniform (fin 4) 2).is_basis {1,0,3} : bool)

#eval (loopy $ fin 5).bases
#eval (uniform (fin 5) 3).bases
#eval (free $ fin 5).bases

#eval ((uniform (fin 4) 2).is_circuit {1,2}: bool)
#eval ((uniform (fin 4) 2).is_circuit {1,2,4} : bool)
#eval ((uniform (fin 4) 2).is_circuit {1,2,3,4} : bool)

#eval (loopy $ fin 5).circuits
#eval (uniform (fin 5) 3).circuits
#eval (free $ fin 5).circuits

#eval uniform (fin 5) 3
#eval (uniform (fin 5) 3).bases.indep
#eval (uniform (fin 5) 3).circuits.indep

/- /- slow -/
#eval circuit_of_dep_of_insert_indep (dec_trivial : {0,2,3} ∈ (uniform 3 $ range 5).indep)
    (dec_trivial : 1 ∈ range 5) (dec_trivial : _ /-insert 3 {1,2} ∉ (uniform 2 $ range 4).indep -/)
#eval fund_circ_of_basis (dec_trivial : is_basis {0,1,2} (uniform 3 $ range 5))
    (dec_trivial : 4 ∈ range 5 \ {0,1,2}) -/
#eval fund_circ_of_basis (dec_trivial : (loopy $ fin 5).is_basis ∅)
    (dec_trivial : 4 ∈ (univ : finset (fin 5)) \ ∅)

#eval basis_containing_indep (dec_trivial : {0,2} ∈ (uniform (fin 5) 3).indep)

#eval basis_of_subset (dec_trivial : {0,4,1,2,3} ⊆ (univ : finset (fin 5))) (uniform (fin 5) 3)

#eval rank_of_subset (dec_trivial : {0,4,1} ⊆ fin 5) (uniform (fin 5) 3)
#eval rank_of_subset (dec_trivial : {0,4,2,1} ⊆ fin 5) (uniform (fin 5) 3)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ fin 5) (loopy $ fin 5)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ fin 5) (free $ fin 5)

end matroid
