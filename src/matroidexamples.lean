/-
Examples of matroids.
-/
import matroid data.equiv.list

open finset

variables (k : ℕ) {α : Type*} [decidable_eq α] [fintype α]
namespace matroid

variable (α)

/-- the loopy matroid on `E : finset α` is the matroid where every
element of `E` is a loop; equivalently, every subset of `E` is
dependent -/
def loopy : indep α :=
⟨{∅},
mem_singleton_self _,
λ x y h1 h2, mem_singleton.mpr $ subset_empty.mp $ (mem_singleton.mp h1) ▸ h2,
λ x y hx hy hcard, false.elim $ (nat.not_lt_zero $ card x) $
  card_empty.subst $ (mem_singleton.mp hy).subst hcard⟩

/-- the free matroid is the matroid where every subset
of the ground set is independent; sometimes called the trivial matroid -/
def free : indep α :=
⟨powerset univ,
empty_mem_powerset _,
λ x y h1 h2, mem_powerset.mpr $ subset.trans h2 $ mem_powerset.mp h1,
λ x y hx hy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
  λ e exy, ⟨e, exy, mem_powerset.mpr $ insert_subset.mpr
    ⟨mem_of_subset (mem_powerset.mp hy) (mem_sdiff.mp exy).1, mem_powerset.mp hx⟩⟩⟩

/-- the uniform matroid U_k on `E : finset α` is the matroid whose
independent sets are all subsets of `E` of size `k` or less; Example 1.2.7 in Oxley -/
def uniform : indep α :=
⟨(powerset univ).filter (λ x, card x ≤ k),
mem_filter.mpr ⟨empty_mem_powerset univ, (@card_empty $ finset α).symm ▸ nat.zero_le k⟩,
by simp; exact λ x y hx hcardx hy, ⟨subset.trans hy hx, le_trans (card_le_of_subset hy) hcardx⟩,
by simp; exact λ x y hx hcardx hy hcardy hcard, exists.elim (exists_sdiff_of_card_lt hcard) $
  λ e exy, ⟨e, ⟨mem_sdiff.mp exy, ⟨insert_subset.mpr ⟨mem_of_subset hy (mem_sdiff.mp exy).1, hx⟩,
    (card_insert_of_not_mem (mem_sdiff.mp exy).2).symm ▸
      nat.succ_le_of_lt $ nat.lt_of_lt_of_le hcard hcardy⟩⟩⟩⟩

theorem loopy_eq_uniform_zero : loopy α = uniform 0 α :=
suffices (loopy α).indep = (uniform 0 α).indep, from eq_of_indep_eq this,
by { simp [loopy, uniform, ext], intro a, rw ←eq_empty_iff_forall_not_mem,
  exact ⟨λ ha, ⟨ha.symm ▸ empty_subset univ, ha⟩, λ ha, ha.2⟩ }

theorem free_eq_uniform_card : free α = uniform (card $ @univ α _) α :=
suffices (free α).indep = (uniform (card univ) α).indep, from eq_of_indep_eq this,
  by simp [free, uniform, ext]; exact λ a, ⟨λ ha, ⟨ha, card_le_of_subset ha⟩, λ ha, ha.1⟩

#eval uniform 2 $ fin 4

#eval (is_basis {1,3} $ uniform 2 $ fin 4 : bool)
#eval (is_basis {1,0,3} $ uniform 2 $ fin 4 : bool)

#eval bases_of_indep $ loopy $ fin 5
#eval bases_of_indep $ uniform 3 $ fin 5
#eval bases_of_indep $ free $ fin 5

#eval (is_circuit {1,2} $ uniform 2 $ fin 4 : bool)
#eval (is_circuit {1,2,4} $ uniform 2 $ fin 4 : bool)
#eval (is_circuit {1,2,3,4} $ uniform 2 $ fin 4 : bool)

#eval circuits_of_indep $ loopy $ fin 5
#eval circuits_of_indep $ uniform 3 $ fin 5
#eval circuits_of_indep $ free $ fin 5

#eval uniform 3 $ fin 5
#eval indep_of_bases $ bases_of_indep $ uniform 3 $ fin 5
#eval indep_of_circuits $ circuits_of_indep $ uniform 3 $ fin 5

/- /- slow -/
#eval circuit_of_dep_of_insert_indep (dec_trivial : {0,2,3} ∈ (uniform 3 $ fin 4).indep)
    (dec_trivial : insert 1 {0,2,3} ∉ (uniform 3 $ fin 4).indep )
#eval fund_circ_of_basis (dec_trivial : is_basis {0,1,2} (uniform 3 $ fin 4))
    (dec_trivial : 3 ∈ (@univ (fin 4) _) \ {0,1,2}) -/
#eval fund_circ_of_basis (dec_trivial : is_basis ∅ (loopy $ fin 4))
    (dec_trivial : 3 ∈ (@univ (fin 4) _) \ ∅)

#eval basis_containing_indep (dec_trivial : {0,2} ∈ (uniform 3 $ fin 5).indep)

/- still broken below -/
#eval basis_of_subset (dec_trivial : {0,4,1,2,3} ⊆ (@univ (fin 5) _)) (uniform 3 $ fin 5)

#eval rank_of_subset (dec_trivial : {0,4,1} ⊆ fin 5) (uniform 3 $ fin 5)
#eval rank_of_subset (dec_trivial : {0,4,2,1} ⊆ fin 5) (uniform 3 $ fin 5)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ fin 5) (loopy $ fin 5)
#eval rank_of_subset (dec_trivial : {0,4} ⊆ fin 5) (free $ fin 5)

end matroid