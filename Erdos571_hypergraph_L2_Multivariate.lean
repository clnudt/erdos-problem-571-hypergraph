import Erdos571_hypergraph_L2_Dual

namespace Erdos571_hypergraph

open Polynomial

/-- Evaluation of a linear functional at a fixed vector. -/
def evalAt {F : Type} [Field F] {n : ℕ} (v : Fin n → F) :
    ((Fin n → F) →ₗ[F] F) →ₗ[F] F where
  toFun ℓ := ℓ v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A single coordinate projection separates two distinct points. -/
lemma exists_linear_separates_pair
    {F : Type} [Field F] {n m : ℕ} {z : Fin m → (Fin n → F)}
    {i j : Fin m} (h : z i ≠ z j) :
    ∃ ℓ : (Fin n → F) →ₗ[F] F, ℓ (z i) ≠ ℓ (z j) := by
  have hex : ∃ k : Fin n, z i k ≠ z j k := by
    by_contra h'
    apply h
    funext k
    by_contra hk
    exact h' ⟨k, hk⟩
  rcases hex with ⟨k, hk⟩
  refine ⟨LinearMap.proj k, ?_⟩
  simpa using hk

/-- The bad set for the pair `(i,j)`: functionals that do not separate
`z i` and `z j`. -/
def badPair {F : Type} [Field F] {n m : ℕ}
    (z : Fin m → (Fin n → F)) (i j : Fin m) :
    Submodule F ((Fin n → F) →ₗ[F] F) :=
  (evalAt (z i) - evalAt (z j)).ker

lemma badPair_ne_top
    {F : Type} [Field F] {n m : ℕ} {z : Fin m → (Fin n → F)}
    {i j : Fin m} (h : z i ≠ z j) :
    badPair z i j ≠ ⊤ := by
  intro htop
  have hzero : evalAt (z i) - evalAt (z j) = 0 :=
    LinearMap.ker_eq_top.mp htop
  rcases exists_linear_separates_pair h with ⟨ℓ, hℓ⟩
  have hval : (evalAt (z i) - evalAt (z j)) ℓ = 0 := by
    rw [hzero]
    rfl
  simp [evalAt] at hval
  exact hℓ (sub_eq_zero.mp hval)

lemma card_pairs (m : ℕ) :
    ((Finset.univ : Finset (Fin m)).product Finset.univ |>.filter
      (fun p : Fin m × Fin m => p.1 < p.2)).card = m.choose 2 := by
  simpa using Finset.card_product_filter_lt
    (s := (Finset.univ : Finset (Fin m)))

lemma card_badPair_le
    {F : Type} [Field F] [Fintype F] {n m : ℕ}
    {z : Fin m → (Fin n → F)} {i j : Fin m}
    (h : z i ≠ z j) (_hn : 0 < n) :
    Nat.card (badPair z i j) ≤ Fintype.card F ^ (n - 1) := by
  classical
  haveI : Fintype ((Fin n → F) →ₗ[F] F) := dualFintype F n
  rw [Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := F) (V := badPair z i j)]
  have hlt : Module.finrank F (badPair z i j) < n := by
    simpa [Subspace.dual_finrank_eq] using Submodule.finrank_lt (badPair_ne_top h)
  have hle : Module.finrank F (badPair z i j) ≤ n - 1 :=
    Nat.le_sub_one_of_lt hlt
  exact Nat.pow_le_pow_right Fintype.card_pos hle

end Erdos571_hypergraph
