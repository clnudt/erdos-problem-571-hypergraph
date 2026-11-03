import Mathlib

namespace Erdos571_hypergraph

/-- Expansion of a vector in the standard basis. -/
lemma pi_eq_sum_single {F : Type} [Field F] {n : ℕ} (x : Fin n → F) :
    x = ∑ i, x i • (Pi.single i (1 : F) : Fin n → F) := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.single, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Function.update, Ne.symm hb]
  · intro hj
    simp at hj

/-- The standard-basis evaluation formula for a linear functional. -/
lemma sum_single_mul_eq {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (x : Fin n → F) :
    (∑ i, ℓ (Pi.single i (1 : F)) * x i) = ℓ x := by
  calc
    ∑ i, ℓ (Pi.single i (1 : F)) * x i
        = ∑ i, x i * ℓ (Pi.single i (1 : F)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i, ℓ (x i • (Pi.single i (1 : F) : Fin n → F)) := by
          simp [map_smul, smul_eq_mul]
    _ = ℓ (∑ i, x i • (Pi.single i (1 : F) : Fin n → F)) := by
          rw [map_sum]
    _ = ℓ x := by
          conv_rhs => rw [pi_eq_sum_single x]

/-- Coordinate projection. -/
def coord {F : Type} [Field F] {n : ℕ} (i : Fin n) :
    (Fin n → F) →ₗ[F] F :=
  LinearMap.proj (φ := fun _ : Fin n => F) i

/-- The dual space of `Fin n → F` is linearly equivalent to `Fin n → F`. -/
noncomputable def dualEquiv (F : Type) [Field F] (n : ℕ) :
    ((Fin n → F) →ₗ[F] F) ≃ₗ[F] (Fin n → F) where
  toFun ℓ := fun i => ℓ (Pi.single i (1 : F))
  invFun y := ∑ i, y i • coord (F := F) (n := n) i
  map_add' ℓ₁ ℓ₂ := by
    funext i
    simp
  map_smul' c ℓ := by
    funext i
    simp
  left_inv ℓ := by
    apply LinearMap.ext
    intro x
    dsimp only
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, coord, LinearMap.proj_apply, smul_eq_mul]
    exact sum_single_mul_eq ℓ x
  right_inv y := by
    funext i
    dsimp only
    rw [LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, coord, LinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Pi.single, Function.update, hb]
    · intro hi
      simp at hi

noncomputable instance dualFintype (F : Type) [Field F] [Fintype F] (n : ℕ) :
    Fintype ((Fin n → F) →ₗ[F] F) :=
  Fintype.ofEquiv (Fin n → F) (dualEquiv F n).symm.toEquiv

lemma card_dual (F : Type) [Field F] [Fintype F] (n : ℕ) :
    Fintype.card ((Fin n → F) →ₗ[F] F) = Fintype.card F ^ n := by
  rw [Fintype.card_congr (dualEquiv F n).toEquiv, Fintype.card_fun]
  simp

end Erdos571_hypergraph
