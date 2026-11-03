import Mathlib

namespace Erdos571_hypergraph

open Polynomial

/-- The linear polynomial `∑ i, ℓ(e_i) * X_i` representing a linear
functional `ℓ` as a multivariate polynomial. -/
noncomputable def linearMvPolynomial {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) : MvPolynomial (Fin n) F :=
  ∑ i, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i

/-- Composition of a univariate polynomial `h` with a linear functional `ℓ`. -/
noncomputable def compLinear {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (h : Polynomial F) : MvPolynomial (Fin n) F :=
  Polynomial.aeval (linearMvPolynomial ℓ) h

lemma eval_linearMvPolynomial {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (z : Fin n → F) :
    MvPolynomial.eval z (linearMvPolynomial ℓ) = ℓ z := by
  have h1 : MvPolynomial.eval z (linearMvPolynomial ℓ)
      = ∑ i, ℓ (Pi.single i (1 : F)) * z i := by
    simp [linearMvPolynomial]
  rw [h1]
  have hz : z = ∑ i, z i • (Pi.single i (1 : F) : Fin n → F) := by
    funext j
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, Pi.single, smul_eq_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Function.update, Ne.symm hb]
    · intro hj
      simp at hj
  calc
    ∑ i, ℓ (Pi.single i (1 : F)) * z i
        = ∑ i, z i * ℓ (Pi.single i (1 : F)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i, ℓ (z i • (Pi.single i (1 : F) : Fin n → F)) := by
          simp [map_smul, smul_eq_mul]
    _ = ℓ (∑ i, z i • (Pi.single i (1 : F) : Fin n → F)) := by
          rw [map_sum]
    _ = ℓ z := by
          conv_rhs => rw [hz]

lemma eval_compLinear {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (z : Fin n → F) (h : Polynomial F) :
    MvPolynomial.eval z (compLinear ℓ h) = Polynomial.eval (ℓ z) h := by
  induction h using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsum : compLinear ℓ (p + q) = compLinear ℓ p + compLinear ℓ q := by
        simp [compLinear, map_add]
      rw [hsum, map_add, hp, hq, Polynomial.eval_add]
  | monomial n a =>
      simp [compLinear, Polynomial.aeval_monomial, map_mul, map_pow,
        eval_linearMvPolynomial]

lemma totalDegree_C_mul_X_le {F : Type} [Field F] {n : ℕ}
    (a : F) (i : Fin n) :
    (MvPolynomial.C a * MvPolynomial.X i).totalDegree ≤ 1 := by
  calc
    (MvPolynomial.C a * MvPolynomial.X i).totalDegree
        ≤ (MvPolynomial.C a).totalDegree + (MvPolynomial.X i).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = 0 + 1 := by
          rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
    _ = 1 := by norm_num

lemma totalDegree_linearMvPolynomial_le {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) :
    (linearMvPolynomial ℓ).totalDegree ≤ 1 := by
  rw [linearMvPolynomial]
  calc
    (∑ i, MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i).totalDegree
        ≤ (Finset.univ : Finset (Fin n)).sup (fun i =>
            (MvPolynomial.C (ℓ (Pi.single i 1)) * MvPolynomial.X i).totalDegree) :=
          MvPolynomial.totalDegree_finsetSum _ _
    _ ≤ 1 := by
          apply Finset.sup_le
          intro i _
          exact totalDegree_C_mul_X_le _ _

lemma totalDegree_aeval_monomial_le {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (m : ℕ) (a : F) :
    (Polynomial.aeval (linearMvPolynomial ℓ) (Polynomial.monomial m a)).totalDegree ≤ m := by
  rw [Polynomial.aeval_monomial]
  change (algebraMap F (MvPolynomial (Fin n) F) a *
      (linearMvPolynomial ℓ) ^ m).totalDegree ≤ m
  rw [show algebraMap F (MvPolynomial (Fin n) F) a =
      (MvPolynomial.C a : MvPolynomial (Fin n) F) from rfl]
  have hx : (linearMvPolynomial ℓ).totalDegree ≤ 1 :=
    totalDegree_linearMvPolynomial_le ℓ
  calc
    ((MvPolynomial.C a : MvPolynomial (Fin n) F) *
        (linearMvPolynomial ℓ) ^ m).totalDegree
        ≤ (MvPolynomial.C a : MvPolynomial (Fin n) F).totalDegree +
            ((linearMvPolynomial ℓ) ^ m).totalDegree := by
          exact MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + m * (linearMvPolynomial ℓ).totalDegree := by
          gcongr
          · simp
          · exact MvPolynomial.totalDegree_pow _ _
    _ ≤ 0 + m * 1 := by gcongr
    _ = m := by omega

lemma totalDegree_compLinear_le {F : Type} [Field F] {n : ℕ}
    (ℓ : (Fin n → F) →ₗ[F] F) (h : Polynomial F) :
    (compLinear ℓ h).totalDegree ≤ h.natDegree := by
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq h]
  rw [compLinear, Polynomial.sum_def, map_sum]
  calc
    (∑ n ∈ h.support,
        Polynomial.aeval (linearMvPolynomial ℓ) (Polynomial.C (h.coeff n) * Polynomial.X ^ n)).totalDegree
        ≤ h.support.sup (fun n =>
            (Polynomial.aeval (linearMvPolynomial ℓ)
              (Polynomial.C (h.coeff n) * Polynomial.X ^ n)).totalDegree) :=
          MvPolynomial.totalDegree_finsetSum _ _
    _ ≤ h.support.sup (fun n => n) := by
          apply Finset.sup_le
          intro n hn
          have hmono : Polynomial.C (h.coeff n) * Polynomial.X ^ n =
              Polynomial.monomial n (h.coeff n) :=
            Polynomial.C_mul_X_pow_eq_monomial
          rw [hmono]
          calc
            (Polynomial.aeval (linearMvPolynomial ℓ)
                (Polynomial.monomial n (h.coeff n))).totalDegree ≤ n :=
              totalDegree_aeval_monomial_le ℓ n (h.coeff n)
            _ ≤ h.support.sup (fun n => n) :=
              Finset.le_sup (s := h.support) (f := fun n => n) hn
    _ ≤ h.natDegree := by
          apply Finset.sup_le
          intro n hn
          exact Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)

end Erdos571_hypergraph
