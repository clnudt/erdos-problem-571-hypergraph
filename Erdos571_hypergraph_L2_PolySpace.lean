import Mathlib

namespace Erdos571_hypergraph

/-- Exponent vectors of monomials of total degree at most `D`. -/
def MonomialIndex (n D : ℕ) :=
  {s : Fin n →₀ ℕ // s.sum (fun _ e => e) ≤ D}

/-- The monomial index type is finite: map it injectively into bounded
exponent vectors. -/
noncomputable instance monomialIndexFintype (n D : ℕ) :
    Fintype (MonomialIndex n D) :=
  Fintype.ofInjective
    (fun s : MonomialIndex n D => fun i : Fin n =>
      (⟨s.1 i, by
        have hle : s.1 i ≤ s.1.sum (fun _ e => e) := by
          simpa using Finsupp.single_le_sum (f := s.1)
            (g := fun _ e => e) (fun _ _ => Nat.zero_le _) i
        exact Nat.lt_succ_of_le (le_trans hle s.2)⟩ : Fin (D + 1)))
    (by
      intro s t h
      apply Subtype.ext
      apply Finsupp.ext
      intro i
      exact Fin.ext_iff.mp (congrFun h i))

/-- The finite coefficient space of polynomials of total degree at most `D`. -/
abbrev PolyCoeff (F : Type) (n D : ℕ) :=
  MonomialIndex n D → F

noncomputable instance polyCoeffFintype (F : Type) [Fintype F] (n D : ℕ) :
    Fintype (PolyCoeff F n D) := by
  classical
  infer_instance

/-- Evaluate a monomial at a point. -/
def monomialEval {F : Type} [CommSemiring F] {n : ℕ} {D : ℕ}
    (s : MonomialIndex n D) (z : Fin n → F) : F :=
  ∏ i, z i ^ s.1 i

/-- Evaluation of a coefficient vector at one point. -/
noncomputable def evalPolyAt {F : Type} [Field F] {n D : ℕ}
    (z : Fin n → F) (c : PolyCoeff F n D) : F :=
  ∑ s : MonomialIndex n D, c s * monomialEval s z

/-- Evaluation of a coefficient vector at `m` points, as an additive map. -/
noncomputable def evalPoly {F : Type} [Field F] {n m D : ℕ}
    (z : Fin m → (Fin n → F)) : PolyCoeff F n D →+ (Fin m → F) where
  toFun c i := evalPolyAt (z i) c
  map_zero' := by
    funext i
    simp [evalPolyAt]
  map_add' c d := by
    funext i
    simp [evalPolyAt, add_mul, Finset.sum_add_distrib]

/-- The coefficient vector of a bounded-degree multivariate polynomial
evaluates to the polynomial itself. -/
lemma evalPolyAt_coeff {F : Type} [Field F] {n D : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p.totalDegree ≤ D)
    (z : Fin n → F) :
    evalPolyAt (D := D) z (fun s => p.coeff s.1) = MvPolynomial.eval z p := by
  classical
  simp only [evalPolyAt, monomialEval]
  rw [MvPolynomial.eval_eq']
  let f : (Fin n →₀ ℕ) → F := fun d => p.coeff d * ∏ i, z i ^ d i
  have hsupp : p.support ⊆ Finset.univ.image (fun s : MonomialIndex n D => s.1) := by
    intro d hd
    have hdeg : d.sum (fun _ e => e) ≤ D := by
      exact le_trans (MvPolynomial.le_totalDegree hd) hp
    refine Finset.mem_image.mpr ⟨⟨d, ?_⟩, Finset.mem_univ _, rfl⟩
    simpa using hdeg
  have hsum1 : (∑ s : MonomialIndex n D, p.coeff s.1 * ∏ i, z i ^ s.1 i)
      = ∑ d ∈ Finset.univ.image (fun s : MonomialIndex n D => s.1), f d := by
    have hinj : Set.InjOn (fun s : MonomialIndex n D => s.1)
        (↑(Finset.univ : Finset (MonomialIndex n D))) := by
      intro a _ b _ h
      exact Subtype.ext h
    rw [← Finset.sum_image (s := Finset.univ)
      (g := fun s : MonomialIndex n D => s.1) (f := f) hinj]
  rw [hsum1]
  exact (Finset.sum_subset hsupp (by
    intro d _ hd
    have hzero : p.coeff d = 0 := by
      by_contra h
      exact hd (MvPolynomial.mem_support_iff.mpr h)
    simp [f, hzero])).symm

end Erdos571_hypergraph
