import Erdos571_hypergraph_L12_Constructible
import Erdos571_hypergraph_L3_Host

namespace Erdos571_hypergraph

/-- The `MvPolynomial` represented by a bounded-degree coefficient vector. -/
noncomputable def toMvPoly {F : Type} [Field F] {n D : ℕ}
    (c : PolyCoeff F n D) : MvPolynomial (Fin n) F :=
  ∑ s : MonomialIndex n D, MvPolynomial.monomial s.1 (c s)

lemma toMvPoly_totalDegree {F : Type} [Field F] {n D : ℕ}
    (c : PolyCoeff F n D) : (toMvPoly c).totalDegree ≤ D := by
  classical
  rw [toMvPoly]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  exact (MvPolynomial.totalDegree_monomial_le s.1 (c s)).trans s.2

lemma evalAtTuple_toMvPoly {F : Type} [Field F] {k b D : ℕ}
    (c : PolyCoeff F (k * b) D) (t : Fin k → (Fin b → F)) :
    evalAtTuple c t = MvPolynomial.eval (flattenTuple t) (toMvPoly c) := by
  classical
  simp [evalAtTuple, evalPolyAt, toMvPoly, monomialEval,
    MvPolynomial.eval_monomial]

end Erdos571_hypergraph
