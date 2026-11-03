import Erdos571_hypergraph_L2
import Erdos571_hypergraph_L2_PolySpace
import Erdos571_hypergraph_L2_Comp
import Erdos571_hypergraph_L2_Separating

namespace Erdos571_hypergraph

/-- Evaluation of the full bounded-degree coefficient space at the points
`z i` is surjective, provided `m ≤ D + 1` and the points are distinct. -/
theorem evalPoly_surjective
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m D : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hD : m ≤ D + 1) :
    Function.Surjective (evalPoly (F := F) (n := n) (m := m) (D := D) z) := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    intro y
    refine ⟨0, ?_⟩
    funext i
    exact Fin.elim0 i
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    intro y
    rcases exists_separating_linear z hz hq with ⟨ℓ, hℓ⟩
    have hsurj := univariate_eval_surjective m (fun i => ℓ (z i)) hℓ
    rcases hsurj y with ⟨h, hh⟩
    let p : MvPolynomial (Fin n) F := compLinear ℓ h.1
    have hp : p.totalDegree ≤ D := by
      have h1 : p.totalDegree ≤ h.1.natDegree :=
        totalDegree_compLinear_le ℓ h.1
      have h2 : h.1.natDegree < m := by
        by_cases hzero : h.1 = 0
        · simp [hzero]
          omega
        · have hdeg : h.1.degree < (m : WithBot ℕ) :=
            Polynomial.mem_degreeLT.mp h.2
          exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdeg
      omega
    refine ⟨fun s => p.coeff s.1, ?_⟩
    funext i
    change evalPolyAt (z i) (fun s => p.coeff s.1) = y i
    rw [evalPolyAt_coeff p hp (z i)]
    rw [show p = compLinear ℓ h.1 from rfl, eval_compLinear]
    exact congrFun hh i

/-- Full Lemma 3.2: the number of coefficient vectors of total degree at
most `D` vanishing at `m` distinct points is `|P| / q^m`. -/
theorem multivariate_interpolation_count_full
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m D : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hD : m ≤ D + 1) :
    (Finset.univ.filter (fun c : PolyCoeff F n D =>
        evalPoly (F := F) (n := n) (m := m) (D := D) z c = 0)).card *
        Fintype.card F ^ m =
        Fintype.card (PolyCoeff F n D) := by
  exact interpolation_count m
    (evalPoly (F := F) (n := n) (m := m) (D := D) z)
    (evalPoly_surjective z hz hq hD)

end Erdos571_hypergraph
