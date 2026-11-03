import Erdos571_hypergraph_L5_Free

namespace Erdos571_hypergraph

/-- The set of edge counts in the definition of `turanNumber` is bounded. -/
lemma turanSet_bddAbove {k : ℕ} (F : FiniteKHypergraph k) (n : ℕ) :
    BddAbove {m : ℕ | ∃ H : KHypergraph k (Fin n),
      ¬ IsCopy F.graph H ∧ H.edges.card = m} := by
  classical
  refine ⟨Fintype.card (Finset (Fin n)), ?_⟩
  rintro m ⟨H, -, rfl⟩
  exact Finset.card_le_univ H.edges

/-- A concrete `F`-free graph gives a lower bound for the Turán number. -/
lemma le_turanNumber {k : ℕ} (F : FiniteKHypergraph k) {n m : ℕ}
    (h : ∃ H : KHypergraph k (Fin n), ¬ IsCopy F.graph H ∧ H.edges.card = m) :
    m ≤ turanNumber F n := by
  classical
  unfold turanNumber
  exact le_csSup (turanSet_bddAbove F n) h

end Erdos571_hypergraph
