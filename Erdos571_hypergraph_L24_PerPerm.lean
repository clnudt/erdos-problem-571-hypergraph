import Erdos571_hypergraph_L23_RootM

open scoped BigOperators

namespace Erdos571_hypergraph

/-- The per-permutation dichotomy for compatible embeddings. -/
lemma compatibleEmbedding_dichotomy {k b a D : ℕ} (hb : 0 < b)
    (U : PartiteRootedKHypergraph k) (P0 q0 : ℕ)
    (hP0 : ∀ (q : ℕ) [Fact q.Prime], q0 ≤ q →
      ∀ Y : Set (Fin (b * Fintype.card U.V) → ZMod q),
        IsConstructible q (b * Fintype.card U.V) (rootM U a b) (max D 1) Y →
          Nat.card Y ≤ P0 ∨ (q : ℚ) / 2 ≤ (Nat.card Y : ℚ))
    {q : ℕ} [Fact q.Prime] (hq : q0 ≤ q)
    (P : HostParams (ZMod q) k b a D)
    (w : U.R → HostVertex (ZMod q) k b) (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1)) :
    Fintype.card (CompatibleEmbedding U (hostPartite P) w π) ≤
        b ^ (Fintype.card U.V * Fintype.card U.V) * P0 ∨
      (q : ℚ) / 2 ≤
        (Fintype.card (CompatibleEmbedding U (hostPartite P) w π) : ℚ) := by
  classical
  rw [card_compatibleEmbedding_eq_sum P U w π hwpart]
  have hchoices : Fintype.card (SamePartPair U π → Fin b) ≤
      b ^ (Fintype.card U.V * Fintype.card U.V) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    exact Nat.pow_le_pow_right (by omega) (samePartPair_card_le U π)
  rcases sum_dichotomy
    (fun c : SamePartPair U π → Fin b =>
      Fintype.card {z : Fin (b * Fintype.card U.V) → ZMod q //
        z ∈ pieceSet P U w π c}) P0 ((q : ℚ) / 2)
    (by
      intro c
      have hc := hP0 q hq (pieceSet P U w π c)
        (piece_isConstructible_rootM q P U w π c)
      simpa [Nat.card_eq_fintype_card] using hc)
    with hsmall | hlarge
  · left
    calc
      (∑ c : SamePartPair U π → Fin b,
          Fintype.card {z : Fin (b * Fintype.card U.V) → ZMod q //
            z ∈ pieceSet P U w π c}) ≤
          Fintype.card (SamePartPair U π → Fin b) * P0 := hsmall
      _ ≤ b ^ (Fintype.card U.V * Fintype.card U.V) * P0 :=
        Nat.mul_le_mul_right _ hchoices
  · right
    exact hlarge

end Erdos571_hypergraph
