import Erdos571_hypergraph_L22_PartPerm

open scoped BigOperators

namespace Erdos571_hypergraph

/-- A uniform complexity bound for all pieces, independent of the part
permutation. -/
noncomputable def rootM {k : ℕ} (U : PartiteRootedKHypergraph k)
    (a b : ℕ) : ℕ :=
  b * Fintype.card U.R + a * U.G.edges.card +
    (b + 1) * (Fintype.card U.V * Fintype.card U.V)

lemma samePartPair_card_le (U : PartiteRootedKHypergraph k)
    (π : Equiv.Perm (Fin k)) :
    Fintype.card (SamePartPair U π) ≤
      Fintype.card U.V * Fintype.card U.V := by
  classical
  calc
    Fintype.card (SamePartPair U π) ≤ Fintype.card (U.V × U.V) :=
      Fintype.card_subtype_le _
    _ = Fintype.card U.V * Fintype.card U.V := Fintype.card_prod _ _

lemma piece_m_le_rootM {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k)) :
    b * Fintype.card U.R + a * U.G.edges.card +
        (b + 1) * Fintype.card (SamePartPair U π) ≤
      rootM U a b := by
  classical
  unfold rootM
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left _ (samePartPair_card_le U π)) _

lemma piece_isConstructible_rootM (q : ℕ) [Fact q.Prime] {k b a D : ℕ}
    (P : HostParams (ZMod q) k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex (ZMod q) k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b) :
    IsConstructible q (b * Fintype.card U.V) (rootM U a b) (max D 1)
      (pieceSet P U w π c) :=
  (pieceSet_isConstructible q P U w π c).mono (piece_m_le_rootM P U π)

end Erdos571_hypergraph
