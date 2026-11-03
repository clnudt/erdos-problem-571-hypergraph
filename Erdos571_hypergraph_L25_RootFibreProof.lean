import Erdos571_hypergraph_L24_PerPerm

open scoped BigOperators

namespace Erdos571_hypergraph

/-- Root-fibre dichotomy, proved from the single general algebraic-geometry
axiom `uniformDichotomy`. -/
theorem rootFibreDichotomy_proved {k b a D : ℕ} (hb : 0 < b)
    (U : PartiteRootedKHypergraph k) :
    ∃ Pstar qstar : ℕ, ∀ (q : ℕ) [Fact q.Prime], qstar ≤ q →
      ∀ (P : HostParams (ZMod q) k b a D)
        (w : U.R → HostVertex (ZMod q) k b),
        Cw U (hostPartite P) w ≤ Pstar ∨
          (q : ℚ) / 2 ≤ (Cw U (hostPartite P) w : ℚ) := by
  classical
  obtain ⟨P0, q0, hP0⟩ :=
    uniformDichotomy (b * Fintype.card U.V) (rootM U a b) (max D 1)
  let B : ℕ := b ^ (Fintype.card U.V * Fintype.card U.V)
  refine ⟨Nat.factorial k * (B * P0), q0, ?_⟩
  intro q _ hq P w
  rw [Cw_eq_sum_filter P U w]
  let s : Finset (Equiv.Perm (Fin k)) :=
    Finset.univ.filter (fun π => ∀ r : U.R, (w r).1 = π (U.part r.1))
  have hper : ∀ π ∈ s,
      Fintype.card (CompatibleEmbedding U (hostPartite P) w π) ≤ B * P0 ∨
        (q : ℚ) / 2 ≤
          (Fintype.card (CompatibleEmbedding U (hostPartite P) w π) : ℚ) := by
    intro π hπ
    rw [Finset.mem_filter] at hπ
    rcases compatibleEmbedding_dichotomy hb U P0 q0 hP0 hq P w π hπ.2 with
      hsmall | hlarge
    · left
      exact hsmall.trans (Nat.mul_le_mul_right _ le_rfl)
    · right
      exact hlarge
  rcases finset_sum_dichotomy s
    (fun π => Fintype.card (CompatibleEmbedding U (hostPartite P) w π))
    (B * P0) ((q : ℚ) / 2) hper with hsmall | hlarge
  · left
    calc
      s.sum (fun π => Fintype.card
          (CompatibleEmbedding U (hostPartite P) w π)) ≤
          s.card * (B * P0) := hsmall
      _ ≤ Nat.factorial k * (B * P0) := by
        apply Nat.mul_le_mul_right
        calc
          s.card ≤ (Finset.univ : Finset (Equiv.Perm (Fin k))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          _ = Nat.factorial k := by
            rw [Finset.card_univ, Fintype.card_perm]
            simp
  · right
    exact hlarge

end Erdos571_hypergraph
