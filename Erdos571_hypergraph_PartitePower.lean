import Erdos571_hypergraph_Power
import Erdos571_hypergraph_PartiteSuspension
import Erdos571_hypergraph_L3_Type

namespace Erdos571_hypergraph

/-- The part map of the rooted power: roots keep their part, interior
vertices keep the part of the original vertex. -/
noncomputable def powerPart {k : ℕ} (U : PartiteRootedKHypergraph k)
    (p : ℕ) :
    U.R ⊕ (Fin p × Interior U) → Fin k
  | Sum.inl r => U.part r.1
  | Sum.inr q => U.part q.2.1

lemma powerPart_copyMap {k : ℕ} (U : PartiteRootedKHypergraph k)
    (p : ℕ) (i : Fin p) (v : U.V) :
    powerPart U p (copyMap U.toRootedKHypergraph p i v) = U.part v := by
  by_cases hv : v ∈ U.R
  · simp [copyMap, powerPart, hv]
  · simp [copyMap, powerPart, hv]

/-- The rooted power, as a partite rooted `k`-graph. -/
noncomputable abbrev partitePower {k : ℕ} (U : PartiteRootedKHypergraph k)
    (p : ℕ) (hp : 0 < p) : PartiteRootedKHypergraph k :=
{ rootedPower U.toRootedKHypergraph p hp with
  part := powerPart U p
  edge_part := by
    intro e he j
    rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
    obtain ⟨i, eT⟩ := q
    have heT : eT ∈ U.G.edges := (Finset.mem_product.mp hq).2
    obtain ⟨x, ⟨hxe, hxpart⟩, huniq⟩ := U.edge_part eT heT j
    refine ⟨copyMap U.toRootedKHypergraph p i x, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hxe, rfl⟩
    · rw [powerPart_copyMap]
      exact hxpart
    · intro y hy
      rcases Finset.mem_image.mp hy.1 with ⟨z, hze, hzy⟩
      have hzpart : U.part z = j := by
        have h := hy.2
        rw [← hzy] at h
        rwa [powerPart_copyMap] at h
      have hzx : z = x := huniq z ⟨hze, hzpart⟩
      rw [← hzy, hzx] }

end Erdos571_hypergraph
