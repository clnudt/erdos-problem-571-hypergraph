import Erdos571_hypergraph_L8_Asymptotic
import Erdos571_hypergraph_PartitePower

namespace Erdos571_hypergraph

/-- The forbidden graph `F_{k,r} = (S^k T)^{(p)}` has no isolated vertices. -/
lemma Fkr_vertex_covered {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) :
    ∀ v, ∃ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges, v ∈ e :=
  rootedPower_vertex_covered (suspensionPartite k hk B).toRootedKHypergraph
    (susp_vertex_covered hk B) p hp

end Erdos571_hypergraph
