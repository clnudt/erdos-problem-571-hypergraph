import Erdos571_hypergraph_PartitePower

namespace Erdos571_hypergraph

/-- The partite version of `F_{k,r}`: the `p`-th power of the partite
suspension of a bipartite rooted graph. -/
noncomputable def FkrPartite {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (p : ℕ) (hp : 0 < p) :
    PartiteRootedKHypergraph k :=
  partitePower (suspensionPartite k hk B) p hp

end Erdos571_hypergraph
