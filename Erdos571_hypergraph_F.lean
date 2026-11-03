import Erdos571_hypergraph_Power
import Erdos571_hypergraph_L1

namespace Erdos571_hypergraph

/-- The forbidden hypergraph `F_{k,r}`: the `p`-th rooted power of the
`k`-uniform suspension of a rooted graph `T`. -/
noncomputable def Fkr {k : ℕ} (hk : 2 ≤ k) (T : RootedGraph) (p : ℕ)
    (hp : 0 < p) : RootedKHypergraph k :=
  rootedPower (suspensionRooted k hk T) p hp

end Erdos571_hypergraph
