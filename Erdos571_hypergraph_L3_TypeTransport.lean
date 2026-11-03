import Erdos571_hypergraph_L3_TypeGraph
import Erdos571_hypergraph_L3_TupleType

namespace Erdos571_hypergraph

/-- `blockOf` depends only on the partition component of the type. -/
lemma blockOf_eq_of_partition_eq {k s : ℕ} (U : PartiteRootedKHypergraph k)
    {τ σ : TypeSpace U s} (h : τ.1 = σ.1)
    (x : Interior U) (i : Fin s) :
    blockOf U s τ x i = blockOf U s σ x i := by
  have hmem : blockOf U s τ x i ∈ σ.1.blocks := by
    rw [← h]
    exact blockOf_mem U s τ x i
  exact ((σ.1.cover (x, i)).unique
    ⟨hmem, mem_blockOf U s τ x i⟩
    ⟨blockOf_mem U s σ x i, mem_blockOf U s σ x i⟩)





end Erdos571_hypergraph
