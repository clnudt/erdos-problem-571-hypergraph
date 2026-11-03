import Erdos571_hypergraph_L3_Partite

namespace Erdos571_hypergraph

/-- The `k`-tuple in `X` corresponding to an edge `e` of `U` under a
compatible embedding. -/
noncomputable def edgeTupleOf {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) {e : Finset U.V}
    (he : e ∈ U.G.edges) (i : Fin k) : X.V :=
  (X.edge_part (e.map ⟨f.toFun, f.inj⟩) (f.edge_map e he) i).choose

lemma edgeTupleOf_mem {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) {e : Finset U.V}
    (he : e ∈ U.G.edges) (i : Fin k) :
    edgeTupleOf f he i ∈ e.map ⟨f.toFun, f.inj⟩ :=
  ((X.edge_part (e.map ⟨f.toFun, f.inj⟩) (f.edge_map e he) i).choose_spec).1.1

lemma edgeTupleOf_part {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) {e : Finset U.V}
    (he : e ∈ U.G.edges) (i : Fin k) :
    X.part (edgeTupleOf f he i) = i :=
  ((X.edge_part (e.map ⟨f.toFun, f.inj⟩) (f.edge_map e he) i).choose_spec).1.2

lemma edgeTupleOf_unique {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) {e : Finset U.V}
    (he : e ∈ U.G.edges) {i : Fin k} {v : X.V}
    (hv : v ∈ e.map ⟨f.toFun, f.inj⟩) (hpart : X.part v = i) :
    v = edgeTupleOf f he i :=
  ((X.edge_part (e.map ⟨f.toFun, f.inj⟩) (f.edge_map e he) i).choose_spec).2
    v ⟨hv, hpart⟩

/-- An injective map sends distinct finite sets to distinct finite sets. -/
lemma finset_image_ne_of_ne {α β : Type} [DecidableEq β]
    {f : α → β} (hf : Function.Injective f)
    {s t : Finset α} (h : s ≠ t) :
    s.image f ≠ t.image f := by
  intro hst
  exact h ((Finset.image_inj hf).mp hst)

end Erdos571_hypergraph
