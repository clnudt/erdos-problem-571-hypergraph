import Erdos571_hypergraph_Defs

namespace Erdos571_hypergraph

/-- A finite `k`-partite `k`-uniform hypergraph: every edge has exactly one
vertex in each part. -/
structure PartiteKHypergraph (k : ℕ) where
  V : Type
  [fintype : Fintype V]
  [decEq : DecidableEq V]
  part : V → Fin k
  G : KHypergraph k V
  edge_part : ∀ e ∈ G.edges, ∀ i : Fin k,
    ∃! v : V, v ∈ e ∧ part v = i

attribute [instance] PartiteKHypergraph.fintype PartiteKHypergraph.decEq

/-- A rooted `k`-partite `k`-uniform hypergraph. -/
structure PartiteRootedKHypergraph (k : ℕ) extends RootedKHypergraph k where
  part : V → Fin k
  edge_part : ∀ e ∈ G.edges, ∀ i : Fin k,
    ∃! v : V, v ∈ e ∧ part v = i

/-- A compatible embedding of a rooted partite `k`-graph into a partite
`k`-graph, extending a fixed root map `w` and using part permutation `π`. -/
structure CompatibleEmbedding {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (π : Equiv.Perm (Fin k)) where
  toFun : U.V → X.V
  inj : Function.Injective toFun
  root_compat : ∀ (r : U.V) (hr : r ∈ U.R), toFun r = w ⟨r, hr⟩
  edge_map : ∀ e ∈ U.G.edges, e.map ⟨toFun, inj⟩ ∈ X.G.edges
  part_compat : ∀ v : U.V, X.part (toFun v) = π (U.part v)

noncomputable instance compatibleEmbeddingFintype {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (π : Equiv.Perm (Fin k)) :
    Fintype (CompatibleEmbedding U X w π) :=
  Fintype.ofInjective (fun f => f.toFun) (by
    intro f g h
    cases f
    cases g
    simp only at h
    subst h
    rfl)

lemma CompatibleEmbedding.ext {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    {f g : CompatibleEmbedding U X w π} (h : f.toFun = g.toFun) : f = g := by
  cases f with
  | mk ff fi fr fe fp =>
    cases g with
    | mk gf gi gr ge gp =>
      simp only at h
      subst h
      rfl

lemma CompatibleEmbedding.edge_card {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) {e : Finset U.V}
    (he : e ∈ U.G.edges) :
    (e.map ⟨f.toFun, f.inj⟩).card = k := by
  rw [Finset.card_map, U.G.edges_card e he]

lemma CompatibleEmbedding.root_injective {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {π : Equiv.Perm (Fin k)}
    (f : CompatibleEmbedding U X w π) (hw : Function.Injective w) :
    Function.Injective (fun r : U.R => f.toFun r.1) := by
  intro r s h
  apply hw
  simpa [f.root_compat] using h

/-- The number of compatible embeddings of `U` into `X` extending `w`,
summed over all part permutations. -/
noncomputable def Cw {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) : ℕ :=
  ∑ π : Equiv.Perm (Fin k), Fintype.card (CompatibleEmbedding U X w π)

/-- Relabel the parts of a rooted partite `k`-graph by a permutation. -/
noncomputable abbrev partPermute {k : ℕ} (U : PartiteRootedKHypergraph k)
    (σ : Equiv.Perm (Fin k)) : PartiteRootedKHypergraph k :=
{ V := U.V
  fintype := U.fintype
  decEq := U.decEq
  G := U.G
  R := U.R
  proper := U.proper
  nonempty := U.nonempty
  part := fun v => σ (U.part v)
  edge_part := by
    intro e he i
    obtain ⟨v, ⟨hve, hvp⟩, huniq⟩ := U.edge_part e he (σ.symm i)
    refine ⟨v, ⟨hve, ?_⟩, ?_⟩
    · show σ (U.part v) = i
      rw [hvp]
      exact σ.apply_symm_apply i
    · intro y hy
      apply huniq y
      exact ⟨hy.1, by
        have h := congrArg σ.symm hy.2
        simpa using h⟩ }

@[simp] lemma partPermute_part {k : ℕ} (U : PartiteRootedKHypergraph k)
    (σ : Equiv.Perm (Fin k)) (v : U.V) :
    (partPermute U σ).part v = σ (U.part v) := rfl

/-- An embedding of `U` compatible with `π` is an embedding of the
part-permuted graph compatible with `π * σ⁻¹`. -/
noncomputable def compatibleEmbeddingPermute {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} (σ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin k)) :
    CompatibleEmbedding U X w π ≃
      CompatibleEmbedding (partPermute U σ) X w (π * σ⁻¹) where
  toFun e :=
    { e with
      part_compat := by
        intro v
        change X.part (e.toFun v) = (π * σ⁻¹) (σ (U.part v))
        rw [e.part_compat]
        simp }
  invFun e :=
    { e with
      part_compat := by
        intro v
        simpa [mul_apply] using e.part_compat v }
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The reverse direction of `compatibleEmbeddingPermute`. -/
noncomputable def compatibleEmbeddingUnpermute {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} (σ : Equiv.Perm (Fin k)) (π : Equiv.Perm (Fin k)) :
    CompatibleEmbedding (partPermute U σ) X w π ≃
      CompatibleEmbedding U X w (π * σ) where
  toFun e :=
    { e with
      part_compat := by
        intro v
        have h := e.part_compat v
        change X.part (e.toFun v) = π (σ (U.part v)) at h
        simpa [mul_apply] using h }
  invFun e :=
    { e with
      part_compat := by
        intro v
        change X.part (e.toFun v) = π (σ (U.part v))
        rw [e.part_compat]
        simp }
  left_inv e := by cases e; rfl
  right_inv e := by cases e; rfl

/-- The total number of compatible embeddings is invariant under relabelling
the parts of `U`. -/
lemma Cw_partPermute {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (σ : Equiv.Perm (Fin k)) :
    Cw U X w = Cw (partPermute U σ) X w := by
  classical
  rw [Cw, Cw]
  refine Finset.sum_bij (fun π _ => π * σ⁻¹) ?_ ?_ ?_ ?_
  · intro π _
    exact Finset.mem_univ _
  · intro π _ π' _ h
    exact mul_right_cancel h
  · intro π' _
    exact ⟨π' * σ, Finset.mem_univ _, by simp [mul_assoc]⟩
  · intro π _
    exact Fintype.card_congr (compatibleEmbeddingPermute (U := U) (X := X) (w := w) σ π)

/-- A root map is legal if it is injective and compatible with one global
permutation of the parts.  This is the manuscript's notion of a legal root
position, stated for an arbitrary partite host `X`. -/
def IsLegalRoot {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) : Prop :=
  Function.Injective w ∧ ∃ σ : Equiv.Perm (Fin k),
    ∀ r : U.R, X.part (w r) = σ (U.part r.1)

end Erdos571_hypergraph
