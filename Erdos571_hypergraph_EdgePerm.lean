import Erdos571_hypergraph_L3_Partite

namespace Erdos571_hypergraph

/-- The unique vertex of an edge in a prescribed part. -/
noncomputable def edgeVertexEmb {k : ℕ} {U : PartiteRootedKHypergraph k}
    {e : Finset U.V} (he : e ∈ U.G.edges) (i : Fin k) : U.V :=
  (U.edge_part e he i).choose

lemma edgeVertexEmb_mem {k : ℕ} {U : PartiteRootedKHypergraph k}
    {e : Finset U.V} (he : e ∈ U.G.edges) (i : Fin k) :
    edgeVertexEmb he i ∈ e :=
  ((U.edge_part e he i).choose_spec).1.1

lemma edgeVertexEmb_part {k : ℕ} {U : PartiteRootedKHypergraph k}
    {e : Finset U.V} (he : e ∈ U.G.edges) (i : Fin k) :
    U.part (edgeVertexEmb he i) = i :=
  ((U.edge_part e he i).choose_spec).1.2

lemma edgeVertexEmb_unique {k : ℕ} {U : PartiteRootedKHypergraph k}
    {e : Finset U.V} (he : e ∈ U.G.edges) {v : U.V} (hv : v ∈ e)
    {i : Fin k} (hpart : U.part v = i) : v = edgeVertexEmb he i :=
  ((U.edge_part e he i).choose_spec).2 v ⟨hv, hpart⟩

/-- The part permutation induced by an embedding of one edge. -/
noncomputable def edgePerm {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} (f : U.V ↪ X.V)
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (hfe : e.map f ∈ X.G.edges) : Equiv.Perm (Fin k) :=
  Equiv.ofBijective
    (fun i : Fin k => X.part (f (edgeVertexEmb he i)))
    (by
      constructor
      · intro i j h
        have hi : f (edgeVertexEmb he i) ∈ e.map f :=
          Finset.mem_map.mpr ⟨_, edgeVertexEmb_mem he i, rfl⟩
        have hj : f (edgeVertexEmb he j) ∈ e.map f :=
          Finset.mem_map.mpr ⟨_, edgeVertexEmb_mem he j, rfl⟩
        have hx : f (edgeVertexEmb he i) = f (edgeVertexEmb he j) :=
          (X.edge_part (e.map f) hfe (X.part (f (edgeVertexEmb he i)))).unique
            ⟨hi, rfl⟩ ⟨hj, h.symm⟩
        have hvv : edgeVertexEmb he i = edgeVertexEmb he j := f.injective hx
        have hp : U.part (edgeVertexEmb he i) = U.part (edgeVertexEmb he j) := by
          rw [hvv]
        rwa [edgeVertexEmb_part, edgeVertexEmb_part] at hp
      · intro j
        obtain ⟨y, ⟨hy, hyp⟩, -⟩ := X.edge_part (e.map f) hfe j
        rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
        refine ⟨U.part x, ?_⟩
        have hxv : x = edgeVertexEmb he (U.part x) :=
          edgeVertexEmb_unique he hx rfl
        rw [hxv] at hyp
        exact hyp)

lemma edgePerm_apply {k : ℕ} {U : PartiteRootedKHypergraph k}
    {X : PartiteKHypergraph k} (f : U.V ↪ X.V)
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (hfe : e.map f ∈ X.G.edges) {v : U.V} (hv : v ∈ e) :
    edgePerm f he hfe (U.part v) = X.part (f v) := by
  change X.part (f (edgeVertexEmb he (U.part v))) = X.part (f v)
  have h : v = edgeVertexEmb he (U.part v) := edgeVertexEmb_unique he hv rfl
  rw [← h]

lemma perm_eq_of_agree {k : ℕ} (π σ : Equiv.Perm (Fin k))
    {S : Finset (Fin k)} (hS : S.card = k - 1)
    (h : ∀ i ∈ S, π i = σ i) : π = σ := by
  classical
  let τ : Equiv.Perm (Fin k) := σ.symm * π
  have hfix : ∀ i ∈ S, τ i = i := by
    intro i hi
    simp [τ, h i hi]
  have hτ : τ = 1 := by
    by_contra hne
    have hlt := Equiv.Perm.fixed_point_card_lt_of_ne_one hne
    rw [Fintype.card_fin] at hlt
    have hle : S.card ≤
        (Finset.univ.filter (fun x : Fin k => τ x = x)).card := by
      apply Finset.card_le_card
      intro i hi
      simp [hfix i hi]
    omega
  have hss : σ.symm * π = 1 := by simpa [τ] using hτ
  calc
    π = σ * (σ.symm * π) := by
      ext x
      simp
    _ = σ * 1 := by rw [hss]
    _ = σ := by simp

/-- An embedding of `U` determines the part permutation uniquely as soon as
`U` has an edge: the edge selects one vertex in each part. -/
lemma CompatibleEmbedding.sigma_unique {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {π π' : Equiv.Perm (Fin k)}
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (f : CompatibleEmbedding U X w π)
    (g : CompatibleEmbedding U X w π') (h : f.toFun = g.toFun) :
    π = π' := by
  apply Equiv.ext
  intro i
  have h1 : X.part (f.toFun (edgeVertexEmb he i)) = π i := by
    simpa [edgeVertexEmb_part] using f.part_compat (edgeVertexEmb he i)
  have h2 : X.part (g.toFun (edgeVertexEmb he i)) = π' i := by
    simpa [edgeVertexEmb_part] using g.part_compat (edgeVertexEmb he i)
  calc
    π i = X.part (f.toFun (edgeVertexEmb he i)) := h1.symm
    _ = X.part (g.toFun (edgeVertexEmb he i)) := by rw [h]
    _ = π' i := h2

end Erdos571_hypergraph
