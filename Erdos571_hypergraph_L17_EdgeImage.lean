import Erdos571_hypergraph_L16_VertexImage

namespace Erdos571_hypergraph

/-- The embedding of `U.V` into the host induced by a point `z`. -/
noncomputable def vertexImageEmb {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (z : Fin (b * Fintype.card U.V) → F)
    (hinj : Function.Injective (vertexImage U π z)) :
    U.V ↪ HostVertex F k b :=
  ⟨vertexImage U π z, hinj⟩

/-- The tuple of host vertices selected by an edge. -/
noncomputable def edgeTuple {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (z : Fin (b * Fintype.card U.V) → F) :
    Fin k → (Fin b → F) :=
  fun i l => z (edgeVar U b he π (finProdFinEquiv (i, l)))

lemma edgeVar_self {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges) (v : U.V) (hv : v ∈ e)
    (l : Fin b)
    (z : Fin (b * Fintype.card U.V) → F) :
    edgeVar U b he π (finProdFinEquiv (π (U.part v), l)) =
      varIndex U b v l := by
  unfold edgeVar
  have h : edgeVertexEmb he (π.symm (π (U.part v))) = v :=
    (edgeVertexEmb_unique he hv (by simp)).symm
  have h' : edgeVertexEmb he (U.part v) = v := by simpa using h
  simp [h']

lemma map_vertexImage_eq_hostEdge {F : Type} [Field F] [DecidableEq F]
    {k b : ℕ} (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (z : Fin (b * Fintype.card U.V) → F)
    (hinj : Function.Injective (vertexImage U π z)) :
    e.map (vertexImageEmb U π z hinj) = hostEdge (edgeTuple U π he z) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    refine Finset.mem_image.mpr ⟨π (U.part v), Finset.mem_univ _, ?_⟩
    ext l
    · rfl
    · simp [hostEdge, vertexImageEmb, vertexImage, edgeTuple,
        edgeVar_self U π he v hv l z]
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    let v : U.V := edgeVertexEmb he (π.symm i)
    have hv : v ∈ e := edgeVertexEmb_mem he (π.symm i)
    refine Finset.mem_map.mpr ⟨v, hv, ?_⟩
    ext l
    · simp [vertexImageEmb, vertexImage, v, edgeVertexEmb_part]
    · simp [vertexImageEmb, vertexImage, edgeTuple, edgeVar, v]

lemma edgePoly_mem_edgeEqs {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin a) :
    edgePoly P U he π j ∈ edgeEqs P U π := by
  classical
  unfold edgeEqs
  exact Finset.mem_image.mpr ⟨(⟨e, he⟩, j), Finset.mem_univ _, rfl⟩

lemma edgeImage_mem_hostEdges {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (z : Fin (b * Fintype.card U.V) → F)
    (hinj : Function.Injective (vertexImage U π z))
    (hedge : ∀ g ∈ edgeEqs P U π, MvPolynomial.eval z g = 0) :
    e.map (vertexImageEmb U π z hinj) ∈ (hostPartite P).G.edges := by
  classical
  rw [map_vertexImage_eq_hostEdge U π he z hinj]
  change hostEdge (edgeTuple U π he z) ∈ hostEdges P
  rw [hostEdges]
  refine Finset.mem_image.mpr ⟨edgeTuple U π he z, ?_, rfl⟩
  · rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro j
    have h := hedge _ (edgePoly_mem_edgeEqs P U π he j)
    rw [edgePoly_eval] at h
    exact h

end Erdos571_hypergraph
