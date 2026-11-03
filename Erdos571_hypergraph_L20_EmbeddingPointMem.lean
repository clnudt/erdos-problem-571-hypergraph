import Erdos571_hypergraph_L19_EmbeddingPoint

namespace Erdos571_hypergraph

/-- The host tuple selected by an edge under the embedding `φ`. -/
noncomputable def embeddingEdgeTuple {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (φ : U.V → HostVertex F k b) : Fin k → (Fin b → F) :=
  fun i l => (φ (edgeVertexEmb he (π.symm i))).2 l

lemma edgeTuple_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    {e : Finset U.V} (he : e ∈ U.G.edges) :
    edgeTuple U π he (embeddingPoint (P := P) U π φ) =
      embeddingEdgeTuple U π he φ.toFun := by
  funext i l
  simp [edgeTuple, embeddingEdgeTuple, embeddingPoint, edgeVar, varIndex]

lemma map_embedding_eq_hostEdge {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    {e : Finset U.V} (he : e ∈ U.G.edges)
    (φ : CompatibleEmbedding U (hostPartite P) w π) :
    e.map ⟨φ.toFun, φ.inj⟩ = hostEdge (embeddingEdgeTuple U π he φ.toFun) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨v, hv, rfl⟩
    refine Finset.mem_image.mpr ⟨π (U.part v), Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · change π (U.part v) = (φ.toFun v).1
      exact (φ.part_compat v).symm
    · funext l
      have h : edgeVertexEmb he (π.symm (π (U.part v))) = v :=
        (edgeVertexEmb_unique he hv (by simp)).symm
      have h' : edgeVertexEmb he (U.part v) = v := by simpa using h
      simp [embeddingEdgeTuple, h']
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    let v : U.V := edgeVertexEmb he (π.symm i)
    have hv : v ∈ e := edgeVertexEmb_mem he (π.symm i)
    refine Finset.mem_map.mpr ⟨v, hv, ?_⟩
    apply Prod.ext
    · change (φ.toFun v).1 = i
      have h1 : (φ.toFun v).1 = π (U.part v) := by
        simpa [hostPartite] using φ.part_compat v
      rw [h1]
      have h2 : U.part v = π.symm i := edgeVertexEmb_part he (π.symm i)
      rw [h2]
      simp
    · funext l
      simp [embeddingEdgeTuple, v]

lemma eval_rootPoly_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π) (r : U.R) (j : Fin b) :
    MvPolynomial.eval (embeddingPoint (P := P) U π φ)
      (rootPoly U w r j) = 0 := by
  have hr : φ.toFun r.1 = w r := by
    simpa using φ.root_compat r.1 r.2
  simp [rootPoly, embeddingPoint, varIndex, hr]

lemma eval_pairEqPoly_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    (p : SamePartPair U π) {l : Fin b}
    (hl : l < embeddingChoice U π φ p) :
    MvPolynomial.eval (embeddingPoint (P := P) U π φ)
      (pairEqPoly U p.1.1 p.1.2 l) = 0 := by
  have h := embeddingChoice_min U π φ p hl
  simp [pairEqPoly, embeddingPoint, varIndex, h]

lemma eval_pairNePoly_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    (p : SamePartPair U π) :
    MvPolynomial.eval (embeddingPoint (P := P) U π φ)
      (pairNePoly U p.1.1 p.1.2 (embeddingChoice U π φ p)) ≠ 0 := by
  have h := embeddingChoice_spec U π φ p
  simpa [pairNePoly, pairEqPoly, embeddingPoint, varIndex] using sub_ne_zero.mpr h

lemma eval_edgePoly_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin a) :
    MvPolynomial.eval (embeddingPoint (P := P) U π φ)
      (edgePoly P U he π j) = 0 := by
  classical
  rw [edgePoly_eval]
  change evalAtTuple (P.coeffs j)
    (edgeTuple U π he (embeddingPoint (P := P) U π φ)) = 0
  rw [edgeTuple_embeddingPoint U π φ he]
  have hmem := φ.edge_map e he
  rw [map_embedding_eq_hostEdge U π he φ] at hmem
  change hostEdge (embeddingEdgeTuple U π he φ.toFun) ∈ hostEdges P at hmem
  unfold hostEdges at hmem
  rcases Finset.mem_image.mp hmem with ⟨t, ht, hte⟩
  have ht_eq : t = embeddingEdgeTuple U π he φ.toFun :=
    hostEdge_injective hte
  subst ht_eq
  exact (Finset.mem_filter.mp ht).2 j

/-- A compatible embedding gives a point of the piece determined by its
first-difference choice. -/
theorem embeddingPoint_mem_pieceSet {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π) :
    embeddingPoint (P := P) U π φ ∈
      pieceSet P U w π (embeddingChoice U π φ) := by
  classical
  constructor
  · intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · rcases Finset.mem_union.mp hg with hg | hg
      · unfold rootEqs at hg
        rcases Finset.mem_image.mp hg with ⟨r, -, rfl⟩
        exact eval_rootPoly_embeddingPoint U π φ r.1 r.2
      · unfold edgeEqs at hg
        rcases Finset.mem_image.mp hg with ⟨q, -, rfl⟩
        exact eval_edgePoly_embeddingPoint U π φ q.1.2 q.2
    · unfold pairEqs at hg
      rcases Finset.mem_image.mp hg with ⟨q, -, rfl⟩
      by_cases h : q.2 < embeddingChoice U π φ q.1
      · simp only [h, if_true]
        exact eval_pairEqPoly_embeddingPoint U π φ q.1 h
      · simp only [h, if_false]
        rfl
  · intro h hh
    unfold pairNeEqs at hh
    rcases Finset.mem_image.mp hh with ⟨p, -, rfl⟩
    exact eval_pairNePoly_embeddingPoint U π φ p

end Erdos571_hypergraph
