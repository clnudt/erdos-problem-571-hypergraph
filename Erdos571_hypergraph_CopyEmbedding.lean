import Erdos571_hypergraph_Adjacent
import Erdos571_hypergraph_FPartite

namespace Erdos571_hypergraph

lemma copyEdge_mem_F {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p)
    {e : Finset (suspensionPartite k hk B).V}
    (he : e ∈ (suspensionPartite k hk B).G.edges) (i : Fin p) :
    e.map (copyEmb (suspensionPartite k hk B).toRootedKHypergraph p i) ∈
      (partitePower (suspensionPartite k hk B) p hp).G.edges := by
  classical
  let U := suspensionPartite k hk B
  let F := partitePower U p hp
  change e.map (copyEmb U.toRootedKHypergraph p i) ∈ F.G.edges
  dsimp only [F, partitePower, rootedPower]
  exact Finset.mem_image.mpr
    ⟨(i, e), Finset.mem_product.mpr ⟨Finset.mem_univ _, he⟩, by
      rw [Finset.map_eq_image]
      simp [copyEmb]⟩

/-- The embedding induced on the `i`-th copy by an embedding of `F`. -/
noncomputable abbrev copyPhiEmb {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (i : Fin p) : (suspensionPartite k hk B).V ↪ X.V :=
  (copyEmb (suspensionPartite k hk B).toRootedKHypergraph p i).trans f

lemma copyPhiEmb_apply {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (i : Fin p) (v : (suspensionPartite k hk B).V) :
    (copyPhiEmb hk B p hp f i) v =
      f (copyMap (suspensionPartite k hk B).toRootedKHypergraph p i v) := rfl

lemma copyPhiEmb_injective {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (i : Fin p) : Function.Injective (copyPhiEmb hk B p hp f i) :=
  (copyPhiEmb hk B p hp f i).injective

lemma suspEdge_map_copyPhi {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (i : Fin p) {eT : Finset B.T.V} (heT : eT ∈ B.T.G.edges) :
    (eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map
        (copyPhiEmb hk B p hp f i) =
      ((eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map
        (copyEmb (suspensionPartite k hk B).toRootedKHypergraph p i)).map f := by
  rw [show copyPhiEmb hk B p hp f i =
    (copyEmb (suspensionPartite k hk B).toRootedKHypergraph p i).trans f from rfl]
  exact (Finset.map_map
    (copyEmb (suspensionPartite k hk B).toRootedKHypergraph p i) f _).symm

lemma copyPhi_edge_mem {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges)
    (i : Fin p) {eT : Finset B.T.V} (heT : eT ∈ B.T.G.edges) :
    (eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map
        (copyPhiEmb hk B p hp f i) ∈ X.G.edges := by
  rw [suspEdge_map_copyPhi hk B p hp f i heT]
  exact hcopy _ (copyEdge_mem_F hk B p hp
    (suspEdge_mem hk B heT) i)

noncomputable def copyRoot {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V) :
    (suspensionPartite k hk B).R → X.V :=
  fun r => f (Sum.inl r)

lemma copyPhi_root {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (i : Fin p) (r : (suspensionPartite k hk B).R) :
    copyPhiEmb hk B p hp f i r.1 = copyRoot hk B p hp f r := by
  change (copyPhiEmb hk B p hp f i) r.1 = (copyRoot hk B p hp f) r
  rw [copyPhiEmb_apply]
  simp [copyRoot, copyMap, r.2]

lemma copyPhi_edge_map {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges)
    (i : Fin p) {e : Finset (suspensionPartite k hk B).V}
    (he : e ∈ (suspensionPartite k hk B).G.edges) :
    e.map (copyPhiEmb hk B p hp f i) ∈ X.G.edges := by
  classical
  have he' : e ∈ suspEdges k B.T := by
    simpa [suspensionPartite, suspEdges] using he
  rcases Finset.mem_image.mp he' with ⟨eT, heT, rfl⟩
  exact copyPhi_edge_mem hk B p hp f hcopy i heT

noncomputable def baseTEdge {k : ℕ} (B : BipartiteRootedGraph) :
    {e : Finset B.T.V // e ∈ B.T.G.edges} :=
  ⟨B.edge_nonempty.choose, B.edge_nonempty.choose_spec⟩

noncomputable def copyPi {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges)
    (i : Fin p) : Equiv.Perm (Fin k) :=
  edgePerm (copyPhiEmb hk B p hp f i)
    (suspEdge_mem hk B (baseTEdge (k := k) B).2)
    (copyPhi_edge_mem hk B p hp f hcopy i (baseTEdge (k := k) B).2)

lemma copyPhi_part {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges)
    (i : Fin p) (v : (suspensionPartite k hk B).V) :
    X.part ((copyPhiEmb hk B p hp f i) v) =
      copyPi hk B p hp f hcopy i ((suspensionPartite k hk B).part v) := by
  classical
  obtain ⟨e, he, hv⟩ := susp_vertex_covered hk B v
  have he' : e ∈ suspEdges k B.T := by
    simpa [suspensionPartite, suspEdges] using he
  rcases Finset.mem_image.mp he' with ⟨eT, heT, rfl⟩
  have hchain := edgePerm_eq_of_chain hk B X (copyPhiEmb hk B p hp f i)
    (fun e => copyPhi_edge_mem hk B p hp f hcopy i e.2)
    ⟨eT, heT⟩ (baseTEdge (k := k) B)
  dsimp only [copyPi]
  rw [← hchain]
  exact (edgePerm_apply (copyPhiEmb hk B p hp f i)
    (suspEdge_mem hk B heT)
    (copyPhi_edge_mem hk B p hp f hcopy i heT) hv).symm

noncomputable def copyToCompatible {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (p : ℕ) (hp : 0 < p)
    {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges)
    (i : Fin p) :
    CompatibleEmbedding (suspensionPartite k hk B) X
      (copyRoot hk B p hp f) (copyPi hk B p hp f hcopy i) where
  toFun := copyPhiEmb hk B p hp f i
  inj := copyPhiEmb_injective hk B p hp f i
  root_compat := fun r hr => copyPhi_root hk B p hp f i ⟨r, hr⟩
  edge_map := by
    intro e he
    simpa using copyPhi_edge_map hk B p hp f hcopy i he
  part_compat := copyPhi_part hk B p hp f hcopy i

lemma copyToCompatible_injective {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (p : ℕ) (hp : 0 < p)
    {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges) :
    Function.Injective (fun i : Fin p =>
      (⟨copyPi hk B p hp f hcopy i,
        copyToCompatible hk B p hp f hcopy i⟩ :
        Σ π : Equiv.Perm (Fin k),
          CompatibleEmbedding (suspensionPartite k hk B) X
            (copyRoot hk B p hp f) π)) := by
  classical
  intro i j hij
  have hfun : copyPhiEmb hk B p hp f i = copyPhiEmb hk B p hp f j := by
    have := congrArg
      (fun e : Σ π : Equiv.Perm (Fin k),
        CompatibleEmbedding (suspensionPartite k hk B) X
          (copyRoot hk B p hp f) π => (e.2).toFun) hij
    simpa [copyToCompatible] using this
  have hne : ∃ x : (suspensionPartite k hk B).V,
      x ∉ (suspensionPartite k hk B).R := by
    by_contra h
    apply (suspensionPartite k hk B).proper
    ext x
    simp only [Finset.mem_univ, iff_true]
    by_contra hx
    exact h ⟨x, hx⟩
  obtain ⟨x, hx⟩ := hne
  have hfun' : (copyPhiEmb hk B p hp f i : (suspensionPartite k hk B).V → X.V) =
      copyPhiEmb hk B p hp f j :=
    congrArg (fun e : (suspensionPartite k hk B).V ↪ X.V =>
      (e : (suspensionPartite k hk B).V → X.V)) hfun
  have hpoint : f (copyMap (suspensionPartite k hk B).toRootedKHypergraph p i x) =
      f (copyMap (suspensionPartite k hk B).toRootedKHypergraph p j x) := by
    have := congrFun hfun' x
    rw [copyPhiEmb_apply, copyPhiEmb_apply] at this
    exact this
  have hcm : copyMap (suspensionPartite k hk B).toRootedKHypergraph p i x =
      copyMap (suspensionPartite k hk B).toRootedKHypergraph p j x :=
    f.injective hpoint
  have h1 : copyMap (suspensionPartite k hk B).toRootedKHypergraph p i x =
      Sum.inr ⟨i, ⟨x, hx⟩⟩ := by simp [copyMap, hx]
  have h2 : copyMap (suspensionPartite k hk B).toRootedKHypergraph p j x =
      Sum.inr ⟨j, ⟨x, hx⟩⟩ := by simp [copyMap, hx]
  rw [h1, h2] at hcm
  exact (Prod.ext_iff.mp (Sum.inr.inj hcm)).1

noncomputable def copyW {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V) :
    (suspensionPartite k hk B).R → X.V :=
  copyRoot hk B p hp f

lemma Cw_ge_p {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges) :
    p ≤ Cw (suspensionPartite k hk B) X (copyW hk B p hp f) := by
  classical
  let emb : Fin p → Σ π : Equiv.Perm (Fin k),
      CompatibleEmbedding (suspensionPartite k hk B) X
        (copyW hk B p hp f) π :=
    fun i => ⟨copyPi hk B p hp f hcopy i,
      copyToCompatible hk B p hp f hcopy i⟩
  have hinj : Function.Injective emb := by
    intro i j h
    change (⟨copyPi hk B p hp f hcopy i,
        copyToCompatible hk B p hp f hcopy i⟩ :
        Σ π : Equiv.Perm (Fin k),
          CompatibleEmbedding (suspensionPartite k hk B) X
            (copyW hk B p hp f) π) =
      ⟨copyPi hk B p hp f hcopy j,
        copyToCompatible hk B p hp f hcopy j⟩ at h
    exact copyToCompatible_injective hk B p hp f hcopy h
  have h := Fintype.card_le_of_injective emb hinj
  simpa [Cw, Fintype.card_sigma, emb] using h

/-- The root map of an arbitrary copy of the `p`-th power is a legal root
position, with the part permutation of any one of its branches. -/
lemma copyW_isLegal {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) {X : PartiteKHypergraph k}
    (f : (partitePower (suspensionPartite k hk B) p hp).V ↪ X.V)
    (hcopy : ∀ e ∈ (partitePower (suspensionPartite k hk B) p hp).G.edges,
      e.map f ∈ X.G.edges) :
    IsLegalRoot (suspensionPartite k hk B) X (copyW hk B p hp f) := by
  classical
  constructor
  · intro r s h
    apply Subtype.ext
    have h' : f (Sum.inl (r : (suspensionPartite k hk B).R)) =
        f (Sum.inl (s : (suspensionPartite k hk B).R)) := h
    have hrs : r = s := Sum.inl_injective (f.injective h')
    exact congrArg Subtype.val hrs
  · let i0 : Fin p := ⟨0, hp⟩
    refine ⟨copyPi hk B p hp f hcopy i0, ?_⟩
    intro r
    have h := copyPhi_part hk B p hp f hcopy i0 r.1
    rwa [copyPhi_root hk B p hp f i0 r] at h

end Erdos571_hypergraph
