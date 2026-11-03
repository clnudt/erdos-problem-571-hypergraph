import Erdos571_hypergraph_L6_Turan

namespace Erdos571_hypergraph

/-- Relabel the vertices of a `k`-graph along an equivalence. -/
noncomputable abbrev mapKHypergraph {k : ℕ} {V W : Type*} (e : V ≃ W)
    (H : KHypergraph k V) : KHypergraph k W where
  edges := by
    classical
    exact H.edges.image (fun s => s.map e.toEmbedding)
  edges_card := by
    classical
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    rw [Finset.card_map]
    exact H.edges_card t ht

/-- Relabelling vertices preserves the existence of a copy. -/
lemma isCopy_mapKHypergraph_iff {k : ℕ} {V V' W : Type*} (e : V' ≃ W)
    (F : KHypergraph k V) (H : KHypergraph k V') :
    IsCopy F (mapKHypergraph e H) ↔ IsCopy F H := by
  classical
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f.trans e.symm.toEmbedding, ?_⟩
    intro s hs
    rcases Finset.mem_image.mp (hf s hs) with ⟨t, ht, hteq⟩
    have h := congrArg (Finset.map e.symm.toEmbedding) hteq
    have h' : t = Finset.map (f.trans e.symm.toEmbedding) s := by
      simpa [Finset.map_map, Finset.map_refl] using h
    rw [← h']
    exact ht
  · rintro ⟨g, hg⟩
    refine ⟨g.trans e.toEmbedding, ?_⟩
    intro s hs
    refine Finset.mem_image.mpr ⟨s.map g, hg s hs, ?_⟩
    rw [Finset.map_map]

/-- Relabel the vertices of a `k`-graph along an embedding. -/
noncomputable abbrev mapKHypergraphEmb {k : ℕ} {V W : Type*} (e : V ↪ W)
    (H : KHypergraph k V) : KHypergraph k W where
  edges := by
    classical
    exact H.edges.image (fun s => s.map e)
  edges_card := by
    classical
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    rw [Finset.card_map]
    exact H.edges_card t ht

/-- Relabelling vertices along an embedding preserves the number of edges. -/
lemma card_mapKHypergraphEmb {k : ℕ} {V W : Type*} (e : V ↪ W)
    (H : KHypergraph k V) :
    (mapKHypergraphEmb e H).edges.card = H.edges.card := by
  classical
  unfold mapKHypergraphEmb
  rw [Finset.card_image_of_injOn]
  intro s _ t _ h
  exact Finset.map_injective e h

/-- If `F` has no isolated vertices, then adding isolated vertices to a host
cannot create a copy of `F`. -/
lemma isCopy_mapEmb_of_no_isolated {k : ℕ} {V V' W : Type*}
    [Nonempty V'] (F : KHypergraph k V)
    (hF : ∀ v : V, ∃ s ∈ F.edges, v ∈ s)
    (e : V' ↪ W) (H : KHypergraph k V') :
    IsCopy F (mapKHypergraphEmb e H) → IsCopy F H := by
  classical
  rintro ⟨f, hf⟩
  have hex : ∀ v : V, ∃ u : V', e u = f v := by
    intro v
    obtain ⟨s, hs, hvs⟩ := hF v
    have hmem : f v ∈ s.map f := Finset.mem_map.mpr ⟨v, hvs, rfl⟩
    have hmap : s.map f ∈ (mapKHypergraphEmb e H).edges := hf s hs
    rcases Finset.mem_image.mp hmap with ⟨t, ht, hteq⟩
    rw [← hteq] at hmem
    rcases Finset.mem_map.mp hmem with ⟨u, hu, heu⟩
    exact ⟨u, heu⟩
  let g : V → V' := fun v => Function.invFun e (f v)
  have hg : ∀ v, e (g v) = f v := fun v => Function.invFun_eq (hex v)
  have ginj : Function.Injective g := by
    intro v w h
    apply f.injective
    rw [← hg v, ← hg w, h]
  let gEmb : V ↪ V' := ⟨g, ginj⟩
  refine ⟨gEmb, ?_⟩
  intro s hs
  have hmap : s.map f ∈ (mapKHypergraphEmb e H).edges := hf s hs
  rcases Finset.mem_image.mp hmap with ⟨t, ht, hteq⟩
  have hEq : s.map gEmb = t := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      rcases Finset.mem_map.mp hu with ⟨x, hx, rfl⟩
      have hfx : f x ∈ t.map e := by
        rw [hteq]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      rcases Finset.mem_map.mp hfx with ⟨y, hy, hyeq⟩
      have hxy : g x = y := e.injective (by rw [hg x, hyeq])
      change g x ∈ t
      rwa [hxy]
    · intro hu
      have heu : e u ∈ t.map e := Finset.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hteq] at heu
      rcases Finset.mem_map.mp heu with ⟨x, hx, hxeq⟩
      refine Finset.mem_map.mpr ⟨x, hx, ?_⟩
      apply e.injective
      change e (g x) = e u
      rw [hg x, hxeq]
  rw [hEq]
  exact ht

end Erdos571_hypergraph
