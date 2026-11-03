import Erdos571_hypergraph_Defs
import Erdos571_hypergraph_L1

namespace Erdos571_hypergraph

/-- The embedding of `U` into the `i`-th copy of its `p`-th rooted power. -/
noncomputable def copyMap {k : ℕ} (U : RootedKHypergraph k) (p : ℕ)
    (i : Fin p) : U.V → U.R ⊕ (Fin p × {x : U.V // x ∉ U.R}) :=
  fun v => if hv : v ∈ U.R then Sum.inl ⟨v, hv⟩
    else Sum.inr ⟨i, ⟨v, hv⟩⟩

lemma copyMap_injective {k : ℕ} (U : RootedKHypergraph k) (p : ℕ)
    (i : Fin p) : Function.Injective (copyMap U p i) := by
  intro v w h
  by_cases hv : v ∈ U.R
  · by_cases hw : w ∈ U.R
    · simpa [copyMap, hv, hw] using h
    · simp [copyMap, hv, hw] at h
  · by_cases hw : w ∈ U.R
    · simp [copyMap, hv, hw] at h
    · simpa [copyMap, hv, hw] using h

/-- The embedding of `U` into the `i`-th copy of its `p`-th power. -/
noncomputable abbrev copyEmb {k : ℕ} (U : RootedKHypergraph k) (p : ℕ)
    (i : Fin p) : U.V ↪ U.R ⊕ (Fin p × {x : U.V // x ∉ U.R}) :=
  ⟨copyMap U p i, copyMap_injective U p i⟩

/-- The `p`-th rooted power of `U`: `p` copies sharing the root set. -/
noncomputable def rootedPower {k : ℕ} (U : RootedKHypergraph k) (p : ℕ)
    (hp : 0 < p) : RootedKHypergraph k where
  V := U.R ⊕ (Fin p × {x : U.V // x ∉ U.R})
  G :=
    { edges := ((Finset.univ : Finset (Fin p)).product U.G.edges).image
        (fun q => q.2.image (copyMap U p q.1))
      edges_card := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨q, hq, rfl⟩
        rw [Finset.card_image_of_injOn]
        · exact U.G.edges_card q.2 (Finset.mem_product.mp hq).2
        · intro x _ y _ h
          exact copyMap_injective U p q.1 h }
  R := (Finset.univ : Finset U.R).image Sum.inl
  proper := by
    have hne : ∃ x : U.V, x ∉ U.R := by
      by_contra h
      apply U.proper
      ext x
      simp only [Finset.mem_univ, iff_true]
      by_contra hx
      exact h ⟨x, hx⟩
    obtain ⟨x, hx⟩ := hne
    intro h
    have : Sum.inr (⟨(⟨0, hp⟩ : Fin p), (⟨x, hx⟩ : {x : U.V // x ∉ U.R})⟩ :
        Fin p × {x : U.V // x ∉ U.R}) ∈
        (Finset.univ : Finset U.R).image Sum.inl := by
      rw [h]; exact Finset.mem_univ _
    rcases Finset.mem_image.mp this with ⟨r, -, hr⟩
    exact Sum.inl_ne_inr hr
  nonempty := by
    obtain ⟨r, hr⟩ := U.nonempty
    exact ⟨Sum.inl ⟨r, hr⟩,
      Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_univ _, rfl⟩⟩

/-- If every vertex of `U` lies in an edge, the same holds for its rooted
power. -/
lemma rootedPower_vertex_covered {k : ℕ} (U : RootedKHypergraph k)
    (hU : ∀ v : U.V, ∃ e ∈ U.G.edges, v ∈ e) (p : ℕ) (hp : 0 < p) :
    ∀ v : (rootedPower U p hp).V,
      ∃ e ∈ (rootedPower U p hp).G.edges, v ∈ e := by
  intro v
  cases v with
  | inl r =>
    obtain ⟨rv, hr⟩ := r
    obtain ⟨e, he, hre⟩ := hU rv
    refine ⟨e.image (copyMap U p ⟨0, hp⟩), ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨(⟨0, hp⟩, e), Finset.mem_product.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    · refine Finset.mem_image.mpr ⟨rv, hre, ?_⟩
      rw [copyMap]
      rw [dif_pos hr]
  | inr q =>
    obtain ⟨i, x, hx⟩ := q
    obtain ⟨e, he, hxe⟩ := hU x
    refine ⟨e.image (copyMap U p i), ?_, ?_⟩
    · exact Finset.mem_image.mpr
        ⟨(i, e), Finset.mem_product.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    · refine Finset.mem_image.mpr ⟨x, hxe, ?_⟩
      rw [copyMap]
      rw [dif_neg hx]

end Erdos571_hypergraph
