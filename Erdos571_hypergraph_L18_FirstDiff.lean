import Erdos571_hypergraph_L17_EdgeImage

namespace Erdos571_hypergraph

lemma exists_ne_coord {F : Type} {b : ℕ} {x y : Fin b → F} (h : x ≠ y) :
    ∃ j : Fin b, x j ≠ y j := by
  by_contra h'
  push_neg at h'
  exact h (funext h')

/-- The first coordinate at which two tuples differ. -/
noncomputable def firstDiff {F : Type} [DecidableEq F] {b : ℕ} (x y : Fin b → F)
    (h : x ≠ y) : Fin b :=
  (Finset.univ.filter (fun j => x j ≠ y j)).min' (by
    obtain ⟨j, hj⟩ := exists_ne_coord h
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩)

lemma firstDiff_mem {F : Type} [DecidableEq F] {b : ℕ} (x y : Fin b → F) (h : x ≠ y) :
    firstDiff x y h ∈ Finset.univ.filter (fun j => x j ≠ y j) :=
  Finset.min'_mem _ _

lemma firstDiff_spec {F : Type} [DecidableEq F] {b : ℕ} (x y : Fin b → F) (h : x ≠ y) :
    x (firstDiff x y h) ≠ y (firstDiff x y h) :=
  (Finset.mem_filter.mp (firstDiff_mem x y h)).2

lemma firstDiff_min {F : Type} [DecidableEq F] {b : ℕ} (x y : Fin b → F) (h : x ≠ y)
    {j : Fin b} (hj : j < firstDiff x y h) : x j = y j := by
  by_contra hne
  have hmem : j ∈ Finset.univ.filter (fun k => x k ≠ y k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
  have hle : firstDiff x y h ≤ j := Finset.min'_le _ _ hmem
  omega

/-- A point of a piece gives a compatible embedding. -/
noncomputable def pieceToEmbedding {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1))
    (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hz : z ∈ pieceSet P U w π c) :
    CompatibleEmbedding U (hostPartite P) w π := by
  classical
  have hroot : ∀ g ∈ rootEqs U w, MvPolynomial.eval z g = 0 := by
    intro g hg
    exact hz.1 g (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inl hg))))
  have hedge : ∀ g ∈ edgeEqs P U π, MvPolynomial.eval z g = 0 := by
    intro g hg
    exact hz.1 g (Finset.mem_union.mpr
      (Or.inl (Finset.mem_union.mpr (Or.inr hg))))
  let hinj : Function.Injective (vertexImage U π z) :=
    vertexImage_injective U π c z hz.2
  refine
    { toFun := vertexImage U π z
      inj := hinj
      root_compat := ?_
      edge_map := ?_
      part_compat := ?_ }
  · intro r hr
    exact vertexImage_root U w π hwpart z hroot ⟨r, hr⟩
  · intro e he
    exact edgeImage_mem_hostEdges P U π he z hinj hedge
  · intro v
    rfl

end Erdos571_hypergraph
