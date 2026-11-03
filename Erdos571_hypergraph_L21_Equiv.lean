import Erdos571_hypergraph_L20_EmbeddingPointMem

namespace Erdos571_hypergraph

lemma firstDiff_eq {F : Type} [DecidableEq F] {b : ℕ} {x y : Fin b → F}
    (h : x ≠ y) (c : Fin b)
    (hlt : ∀ l : Fin b, l < c → x l = y l)
    (hne : x c ≠ y c) : firstDiff x y h = c := by
  apply le_antisymm
  · exact Finset.min'_le
      (Finset.univ.filter (fun l : Fin b => x l ≠ y l)) c
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
  · by_contra hc
    have hlt' : firstDiff x y h < c := lt_of_not_ge hc
    exact (firstDiff_spec x y h) (hlt (firstDiff x y h) hlt')

lemma embeddingPoint_pieceToEmbedding {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1))
    (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hz : z ∈ pieceSet P U w π c) :
    embeddingPoint (P := P) U π
      (pieceToEmbedding P U w π hwpart c z hz) = z := by
  classical
  funext q
  rcases p : (vertexVarEquiv U b).symm q with ⟨v, j⟩
  have hq : varIndex U b v j = q := by
    rw [varIndex]
    rw [← p]
    exact (vertexVarEquiv U b).apply_symm_apply q
  simp only [embeddingPoint, pieceToEmbedding, vertexImage]
  rw [p]
  simp [hq]

lemma mem_pairEqs_of_lt {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) (p : SamePartPair U π) {l : Fin b}
    (hl : l < c p) :
    pairEqPoly U p.1.1 p.1.2 l ∈ pairEqs (F := F) U π c := by
  classical
  unfold pairEqs
  exact Finset.mem_image.mpr ⟨(p, l), Finset.mem_univ _, by simp [hl]⟩

lemma eval_pairEq_of_piece {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hz : z ∈ pieceSet P U w π c) (p : SamePartPair U π) {l : Fin b}
    (hl : l < c p) :
    MvPolynomial.eval z (pairEqPoly U p.1.1 p.1.2 l) = 0 :=
  hz.1 _ (Finset.mem_union.mpr
    (Or.inr (mem_pairEqs_of_lt U π c p hl)))

lemma mem_pairNeEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) (p : SamePartPair U π) :
    pairNePoly U p.1.1 p.1.2 (c p) ∈ pairNeEqs (F := F) U π c := by
  classical
  unfold pairNeEqs
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

lemma eval_pairNe_of_piece {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hz : z ∈ pieceSet P U w π c) (p : SamePartPair U π) :
    MvPolynomial.eval z (pairNePoly U p.1.1 p.1.2 (c p)) ≠ 0 :=
  hz.2 _ (mem_pairNeEqs U π c p)

lemma embeddingChoice_pieceToEmbedding {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1))
    (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hz : z ∈ pieceSet P U w π c) :
    embeddingChoice U π (pieceToEmbedding P U w π hwpart c z hz) = c := by
  classical
  funext p
  apply firstDiff_eq
  · intro l hl
    have h := eval_pairEq_of_piece P U w π c z hz p hl
    have h' : z (varIndex U b p.1.1 l) - z (varIndex U b p.1.2 l) = 0 := by
      simpa [pairEqPoly] using h
    simpa [vertexImage, pieceToEmbedding] using sub_eq_zero.mp h'
  · have h := eval_pairNe_of_piece P U w π c z hz p
    have h' : z (varIndex U b p.1.1 (c p)) -
        z (varIndex U b p.1.2 (c p)) ≠ 0 := by
      simpa [pairNePoly, pairEqPoly] using h
    simpa [vertexImage, pieceToEmbedding] using sub_ne_zero.mp h'

/-- Compatible embeddings are the disjoint union, over all first-difference
choices, of the corresponding constructible pieces. -/
noncomputable def embeddingPieceEquiv {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1)) :
    CompatibleEmbedding U (hostPartite P) w π ≃
      Σ c : SamePartPair U π → Fin b,
        {z : Fin (b * Fintype.card U.V) → F // z ∈ pieceSet P U w π c} where
  toFun φ :=
    ⟨embeddingChoice U π φ, embeddingPoint (P := P) U π φ,
      embeddingPoint_mem_pieceSet U π φ⟩
  invFun p :=
    pieceToEmbedding P U w π hwpart p.1 p.2.1 p.2.2
  left_inv φ := by
    apply CompatibleEmbedding.ext
    funext v
    exact vertexImage_embeddingPoint U π φ v
  right_inv p := by
    rcases p with ⟨c, z, hz⟩
    let φ := pieceToEmbedding P U w π hwpart c z hz
    have hchoice : embeddingChoice U π φ = c :=
      embeddingChoice_pieceToEmbedding P U w π hwpart c z hz
    change
      (⟨embeddingChoice U π φ,
        (⟨embeddingPoint (P := P) U π φ,
          embeddingPoint_mem_pieceSet U π φ⟩ :
          {z : Fin (b * Fintype.card U.V) → F //
            z ∈ pieceSet P U w π (embeddingChoice U π φ)})⟩ :
        Σ c : SamePartPair U π → Fin b,
          {z : Fin (b * Fintype.card U.V) → F // z ∈ pieceSet P U w π c}) =
      (⟨c, (⟨z, hz⟩ :
          {z : Fin (b * Fintype.card U.V) → F // z ∈ pieceSet P U w π c})⟩ :
        Σ c : SamePartPair U π → Fin b,
          {z : Fin (b * Fintype.card U.V) → F // z ∈ pieceSet P U w π c})
    refine Sigma.ext hchoice ?_
    apply (Subtype.heq_iff_coe_eq ?_).2
    · exact embeddingPoint_pieceToEmbedding P U w π hwpart c z hz
    · intro x
      change x ∈ pieceSet P U w π (embeddingChoice U π φ) ↔
        x ∈ pieceSet P U w π c
      rw [hchoice]

/-- The number of compatible embeddings is the sum of the cardinalities of the
constructible pieces. -/
noncomputable instance pieceSubtypeFintype {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b) :
    Fintype {z : Fin (b * Fintype.card U.V) → F //
      z ∈ pieceSet P U w π c} :=
  Fintype.ofInjective (fun z => z.1) (by
    intro a b h
    exact Subtype.ext h)

theorem card_compatibleEmbedding_eq_sum {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1)) :
    Fintype.card (CompatibleEmbedding U (hostPartite P) w π) =
      ∑ c : SamePartPair U π → Fin b,
        Fintype.card {z : Fin (b * Fintype.card U.V) → F //
          z ∈ pieceSet P U w π c} := by
  classical
  rw [Fintype.card_congr (embeddingPieceEquiv P U w π hwpart)]
  rw [Fintype.card_sigma]

end Erdos571_hypergraph
