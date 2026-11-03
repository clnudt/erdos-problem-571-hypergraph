import Erdos571_hypergraph_L3_Type

namespace Erdos571_hypergraph

/-- The block of `(x,i)` in the partition `τ`. -/
noncomputable def blockOf {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (x : Interior U) (i : Fin s) :
    Finset (Interior U × Fin s) :=
  (τ.1.cover (x, i)).choose

lemma blockOf_mem {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (x : Interior U) (i : Fin s) :
    blockOf U s τ x i ∈ τ.1.blocks :=
  ((τ.1.cover (x, i)).choose_spec).1.1

lemma mem_blockOf {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (x : Interior U) (i : Fin s) :
    (x, i) ∈ blockOf U s τ x i :=
  ((τ.1.cover (x, i)).choose_spec).1.2

/-- Vertices of the type graph `H_τ`: roots plus blocks. -/
abbrev TypeVertex {k : ℕ} (U : PartiteRootedKHypergraph k) {s : ℕ}
    (τ : TypeSpace U s) :=
  U.R ⊕ {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}

/-- The map `ψ_i : V(U) → V(H_τ)`. -/
noncomputable def typeEmbed {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (i : Fin s) (v : U.V) : TypeVertex U τ :=
  if hv : v ∈ U.R then Sum.inl ⟨v, hv⟩
  else Sum.inr ⟨blockOf U s τ ⟨v, hv⟩ i, blockOf_mem U s τ ⟨v, hv⟩ i⟩

/-- The image of an edge of `U` in the `i`-th copy of `H_τ`. -/
noncomputable def typeEdgeSet {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (i : Fin s) (e : Finset U.V) :
    Finset (TypeVertex U τ) :=
  e.image (typeEmbed U s τ i)

/-- A type is admissible if, on every edge of `U` and in every copy, the map
`ψ_i` is injective.  Every type coming from an actual tuple is admissible. -/
def TypeAdmissible {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) : Prop :=
  ∀ (i : Fin s) {e : Finset U.V}, e ∈ U.G.edges →
    ∀ {x y : U.V}, x ∈ e → y ∈ e → x ≠ y →
      typeEmbed U s τ i x ≠ typeEmbed U s τ i y

lemma typeEdgeSet_card {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (hτa : TypeAdmissible U s τ)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    (typeEdgeSet U s τ i e).card = k := by
  classical
  rw [typeEdgeSet, Finset.card_image_of_injOn]
  · exact U.G.edges_card e he
  · intro x hx y hy hxy
    by_contra hne
    exact hτa i he hx hy hne hxy

lemma blockOf_partitionOf {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (x : Interior U) (i : Fin s) :
    blockOf U s (partitionOf U X w s φ, fun i => (φ i).1) x i =
      block U X w s φ (x, i) := by
  classical
  let τφ : TypeSpace U s := (partitionOf U X w s φ, fun i => (φ i).1)
  let h := τφ.1.cover (x, i)
  refine h.unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact blockOf_mem U s τφ x i
  · exact mem_blockOf U s τφ x i
  · exact Finset.mem_image.mpr ⟨(x, i), Finset.mem_univ _, rfl⟩
  · exact (mem_block_iff U X w s φ (x, i) (x, i)).mpr rfl

lemma partitionOf_admissible {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    TypeAdmissible U s (partitionOf U X w s φ, fun i => (φ i).1) := by
  classical
  intro i e he x y hx hy hxy hEq
  by_cases hxR : x ∈ U.R
  · by_cases hyR : y ∈ U.R
    · simp [typeEmbed, hxR, hyR] at hEq
      exact hxy hEq
    · simp [typeEmbed, hxR, hyR] at hEq
  · by_cases hyR : y ∈ U.R
    · simp [typeEmbed, hxR, hyR] at hEq
    · simp only [typeEmbed, hxR, hyR] at hEq
      have hblock :
          blockOf U s (partitionOf U X w s φ, fun i => (φ i).1) ⟨x, hxR⟩ i =
          blockOf U s (partitionOf U X w s φ, fun i => (φ i).1) ⟨y, hyR⟩ i :=
        Subtype.ext_iff.mp (Sum.inr.inj hEq)
      rw [blockOf_partitionOf] at hblock
      rw [blockOf_partitionOf] at hblock
      have himg : tupleImage U X w s φ (⟨x, hxR⟩, i) =
          tupleImage U X w s φ (⟨y, hyR⟩, i) := by
        have hxmem : (⟨x, hxR⟩, i) ∈ block U X w s φ (⟨y, hyR⟩, i) := by
          rw [← hblock]
          exact (mem_block_iff U X w s φ (⟨x, hxR⟩, i) (⟨x, hxR⟩, i)).mpr rfl
        exact (mem_block_iff U X w s φ (⟨y, hyR⟩, i) (⟨x, hxR⟩, i)).mp hxmem
      exact hxy ((φ i).2.inj himg)

/-- The type graph `H_τ` as a `k`-uniform hypergraph, for an admissible
type. -/
noncomputable def typeGraph {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (h : TypeAdmissible U s τ) :
    KHypergraph k (TypeVertex U τ) where
  edges := by
    classical
    exact Finset.univ.image (fun p : Fin s × {e : Finset U.V // e ∈ U.G.edges} =>
      typeEdgeSet U s τ p.1 p.2.1)
  edges_card := by
    classical
    intro e he
    rcases Finset.mem_image.mp he with ⟨p, -, rfl⟩
    exact typeEdgeSet_card U s τ h p.1 p.2.2

/-- The number of interior vertices of `H_τ`. -/
noncomputable def hτ {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) : ℕ :=
  τ.1.blocks.card

/-- The number of edges of `H_τ`. -/
noncomputable def eτ {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) : ℕ := by
  classical
  exact (Finset.univ.image (fun p : Fin s × {e : Finset U.V // e ∈ U.G.edges} =>
    typeEdgeSet U s τ p.1 p.2.1)).card

lemma eτ_eq_typeGraph_edges {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (h : TypeAdmissible U s τ) :
    eτ U s τ = (typeGraph U s τ h).edges.card := by
  rfl

end Erdos571_hypergraph
