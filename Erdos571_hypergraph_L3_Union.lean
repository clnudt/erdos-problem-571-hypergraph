import Erdos571_hypergraph_L3_Partite

namespace Erdos571_hypergraph

/-- Vertices of the union graph `H(c)`: roots are shared, while interior
vertices are indexed by the copy number. -/
inductive UnionVertex {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ) where
  | root (r : U.V) (hr : r ∈ U.R)
  | interior (x : U.V) (hx : x ∉ U.R) (i : Fin s)
  deriving DecidableEq, Fintype

/-- The equivalence relation identifying interior vertices with the same
image under the tuple of embeddings. -/
def UnionRel {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    UnionVertex U s → UnionVertex U s → Prop :=
  Relation.EqvGen (fun a b =>
    match a, b with
    | UnionVertex.interior x _ i, UnionVertex.interior y _ j =>
        (φ i).2.toFun x = (φ j).2.toFun y
    | _, _ => False)

/-- The image in `X` of a union vertex. -/
noncomputable def unionImage {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    UnionVertex U s → X.V
  | UnionVertex.root r hr => w ⟨r, hr⟩
  | UnionVertex.interior x _ i => (φ i).2.toFun x

/-- Equivalent union vertices have the same image in `X`. -/
lemma unionRel_image {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    {a b : UnionVertex U s} (h : UnionRel U X w s φ a b) :
    unionImage U X w s φ a = unionImage U X w s φ b := by
  induction h with
  | rel a b hab =>
      cases a with
      | root r hr =>
          cases b <;> simp at hab
      | interior x hx i =>
          cases b with
          | root r hr => simp at hab
          | interior y hy j =>
              simpa [unionImage] using hab
  | refl a => rfl
  | symm a b h ih => exact ih.symm
  | trans a b c h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- The setoid whose equivalence classes are union vertices. -/
def unionSetoid {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    Setoid (UnionVertex U s) where
  r := UnionRel U X w s φ
  iseqv :=
    ⟨fun a => Relation.EqvGen.refl a,
     fun h => Relation.EqvGen.symm _ _ h,
     fun h₁ h₂ => Relation.EqvGen.trans _ _ _ h₁ h₂⟩

/-- The canonical map from `U` into the union quotient, sending an interior
vertex to its copy `i`. -/
noncomputable def unionEmbed {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (i : Fin s) (v : U.V) : Quotient (unionSetoid U X w s φ) :=
  if hv : v ∈ U.R then Quotient.mk (unionSetoid U X w s φ) (UnionVertex.root v hv)
  else Quotient.mk (unionSetoid U X w s φ) (UnionVertex.interior v hv i)

/-- For a fixed copy, the map into the union quotient is injective. -/
lemma unionEmbed_injective {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (i : Fin s) :
    Function.Injective (unionEmbed U X w s φ i) := by
  intro x y h
  by_cases hx : x ∈ U.R <;> by_cases hy : y ∈ U.R
  · have h' : Quotient.mk (unionSetoid U X w s φ) (UnionVertex.root x hx) =
        Quotient.mk (unionSetoid U X w s φ) (UnionVertex.root y hy) := by
      simpa [unionEmbed, hx, hy] using h
    have hrel : UnionRel U X w s φ
        (UnionVertex.root x hx) (UnionVertex.root y hy) :=
      Quotient.exact h'
    have himg := unionRel_image U X w s φ hrel
    simp only [unionImage] at himg
    exact Subtype.ext_iff.mp (hw himg)
  · have h' : Quotient.mk (unionSetoid U X w s φ) (UnionVertex.root x hx) =
        Quotient.mk (unionSetoid U X w s φ) (UnionVertex.interior y hy i) := by
      simpa [unionEmbed, hx, hy] using h
    have hrel : UnionRel U X w s φ
        (UnionVertex.root x hx) (UnionVertex.interior y hy i) :=
      Quotient.exact h'
    have himg := unionRel_image U X w s φ hrel
    simp only [unionImage] at himg
    have hroot : (φ i).2.toFun x = w ⟨x, hx⟩ :=
      (φ i).2.root_compat x hx
    have hxy : x = y := (φ i).2.inj (hroot.trans himg)
    exact absurd (hxy ▸ hx) hy
  · have h' : Quotient.mk (unionSetoid U X w s φ) (UnionVertex.interior x hx i) =
        Quotient.mk (unionSetoid U X w s φ) (UnionVertex.root y hy) := by
      simpa [unionEmbed, hx, hy] using h
    have hrel : UnionRel U X w s φ
        (UnionVertex.interior x hx i) (UnionVertex.root y hy) :=
      Quotient.exact h'
    have himg := unionRel_image U X w s φ hrel
    simp only [unionImage] at himg
    have hroot : (φ i).2.toFun y = w ⟨y, hy⟩ :=
      (φ i).2.root_compat y hy
    have hxy : y = x := (φ i).2.inj (hroot.trans himg.symm)
    exact absurd (hxy ▸ hy) hx
  · have h' : Quotient.mk (unionSetoid U X w s φ) (UnionVertex.interior x hx i) =
        Quotient.mk (unionSetoid U X w s φ) (UnionVertex.interior y hy i) := by
      simpa [unionEmbed, hx, hy] using h
    have hrel : UnionRel U X w s φ
        (UnionVertex.interior x hx i) (UnionVertex.interior y hy i) :=
      Quotient.exact h'
    have himg := unionRel_image U X w s φ hrel
    simp only [unionImage] at himg
    exact (φ i).2.inj himg

/-- The image of one edge of `U` in the `i`-th copy, inside the union
quotient. -/
noncomputable def unionEdge {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (i : Fin s) (e : Finset U.V) :
    Finset (Quotient (unionSetoid U X w s φ)) :=
  e.map ⟨unionEmbed U X w s φ i,
    unionEmbed_injective U X w hw s φ i⟩

lemma unionEdge_card {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    (unionEdge U X w hw s φ i e).card = k := by
  rw [unionEdge, Finset.card_map, U.G.edges_card e he]

/-- The edge set of the union graph. -/
noncomputable def unionEdges {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    Finset (Finset (Quotient (unionSetoid U X w s φ))) := by
  classical
  exact (Finset.univ : Finset (Fin s)).biUnion (fun i =>
    U.G.edges.image (fun e => unionEdge U X w hw s φ i e))

/-- The union graph `H(c)`. -/
noncomputable def unionGraph {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    KHypergraph k (Quotient (unionSetoid U X w s φ)) := by
  classical
  exact
    { edges := unionEdges U X w hw s φ
      edges_card := by
        intro e he
        rcases (by simpa [unionEdges] using he) with ⟨i, e₀, he₀, rfl⟩
        exact unionEdge_card U X w hw s φ i he₀ }

/-- The number of interior vertices of the union graph. -/
noncomputable def hUnion {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) : ℕ := by
  classical
  exact Fintype.card (Quotient (unionSetoid U X w s φ)) - U.R.card

/-- The number of edges of the union graph. -/
noncomputable def eUnion {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) : ℕ :=
  (unionGraph U X w hw s φ).edges.card

lemma eUnion_le {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π) :
    eUnion U X w hw s φ ≤ s * U.G.edges.card := by
  classical
  change (unionEdges U X w hw s φ).card ≤ s * U.G.edges.card
  calc
    (unionEdges U X w hw s φ).card
        ≤ ∑ i : Fin s,
            (U.G.edges.image (fun e => unionEdge U X w hw s φ i e)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin s, U.G.edges.card := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.card_image_le
    _ = s * U.G.edges.card := by
          simp [Finset.sum_const]

end Erdos571_hypergraph
