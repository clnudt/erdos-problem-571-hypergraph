import Erdos571_hypergraph_L3_TypeEmbeddingOf

namespace Erdos571_hypergraph

/-- A type embedding parameterized only by the type `τ`, with no separate
part-function parameter.  Part compatibility is supplied as a hypothesis
when a tuple is reconstructed. -/
structure TypeEmbeddingOf' {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) where
  toFun : TypeVertex U τ → X.V
  inj : Function.Injective toFun
  root_compat : ∀ r : U.R, toFun (Sum.inl r) = w r
  edge_mem : ∀ (i : Fin s) {e : Finset U.V}, e ∈ U.G.edges →
    (typeEdgeSet U s τ i e).image toFun ∈ X.G.edges

/-- The type-parameterized embedding induced by a tuple, without a separate
part-function parameter. -/
noncomputable def tupleToTypeEmbeddingOf' {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hw : Function.Injective w) (s : ℕ)
    (φ : Tuple U X w s) :
    TypeEmbeddingOf' U X w s (tupleType U X w s φ) where
  toFun := tupleToEmbedding U X w s φ
  inj := tupleToEmbedding_injective U X w hw s φ
  root_compat := by
    intro r
    rfl
  edge_mem := by
    intro i e he
    exact tupleToEmbedding_edge_mem U X w s φ i he

/-- View a part-free embedding as an embedding with the canonical part
function `b ↦ X.part (Φ (inr b))`. -/
noncomputable def toTypeEmbeddingOf {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (Φ : TypeEmbeddingOf' U X w s τ)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) :
    TypeEmbeddingOf U X w s τ
      (fun b => X.part (Φ.toFun (Sum.inr b))) where
  toFun := Φ.toFun
  inj := Φ.inj
  root_compat := Φ.root_compat
  part_compat := by
    intro v
    cases v with
    | inl r =>
        simp [typeVertexPartOf, Φ.root_compat, hwpart r]
    | inr b =>
        rfl
  edge_mem := Φ.edge_mem

/-- The tuple induced by a part-free type embedding, using the canonical
part function. -/
noncomputable def typeEmbeddingOfToTuple' {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (Φ : TypeEmbeddingOf' U X w s τ)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V),
      X.part (Φ.toFun (typeEmbed U s τ i v)) = τ.2 i (U.part v)) :
    Tuple U X w s :=
  typeEmbeddingOfToTuple U X w s τ
    (fun b => X.part (Φ.toFun (Sum.inr b)))
    (toTypeEmbeddingOf U X w s τ Φ hwpart) hinj hπroot
    (by
      intro i v hv
      simpa [typeEmbed, hv] using hpart i v)

lemma tupleType_typeEmbeddingOfToTuple' {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (Φ : TypeEmbeddingOf' U X w s τ)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V),
      X.part (Φ.toFun (typeEmbed U s τ i v)) = τ.2 i (U.part v)) :
    tupleType U X w s
      (typeEmbeddingOfToTuple' U X w s τ Φ hwpart hinj hπroot hpart) = τ :=
  tupleType_typeEmbeddingOfToTuple U X w s τ
    (fun b => X.part (Φ.toFun (Sum.inr b)))
    (toTypeEmbeddingOf U X w s τ Φ hwpart) hinj hπroot
    (by
      intro i v hv
      simpa [typeEmbed, hv] using hpart i v)

lemma TypeEmbeddingOf'.ext' {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {s : ℕ} {τ : TypeSpace U s}
    {Φ Ψ : TypeEmbeddingOf' U X w s τ}
    (h : Φ.toFun = Ψ.toFun) : Φ = Ψ := by
  cases Φ
  cases Ψ
  simp only at h
  subst h
  rfl

end Erdos571_hypergraph
