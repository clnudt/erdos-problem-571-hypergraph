import Erdos571_hypergraph_L3_TypeEmbeddingSimple

namespace Erdos571_hypergraph

/-- The map from the blocks of the type of a tuple to their images in `X`.
This is the object counted in the expectation bound: a tuple of type `τ` is
determined by this map. -/
noncomputable def blockMapOfTuple {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks} →
      X.V :=
  fun b => blockImage U X w s φ b

lemma tupleImage_eq_blockImage {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (p : Interior U × Fin s) :
    tupleImage U X w s φ p =
      blockImage U X w s φ
        ⟨blockOf U s (tupleType U X w s φ) p.1 p.2,
          blockOf_mem U s (tupleType U X w s φ) p.1 p.2⟩ := by
  symm
  exact blockImage_eq U X w s φ _
    (mem_blockOf U s (tupleType U X w s φ) p.1 p.2)

/-- Tuples of a fixed type `τ`. -/
abbrev TupleOfType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) :=
  {φ : Tuple U X w s // tupleType U X w s φ = τ}

/-- The block map of a tuple of a fixed type. -/
noncomputable def blockMapOfType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) (φ : TupleOfType U X w s τ) :
    {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → X.V :=
  fun b =>
    blockImage U X w s φ.1
      ⟨b.1, φ.2.symm ▸ b.2⟩

end Erdos571_hypergraph
