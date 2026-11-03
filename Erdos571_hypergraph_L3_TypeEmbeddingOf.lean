import Erdos571_hypergraph_L3_TupleEmbedding

namespace Erdos571_hypergraph

/-- The part of a vertex of `H_τ`, given an explicit part function on blocks. -/
noncomputable def typeVertexPartOf {k : ℕ} {U : PartiteRootedKHypergraph k}
    {s : ℕ} (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k) :
    TypeVertex U τ → Fin k
  | Sum.inl r => U.part r.1
  | Sum.inr b => partOf b

/-- A type embedding parameterized by the type `τ` and an explicit part
function, rather than by a tuple. -/
structure TypeEmbeddingOf {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k) where
  toFun : TypeVertex U τ → X.V
  inj : Function.Injective toFun
  root_compat : ∀ r : U.R, toFun (Sum.inl r) = w r
  part_compat : ∀ v : TypeVertex U τ,
    X.part (toFun v) = typeVertexPartOf τ partOf v
  edge_mem : ∀ (i : Fin s) {e : Finset U.V}, e ∈ U.G.edges →
    (typeEdgeSet U s τ i e).image toFun ∈ X.G.edges

/-- The type-parameterized embedding induced by a tuple. -/
noncomputable def tupleToTypeEmbeddingOf {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hw : Function.Injective w)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) :
    TypeEmbeddingOf U X w s (tupleType U X w s φ)
      (fun b => blockPart U X w s φ b) where
  toFun := tupleToEmbedding U X w s φ
  inj := tupleToEmbedding_injective U X w hw s φ
  root_compat := by
    intro r
    rfl
  part_compat := by
    intro v
    cases v with
    | inl r =>
        simp [tupleToEmbedding, typeVertexPartOf, hwpart r]
    | inr b =>
        obtain ⟨p, hp⟩ := (tupleType U X w s φ).1.nonempty b.1 b.2
        change X.part (blockImage U X w s φ b) = blockPart U X w s φ b
        rw [blockImage_eq U X w s φ b hp]
        rw [blockPart_eq U X w s φ b hp]
        exact (φ p.2).2.part_compat p.1.1
  edge_mem := by
    intro i e he
    exact tupleToEmbedding_edge_mem U X w s φ i he

/-- The preimage of a block under `blockOf`. -/
noncomputable def preimageBlock {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    Finset (Interior U × Fin s) := by
  classical
  exact Finset.univ.filter (fun p => blockOf U s τ p.1 p.2 = b.1)

lemma blockOf_eq_of_mem {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    blockOf U s τ p.1 p.2 = b.1 := by
  exact (τ.1.cover p).unique
    ⟨blockOf_mem U s τ p.1 p.2, mem_blockOf U s τ p.1 p.2⟩
    ⟨b.2, hp⟩

lemma preimageBlock_eq_self {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    preimageBlock U s τ b = b.1 := by
  classical
  ext p
  simp only [preimageBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rw [← h]
    exact mem_blockOf U s τ p.1 p.2
  · intro hp
    exact blockOf_eq_of_mem U s τ b hp

lemma typeEmbed_eq_inr_of_mem' {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    typeEmbed U s τ p.2 p.1.1 = Sum.inr b := by
  classical
  have hb : blockOf U s τ p.1 p.2 = b.1 :=
    blockOf_eq_of_mem U s τ b hp
  have hsub : (⟨blockOf U s τ p.1 p.2,
      blockOf_mem U s τ p.1 p.2⟩ :
        {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) = b :=
    Subtype.ext hb
  simp [typeEmbed, p.1.2, hsub]

/-- The tuple induced by a type-parameterized embedding. -/
noncomputable def typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v)) :
    Tuple U X w s :=
  fun i =>
    ⟨τ.2 i,
      { toFun := fun v => Φ.toFun (typeEmbed U s τ i v)
        inj := Φ.inj.comp (hinj i)
        root_compat := by
          intro r hr
          simp [typeEmbed, hr, Φ.root_compat]
        edge_map := by
          intro e he
          have h := Φ.edge_mem i he
          rw [typeEdgeSet, Finset.image_image] at h
          rw [Finset.map_eq_image]
          simpa [Function.comp_def] using h
        part_compat := by
          intro v
          rw [Φ.part_compat]
          by_cases hv : v ∈ U.R
          · simp [typeVertexPartOf, typeEmbed, hv, hπroot i ⟨v, hv⟩]
          · have hte : typeEmbed U s τ i v =
                Sum.inr ⟨blockOf U s τ ⟨v, hv⟩ i,
                  blockOf_mem U s τ ⟨v, hv⟩ i⟩ := by
              simp [typeEmbed, hv]
            rw [hte]
            simp only [typeVertexPartOf]
            rw [hpart i v hv] }⟩

lemma tupleType_snd_typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v)) :
    (fun i : Fin s =>
      ((typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart) i).1) = τ.2 := by
  rfl

lemma tupleImage_typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v))
    (p : Interior U × Fin s) :
    tupleImage U X w s
      (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart) p =
      Φ.toFun (typeEmbed U s τ p.2 p.1.1) := by
  rfl

lemma block_typeEmbeddingOfToTuple_eq {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v))
    (p : Interior U × Fin s) :
    block U X w s
        (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart) p =
      preimageBlock U s τ
        ⟨blockOf U s τ p.1 p.2,
          blockOf_mem U s τ p.1 p.2⟩ := by
  classical
  ext q
  rw [mem_block_iff, preimageBlock]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [tupleImage_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart q,
    tupleImage_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart p]
  rw [Φ.inj.eq_iff]
  simp [typeEmbed, q.1.2, p.1.2]

lemma blocks_typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v)) :
    (partitionOf U X w s
      (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)).blocks =
      τ.1.blocks := by
  classical
  ext b
  constructor
  · intro hb
    rcases Finset.mem_image.mp hb with ⟨p, -, hpb⟩
    rw [← hpb]
    rw [block_typeEmbeddingOfToTuple_eq U X w s τ partOf Φ hinj hπroot hpart p]
    rw [preimageBlock_eq_self]
    exact blockOf_mem U s τ p.1 p.2
  · intro hb
    obtain ⟨p, hp⟩ := τ.1.nonempty b hb
    refine Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
    rw [block_typeEmbeddingOfToTuple_eq U X w s τ partOf Φ hinj hπroot hpart p]
    rw [preimageBlock_eq_self]
    exact blockOf_eq_of_mem U s τ ⟨b, hb⟩ hp

lemma partitionOf_typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v)) :
    partitionOf U X w s
      (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart) = τ.1 :=
  Partition.ext
    (blocks_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)

lemma tupleType_typeEmbeddingOfToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v)) :
    tupleType U X w s
      (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart) = τ := by
  dsimp [tupleType]
  exact Prod.ext
    (partitionOf_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)
    (tupleType_snd_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)

lemma blockPart_typeEmbeddingOfToTuple_eq_partOf {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (partOf : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → Fin k)
    (Φ : TypeEmbeddingOf U X w s τ partOf)
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hπroot : ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1)
    (hpart : ∀ (i : Fin s) (v : U.V) (hv : v ∉ U.R),
      partOf ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩ = τ.2 i (U.part v))
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    blockPart U X w s
      (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)
      ⟨b.1, by
        change b.1 ∈ (partitionOf U X w s
          (typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart)).blocks
        rw [partitionOf_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart]
        exact b.2⟩ = partOf b := by
  classical
  let ψ := typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart
  let b' : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s ψ).1.blocks} :=
    ⟨b.1, by
      change b.1 ∈ (partitionOf U X w s ψ).blocks
      rw [partitionOf_typeEmbeddingOfToTuple U X w s τ partOf Φ hinj hπroot hpart]
      exact b.2⟩
  change blockPart U X w s ψ b' = partOf b
  obtain ⟨p, hp⟩ := τ.1.nonempty b.1 b.2
  rw [blockPart_eq U X w s ψ b' (by simpa [b', tupleType] using hp)]
  have hto : (ψ p.2).2.toFun p.1.1 =
      Φ.toFun (typeEmbed U s τ p.2 p.1.1) := rfl
  rw [show (ψ p.2).1 (U.part p.1.1) =
      X.part ((ψ p.2).2.toFun p.1.1) from ((ψ p.2).2.part_compat p.1.1).symm]
  rw [hto, typeEmbed_eq_inr_of_mem' U s τ b hp]
  simpa [typeVertexPartOf] using Φ.part_compat (Sum.inr b)

end Erdos571_hypergraph
