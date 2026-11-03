import Erdos571_hypergraph_L3_TypeGraph

namespace Erdos571_hypergraph

/-- The type of a tuple: its induced partition and part permutations. -/
noncomputable def tupleType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) : TypeSpace U s :=
  (partitionOf U X w s φ, fun i => (φ i).1)

lemma tupleImage_eq_of_mem_same_block {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s)
    {b : Finset (Interior U × Fin s)}
    (hb : b ∈ (partitionOf U X w s φ).blocks)
    {p q : Interior U × Fin s} (hp : p ∈ b) (hq : q ∈ b) :
    tupleImage U X w s φ p = tupleImage U X w s φ q := by
  classical
  rcases Finset.mem_image.mp hb with ⟨r, -, rfl⟩
  exact ((mem_block_iff U X w s φ r p).mp hp).trans
    ((mem_block_iff U X w s φ r q).mp hq).symm

/-- The image in `X` of a block of the partition induced by a tuple. -/
noncomputable def blockImage {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks}) :
    X.V := by
  classical
  exact tupleImage U X w s φ
    (Classical.choose ((tupleType U X w s φ).1.nonempty b.1 b.2))

lemma blockImage_eq {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    blockImage U X w s φ b = tupleImage U X w s φ p := by
  classical
  unfold blockImage
  exact tupleImage_eq_of_mem_same_block U X w s φ b.2
    (Classical.choose_spec _) hp

/-- The part of a block of the partition induced by a tuple. -/
noncomputable def blockPart {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks}) :
    Fin k := by
  classical
  let p := Classical.choose ((tupleType U X w s φ).1.nonempty b.1 b.2)
  exact (φ p.2).1 (U.part p.1.1)

lemma blockPart_eq {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    blockPart U X w s φ b = (φ p.2).1 (U.part p.1.1) := by
  classical
  unfold blockPart
  let q := Classical.choose ((tupleType U X w s φ).1.nonempty b.1 b.2)
  have hq : q ∈ b.1 := Classical.choose_spec _
  have himg : tupleImage U X w s φ q = tupleImage U X w s φ p :=
    tupleImage_eq_of_mem_same_block U X w s φ b.2 hq hp
  calc
    (φ q.2).1 (U.part q.1.1) = X.part ((φ q.2).2.toFun q.1.1) :=
      ((φ q.2).2.part_compat q.1.1).symm
    _ = X.part ((φ p.2).2.toFun p.1.1) := by
      simpa [tupleImage] using congrArg X.part himg
    _ = (φ p.2).1 (U.part p.1.1) := (φ p.2).2.part_compat p.1.1

/-- The embedding of `H_τ` into `X` induced by a tuple of type `τ`. -/
noncomputable def tupleToEmbedding {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    TypeVertex U (tupleType U X w s φ) → X.V
  | Sum.inl r => w r
  | Sum.inr b => blockImage U X w s φ b

lemma tupleToEmbedding_typeEmbed {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (i : Fin s) (v : U.V) :
    tupleToEmbedding U X w s φ (typeEmbed U s (tupleType U X w s φ) i v) =
      (φ i).2.toFun v := by
  classical
  by_cases hv : v ∈ U.R
  · simp [tupleToEmbedding, typeEmbed, hv, (φ i).2.root_compat v hv]
  · have hte : typeEmbed U s (tupleType U X w s φ) i v =
        Sum.inr ⟨blockOf U s (tupleType U X w s φ) ⟨v, hv⟩ i,
          blockOf_mem U s (tupleType U X w s φ) ⟨v, hv⟩ i⟩ := by
      simp [typeEmbed, hv]
    rw [hte]
    simp only [tupleToEmbedding]
    rw [blockImage_eq U X w s φ _
      (p := (⟨v, hv⟩, i))
      (mem_blockOf U s (tupleType U X w s φ) ⟨v, hv⟩ i)]
    simp [tupleImage]

/-- The part of a vertex of `H_τ`. -/
noncomputable def typeVertexPart {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) : TypeVertex U (tupleType U X w s φ) → Fin k
  | Sum.inl r => U.part r.1
  | Sum.inr b => blockPart U X w s φ b

lemma typeVertexPart_typeEmbed {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) (i : Fin s) (v : U.V) :
    typeVertexPart U X w s φ (typeEmbed U s (tupleType U X w s φ) i v) =
      (φ i).1 (U.part v) := by
  classical
  by_cases hv : v ∈ U.R
  · have hroot : (φ i).1 (U.part v) = U.part v := by
      rw [← (φ i).2.part_compat v, (φ i).2.root_compat v hv,
        hwpart ⟨v, hv⟩]
    simp [typeVertexPart, typeEmbed, hv, hroot]
  · have hte : typeEmbed U s (tupleType U X w s φ) i v =
        Sum.inr ⟨blockOf U s (tupleType U X w s φ) ⟨v, hv⟩ i,
          blockOf_mem U s (tupleType U X w s φ) ⟨v, hv⟩ i⟩ := by
      simp [typeEmbed, hv]
    rw [hte]
    simp only [typeVertexPart]
    rw [blockPart_eq U X w s φ _
      (mem_blockOf U s (tupleType U X w s φ) ⟨v, hv⟩ i)]

lemma typeEmbed_injective_tupleType {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s) (i : Fin s) :
    Function.Injective (typeEmbed U s (tupleType U X w s φ) i) := by
  classical
  intro x y h
  by_cases hx : x ∈ U.R <;> by_cases hy : y ∈ U.R
  · simp [typeEmbed, hx, hy] at h
    exact h
  · simp [typeEmbed, hx, hy] at h
  · simp [typeEmbed, hx, hy] at h
  · simp only [typeEmbed, hx, hy] at h
    have hblock : blockOf U s (tupleType U X w s φ) ⟨x, hx⟩ i =
        blockOf U s (tupleType U X w s φ) ⟨y, hy⟩ i :=
      Subtype.ext_iff.mp (Sum.inr.inj h)
    simp only [tupleType] at hblock
    rw [blockOf_partitionOf] at hblock
    rw [blockOf_partitionOf] at hblock
    have himg : tupleImage U X w s φ (⟨x, hx⟩, i) =
        tupleImage U X w s φ (⟨y, hy⟩, i) := by
      have hxmem : (⟨x, hx⟩, i) ∈ block U X w s φ (⟨y, hy⟩, i) := by
        rw [← hblock]
        exact (mem_block_iff U X w s φ (⟨x, hx⟩, i) (⟨x, hx⟩, i)).mpr rfl
      exact (mem_block_iff U X w s φ (⟨y, hy⟩, i) (⟨x, hx⟩, i)).mp hxmem
    exact (φ i).2.inj himg

lemma blockImage_injective {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    Function.Injective (blockImage U X w s φ) := by
  classical
  intro b c h
  apply Subtype.ext
  obtain ⟨p, hp⟩ := (tupleType U X w s φ).1.nonempty b.1 b.2
  obtain ⟨q, hq⟩ := (tupleType U X w s φ).1.nonempty c.1 c.2
  have hb := blockImage_eq U X w s φ b hp
  have hc := blockImage_eq U X w s φ c hq
  have hpq : tupleImage U X w s φ p = tupleImage U X w s φ q := by
    rw [← hb, ← hc]
    exact h
  rcases Finset.mem_image.mp b.2 with ⟨r, -, hbr⟩
  rcases Finset.mem_image.mp c.2 with ⟨s₀, -, hcs⟩
  have hpb : p ∈ block U X w s φ r := by
    rwa [← hbr] at hp
  have hqc : q ∈ block U X w s φ s₀ := by
    rwa [← hcs] at hq
  have hqp : q ∈ block U X w s φ p :=
    (mem_block_iff U X w s φ p q).mpr hpq.symm
  have hbp : block U X w s φ p = block U X w s φ r :=
    block_eq_of_mem U X w s φ hpb
  have hbq : block U X w s φ q = block U X w s φ s₀ :=
    block_eq_of_mem U X w s φ hqc
  have hpqblock : block U X w s φ q = block U X w s φ p :=
    block_eq_of_mem U X w s φ hqp
  calc
    b.1 = block U X w s φ r := hbr.symm
    _ = block U X w s φ p := hbp.symm
    _ = block U X w s φ q := hpqblock.symm
    _ = block U X w s φ s₀ := hbq
    _ = c.1 := hcs

lemma tupleToEmbedding_injective {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hw : Function.Injective w) (s : ℕ) (φ : Tuple U X w s) :
    Function.Injective (tupleToEmbedding U X w s φ) := by
  classical
  intro x y h
  rcases x with r | b
  · rcases y with s₀ | c
    · simp only [tupleToEmbedding] at h
      exact congrArg Sum.inl (hw h)
    · simp only [tupleToEmbedding] at h
      exfalso
      obtain ⟨p, hp⟩ := (tupleType U X w s φ).1.nonempty c.1 c.2
      rcases p with ⟨z, i⟩
      have hb := blockImage_eq U X w s φ c hp
      have hx : z.1 = r.1 := (φ i).2.inj (by
        calc
          (φ i).2.toFun z.1 = w r := (h.trans hb).symm
          _ = (φ i).2.toFun r.1 := ((φ i).2.root_compat r.1 r.2).symm)
      exact z.2 (hx ▸ r.2)
  · rcases y with s₀ | c
    · simp only [tupleToEmbedding] at h
      exfalso
      obtain ⟨p, hp⟩ := (tupleType U X w s φ).1.nonempty b.1 b.2
      rcases p with ⟨z, i⟩
      have hb := blockImage_eq U X w s φ b hp
      have hx : z.1 = s₀.1 := (φ i).2.inj (by
        calc
          (φ i).2.toFun z.1 = w s₀ := hb.symm.trans h
          _ = (φ i).2.toFun s₀.1 := ((φ i).2.root_compat s₀.1 s₀.2).symm)
      exact z.2 (hx ▸ s₀.2)
    · simp only [tupleToEmbedding] at h
      exact congrArg Sum.inr (blockImage_injective U X w s φ h)

lemma tupleToEmbedding_typeEdgeSet {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s)
    (i : Fin s) (e : Finset U.V) :
    (typeEdgeSet U s (tupleType U X w s φ) i e).image
        (tupleToEmbedding U X w s φ) =
      e.map ⟨(φ i).2.toFun, (φ i).2.inj⟩ := by
  classical
  rw [typeEdgeSet, Finset.image_image, Finset.map_eq_image]
  apply Finset.image_congr
  intro v _
  exact tupleToEmbedding_typeEmbed U X w s φ i v

lemma tupleToEmbedding_edge_mem {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    (typeEdgeSet U s (tupleType U X w s φ) i e).image
        (tupleToEmbedding U X w s φ) ∈ X.G.edges := by
  rw [tupleToEmbedding_typeEdgeSet U X w s φ i e]
  exact (φ i).2.edge_map e he

/-- An embedding of the type graph `H_τ` into `X`, with part compatibility. -/
structure TypeEmbedding {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) where
  toFun : TypeVertex U (tupleType U X w s φ) → X.V
  inj : Function.Injective toFun
  root_compat : ∀ r : U.R, toFun (Sum.inl r) = w r
  part_compat : ∀ v : TypeVertex U (tupleType U X w s φ),
    X.part (toFun v) = typeVertexPart U X w s φ v
  edge_mem : ∀ (i : Fin s) {e : Finset U.V}, e ∈ U.G.edges →
    (typeEdgeSet U s (tupleType U X w s φ) i e).image toFun ∈ X.G.edges

lemma TypeEmbedding.ext' {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {s : ℕ} {φ : Tuple U X w s}
    {Φ Ψ : TypeEmbedding U X w s φ} (h : Φ.toFun = Ψ.toFun) : Φ = Ψ := by
  cases Φ
  cases Ψ
  simp only at h
  subst h
  rfl

lemma typeEmbed_eq_inr_of_mem {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ (tupleType U X w s φ).1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    typeEmbed U s (tupleType U X w s φ) p.2 p.1.1 = Sum.inr b := by
  classical
  have hb_eq : (⟨blockOf U s (tupleType U X w s φ) p.1 p.2,
      blockOf_mem U s (tupleType U X w s φ) p.1 p.2⟩ :
        {b : Finset (Interior U × Fin s) //
          b ∈ (tupleType U X w s φ).1.blocks}) = b := by
    apply Subtype.ext
    simp only [tupleType]
    rw [blockOf_partitionOf]
    rcases Finset.mem_image.mp b.2 with ⟨r, -, hbr⟩
    have hpr : p ∈ block U X w s φ r := by
      rwa [← hbr] at hp
    rw [block_eq_of_mem U X w s φ hpr, hbr]
  simp [typeEmbed, p.1.2, hb_eq]

/-- The type embedding induced by a tuple. -/
noncomputable def tupleToTypeEmbedding {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hw : Function.Injective w)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) : TypeEmbedding U X w s φ where
  toFun := tupleToEmbedding U X w s φ
  inj := tupleToEmbedding_injective U X w hw s φ
  root_compat := by
    intro r
    rfl
  part_compat := by
    intro v
    cases v with
    | inl r =>
        simp [tupleToEmbedding, typeVertexPart, hwpart r]
    | inr b =>
        obtain ⟨p, hp⟩ := (tupleType U X w s φ).1.nonempty b.1 b.2
        rw [show (tupleToEmbedding U X w s φ) (Sum.inr b) =
            blockImage U X w s φ b from rfl]
        rw [blockImage_eq U X w s φ b hp]
        rw [show typeVertexPart U X w s φ (Sum.inr b) =
            blockPart U X w s φ b from rfl]
        rw [blockPart_eq U X w s φ b hp]
        exact (φ p.2).2.part_compat p.1.1
  edge_mem := by
    intro i e he
    exact tupleToEmbedding_edge_mem U X w s φ i he

/-- The tuple induced by an embedding of `H_τ`, for `τ` the type of `φ`. -/
noncomputable def typeEmbeddingToTuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) (Φ : TypeEmbedding U X w s φ) :
    Tuple U X w s :=
  fun i =>
    ⟨(tupleType U X w s φ).2 i,
      { toFun := fun v => Φ.toFun (typeEmbed U s (tupleType U X w s φ) i v)
        inj := Φ.inj.comp (typeEmbed_injective_tupleType U X w s φ i)
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
          exact typeVertexPart_typeEmbed U X w hwpart s φ i v }⟩

lemma typeEmbeddingToTuple_tupleToTypeEmbedding {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hw : Function.Injective w)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) :
    typeEmbeddingToTuple U X w hwpart s φ
      (tupleToTypeEmbedding U X w hw hwpart s φ) = φ := by
  classical
  funext i
  apply Sigma.ext
  · dsimp [typeEmbeddingToTuple, tupleType]
  · apply heq_of_eq
    apply CompatibleEmbedding.ext
    funext v
    exact tupleToEmbedding_typeEmbed U X w s φ i v

end Erdos571_hypergraph
