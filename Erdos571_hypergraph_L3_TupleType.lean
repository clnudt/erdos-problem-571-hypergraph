import Erdos571_hypergraph_L3_TupleEmbedding

namespace Erdos571_hypergraph

/-- A tuple of a fixed type `τ`: the part permutation of copy `i` is `τ.2 i`,
and the induced partition is `τ.1`.  This representation avoids the
dependent `Sigma` in the old `Tuple`. -/
structure TupleOfType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) where
  emb : ∀ i : Fin s, CompatibleEmbedding U X w (τ.2 i)
  is_type :
    partitionOf U X w s (fun i => (⟨τ.2 i, emb i⟩ :
      Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)) = τ.1

noncomputable instance tupleOfTypeFintype {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s) :
    Fintype (TupleOfType U X w s τ) :=
  Fintype.ofInjective (fun t : TupleOfType U X w s τ => t.emb) (by
    intro t₁ t₂ h
    cases t₁
    cases t₂
    simp only at h
    subst h
    rfl)

/-- The old `Sigma`-valued tuple associated with a fixed-type tuple. -/
noncomputable def TupleOfType.toSigma {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (t : TupleOfType U X w s τ) : Tuple U X w s :=
  fun i => ⟨τ.2 i, t.emb i⟩

/-- The fixed-type tuple associated with an old tuple. -/
noncomputable def tupleToTupleOfType {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (φ : Tuple U X w s) :
    TupleOfType U X w s (tupleType U X w s φ) where
  emb i := (φ i).2
  is_type := rfl

/-- Extensionality for fixed-type tuples. -/
lemma TupleOfType.ext' {k : ℕ}
    {U : PartiteRootedKHypergraph k} {X : PartiteKHypergraph k}
    {w : U.R → X.V} {s : ℕ} {τ : TypeSpace U s}
    {t u : TupleOfType U X w s τ} (h : t.emb = u.emb) : t = u := by
  cases t
  cases u
  simp only at h
  subst h
  rfl

/-- The block map of a fixed-type tuple. -/
noncomputable def blockMapOfTupleOfType {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (t : TupleOfType U X w s τ) :
    {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → X.V :=
  fun b =>
    blockImage U X w s (TupleOfType.toSigma U X w s t)
      ⟨b.1, cast (congrArg
        (fun p : Partition (Interior U × Fin s) => b.1 ∈ p.blocks)
        t.is_type.symm) b.2⟩

/-- The number of tuples of a fixed type, in the type-parameterized
representation. -/
noncomputable def NτFixed {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) : ℕ :=
  Fintype.card (TupleOfType U X w s τ)

lemma tupleImage_toSigma_eq_blockImage {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (t : TupleOfType U X w s τ) (p : Interior U × Fin s) :
    tupleImage U X w s (TupleOfType.toSigma U X w s t) p =
      blockImage U X w s (TupleOfType.toSigma U X w s t)
        ⟨blockOf U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
            p.1 p.2,
          blockOf_mem U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
            p.1 p.2⟩ := by
  symm
  exact blockImage_eq U X w s (TupleOfType.toSigma U X w s t) _
    (mem_blockOf U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
      p.1 p.2)

lemma blockOf_toSigma_eq {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    {τ : TypeSpace U s} (t : TupleOfType U X w s τ)
    (p : Interior U × Fin s) :
    blockOf U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
        p.1 p.2 = (τ.1.cover p).choose := by
  classical
  let bτ := (τ.1.cover p).choose
  have hbτ_mem : bτ ∈ τ.1.blocks := ((τ.1.cover p).choose_spec).1.1
  have hp_bτ : p ∈ bτ := ((τ.1.cover p).choose_spec).1.2
  have hbτ_t : bτ ∈ (tupleType U X w s
      (TupleOfType.toSigma U X w s t)).1.blocks := by
    change bτ ∈ (partitionOf U X w s
      (fun i => (⟨τ.2 i, t.emb i⟩ :
        Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π))).blocks
    rw [t.is_type]
    exact hbτ_mem
  exact ((tupleType U X w s (TupleOfType.toSigma U X w s t)).1.cover p).unique
    ⟨blockOf_mem U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
        p.1 p.2,
      mem_blockOf U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
        p.1 p.2⟩
    ⟨hbτ_t, hp_bτ⟩

lemma blockMapOfTupleOfType_injective {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s) :
    Function.Injective (blockMapOfTupleOfType U X w s (τ := τ)) := by
  classical
  intro t u h
  apply TupleOfType.ext'
  funext i
  apply CompatibleEmbedding.ext
  funext x
  by_cases hx : x ∈ U.R
  · have ht := (t.emb i).root_compat x hx
    have hu := (u.emb i).root_compat x hx
    rw [ht, hu]
  · let p : Interior U × Fin s := (⟨x, hx⟩, i)
    let bτ : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} :=
      ⟨(τ.1.cover p).choose, ((τ.1.cover p).choose_spec).1.1⟩
    have hp_bτ : p ∈ bτ.1 := ((τ.1.cover p).choose_spec).1.2
    have hmap := congrFun h bτ
    have ht_block := blockOf_toSigma_eq U X w s t p
    have hu_block := blockOf_toSigma_eq U X w s u p
    calc
      (t.emb i).toFun x =
          tupleImage U X w s (TupleOfType.toSigma U X w s t) p := rfl
      _ = blockImage U X w s (TupleOfType.toSigma U X w s t)
            ⟨blockOf U s (tupleType U X w s
                (TupleOfType.toSigma U X w s t)) p.1 p.2,
              blockOf_mem U s (tupleType U X w s
                (TupleOfType.toSigma U X w s t)) p.1 p.2⟩ :=
          tupleImage_toSigma_eq_blockImage U X w s t p
      _ = blockMapOfTupleOfType U X w s t bτ := by
          simp [blockMapOfTupleOfType, bτ, ht_block]
      _ = blockMapOfTupleOfType U X w s u bτ := hmap
      _ = blockImage U X w s (TupleOfType.toSigma U X w s u)
            ⟨blockOf U s (tupleType U X w s
                (TupleOfType.toSigma U X w s u)) p.1 p.2,
              blockOf_mem U s (tupleType U X w s
                (TupleOfType.toSigma U X w s u)) p.1 p.2⟩ := by
          simp [blockMapOfTupleOfType, bτ, hu_block]
      _ = tupleImage U X w s (TupleOfType.toSigma U X w s u) p :=
          (tupleImage_toSigma_eq_blockImage U X w s u p).symm
      _ = (u.emb i).toFun x := rfl

/-- A type is part-consistent if all pairs in a block have the same host
part, as prescribed by the part permutations. -/
def PartConsistent {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) : Prop :=
  ∀ (b : Finset (Interior U × Fin s)), b ∈ τ.1.blocks →
    ∀ p q : Interior U × Fin s, p ∈ b → q ∈ b →
      τ.2 p.2 (U.part p.1.1) = τ.2 q.2 (U.part q.1.1)

/-- The host part of a block, assuming part consistency. -/
noncomputable def blockPartOf {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) : Fin k :=
  let p := Classical.choose (τ.1.nonempty b.1 b.2)
  τ.2 p.2 (U.part p.1.1)

lemma blockPartOf_eq {k : ℕ} (U : PartiteRootedKHypergraph k)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    blockPartOf U s τ h b = τ.2 p.2 (U.part p.1.1) := by
  classical
  unfold blockPartOf
  exact h b.1 b.2 _ p (Classical.choose_spec (τ.1.nonempty b.1 b.2)) hp

lemma blockMapOfTupleOfType_part {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (t : TupleOfType U X w s τ) (h : PartConsistent U s τ)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    X.part (blockMapOfTupleOfType U X w s (τ := τ) t b) =
      blockPartOf U s τ h b := by
  classical
  obtain ⟨p, hp⟩ := τ.1.nonempty b.1 b.2
  have hmap : blockMapOfTupleOfType U X w s (τ := τ) t b =
      tupleImage U X w s (TupleOfType.toSigma U X w s t) p := by
    unfold blockMapOfTupleOfType
    rw [blockImage_eq U X w s (TupleOfType.toSigma U X w s t) _ hp]
  rw [hmap]
  change X.part ((t.emb p.2).toFun p.1.1) = blockPartOf U s τ h b
  rw [blockPartOf_eq U s τ h b hp]
  exact (t.emb p.2).part_compat p.1.1

/-- Block maps that respect the host part of each block. -/
abbrev PartRespectingBlockMaps {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) (h : PartConsistent U s τ) :=
  {β : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} → X.V //
    ∀ b, X.part (β b) = blockPartOf U s τ h b}

/-- A tuple gives a part-respecting block map. -/
noncomputable def tupleToPartRespectingBlockMap {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (h : PartConsistent U s τ) (t : TupleOfType U X w s τ) :
    PartRespectingBlockMaps U X w s τ h :=
  ⟨blockMapOfTupleOfType U X w s (τ := τ) t,
    blockMapOfTupleOfType_part U X w s t h⟩

lemma tupleToPartRespectingBlockMap_injective {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) {τ : TypeSpace U s}
    (h : PartConsistent U s τ) :
    Function.Injective (tupleToPartRespectingBlockMap U X w s h) := by
  intro t u htu
  apply blockMapOfTupleOfType_injective U X w s τ
  exact congrArg Subtype.val htu

lemma NτFixed_le_card_blockMaps {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    NτFixed U X w s τ ≤
      Fintype.card (PartRespectingBlockMaps U X w s τ h) := by
  classical
  rw [NτFixed]
  exact Fintype.card_le_of_injective _
    (tupleToPartRespectingBlockMap_injective U X w s h)

/-- Part-respecting block maps are equivalently dependent choices of a
vertex in the prescribed part of each block. -/
noncomputable def partRespectingEquiv {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    PartRespectingBlockMaps U X w s τ h ≃
      ((b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) →
        {v : X.V // X.part v = blockPartOf U s τ h b}) where
  toFun β b := ⟨β.1 b, β.2 b⟩
  invFun f := ⟨fun b => (f b).1, fun b => (f b).2⟩
  left_inv β := by
    cases β
    rfl
  right_inv f := by
    funext b
    exact Subtype.ext rfl

lemma card_partRespectingBlockMaps {k : ℕ} {F : Type} [Fintype F]
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) (b : ℕ)
    (hpart_card : ∀ i : Fin k,
      Fintype.card {v : X.V // X.part v = i} = Fintype.card F ^ b) :
    Fintype.card (PartRespectingBlockMaps U X w s τ h) =
      Fintype.card F ^ (b * hτ U s τ) := by
  classical
  rw [Fintype.card_congr (partRespectingEquiv U X w s τ h),
    Fintype.card_pi]
  simp only [hpart_card]
  rw [Finset.prod_const, Finset.card_univ, hτ, ← pow_mul]
  simp

/-- The number of tuples of a fixed type is at most the number of
part-respecting block maps, hence at most `q^(b * hτ)`. -/
lemma NτFixed_le {k : ℕ} {F : Type} [Fintype F]
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) (b : ℕ)
    (hpart_card : ∀ i : Fin k,
      Fintype.card {v : X.V // X.part v = i} = Fintype.card F ^ b) :
    NτFixed U X w s τ ≤ Fintype.card F ^ (b * hτ U s τ) := by
  rw [← card_partRespectingBlockMaps U X w s τ h b hpart_card]
  exact NτFixed_le_card_blockMaps U X w s τ h

end Erdos571_hypergraph
