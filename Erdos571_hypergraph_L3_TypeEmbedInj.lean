import Erdos571_hypergraph_L3_TypeTransport
import Erdos571_hypergraph_L3_TypeGood

namespace Erdos571_hypergraph

lemma typeEmbed_injective_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (t : TupleOfType U X w s τ) (i : Fin s) :
    Function.Injective (typeEmbed U s τ i) := by
  classical
  intro x y h
  by_cases hx : x ∈ U.R
  · by_cases hy : y ∈ U.R
    · have hxte : typeEmbed U s τ i x = Sum.inl ⟨x, hx⟩ := by
        simp [typeEmbed, hx]
      have hyte : typeEmbed U s τ i y = Sum.inl ⟨y, hy⟩ := by
        simp [typeEmbed, hy]
      rw [hxte, hyte] at h
      injection h with hsub
      exact congrArg Subtype.val hsub
    · have hxte : typeEmbed U s τ i x = Sum.inl ⟨x, hx⟩ := by
        simp [typeEmbed, hx]
      have hyte : typeEmbed U s τ i y =
          Sum.inr ⟨blockOf U s τ ⟨y, hy⟩ i,
            blockOf_mem U s τ ⟨y, hy⟩ i⟩ := by
        simp [typeEmbed, hy]
      rw [hxte, hyte] at h
      simp at h
  · by_cases hy : y ∈ U.R
    · have hxte : typeEmbed U s τ i x =
          Sum.inr ⟨blockOf U s τ ⟨x, hx⟩ i,
            blockOf_mem U s τ ⟨x, hx⟩ i⟩ := by
        simp [typeEmbed, hx]
      have hyte : typeEmbed U s τ i y = Sum.inl ⟨y, hy⟩ := by
        simp [typeEmbed, hy]
      rw [hxte, hyte] at h
      simp at h
    · have hxte : typeEmbed U s τ i x =
          Sum.inr ⟨blockOf U s τ ⟨x, hx⟩ i,
            blockOf_mem U s τ ⟨x, hx⟩ i⟩ := by
        simp [typeEmbed, hx]
      have hyte : typeEmbed U s τ i y =
          Sum.inr ⟨blockOf U s τ ⟨y, hy⟩ i,
            blockOf_mem U s τ ⟨y, hy⟩ i⟩ := by
        simp [typeEmbed, hy]
      rw [hxte, hyte] at h
      injection h with hblockSub
      have hblock : blockOf U s τ ⟨x, hx⟩ i =
          blockOf U s τ ⟨y, hy⟩ i := congrArg Subtype.val hblockSub
      have hx_mem : (⟨x, hx⟩, i) ∈ blockOf U s τ ⟨y, hy⟩ i := by
        rw [← hblock]
        exact mem_blockOf U s τ ⟨x, hx⟩ i
      have hy_mem : (⟨y, hy⟩, i) ∈ blockOf U s τ ⟨y, hy⟩ i :=
        mem_blockOf U s τ ⟨y, hy⟩ i
      have hbo : blockOf U s τ ⟨y, hy⟩ i =
          blockOf U s (tupleType U X w s (TupleOfType.toSigma U X w s t))
            ⟨y, hy⟩ i :=
        blockOf_eq_of_partition_eq U t.is_type.symm ⟨y, hy⟩ i
      have htupleBlock : blockOf U s τ ⟨y, hy⟩ i =
          block U X w s (TupleOfType.toSigma U X w s t) (⟨y, hy⟩, i) := by
        rw [hbo]
        simpa [tupleType, TupleOfType.toSigma] using
          (blockOf_partitionOf U X w s
            (TupleOfType.toSigma U X w s t) ⟨y, hy⟩ i)
      have hx_tuple : (⟨x, hx⟩, i) ∈
          block U X w s (TupleOfType.toSigma U X w s t) (⟨y, hy⟩, i) := by
        rw [← htupleBlock]
        exact hx_mem
      have himg : tupleImage U X w s (TupleOfType.toSigma U X w s t) (⟨x, hx⟩, i) =
          tupleImage U X w s (TupleOfType.toSigma U X w s t) (⟨y, hy⟩, i) :=
        (mem_block_iff U X w s (TupleOfType.toSigma U X w s t)
          (⟨y, hy⟩, i) (⟨x, hx⟩, i)).mp hx_tuple
      have hxy : (t.emb i).toFun x = (t.emb i).toFun y := by
        simpa [tupleImage, TupleOfType.toSigma] using himg
      exact (t.emb i).inj hxy

lemma blockOf_injective_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (t : TupleOfType U X w s τ) (i : Fin s) :
    Function.Injective (fun x : Interior U => blockOf U s τ x i) := by
  classical
  intro x y h
  have hx : typeEmbed U s τ i x.1 =
      Sum.inr ⟨blockOf U s τ x i, blockOf_mem U s τ x i⟩ := by
    simp [typeEmbed, x.2]
  have hy : typeEmbed U s τ i y.1 =
      Sum.inr ⟨blockOf U s τ y i, blockOf_mem U s τ y i⟩ := by
    simp [typeEmbed, y.2]
  have hte : typeEmbed U s τ i x.1 = typeEmbed U s τ i y.1 := by
    rw [hx, hy]
    have hsub : (⟨blockOf U s τ x i, blockOf_mem U s τ x i⟩ :
        {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) =
        ⟨blockOf U s τ y i, blockOf_mem U s τ y i⟩ :=
      Subtype.ext h
    exact congrArg Sum.inr hsub
  have hxy : x.1 = y.1 :=
    typeEmbed_injective_of_tuple U X w s τ t i hte
  exact Subtype.ext hxy

lemma typeAdmissible_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (t : TupleOfType U X w s τ) :
    TypeAdmissible U s τ := by
  intro i e he x y hx hy hxy hEq
  exact hxy (typeEmbed_injective_of_tuple U X w s τ t i hEq)

lemma partConsistent_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (s : ℕ) (τ : TypeSpace U s)
    (t : TupleOfType U X w s τ) :
    PartConsistent U s τ := by
  intro b hb p q hp hq
  have hb' : b ∈ (tupleType U X w s
      (TupleOfType.toSigma U X w s t)).1.blocks := by
    change b ∈ (partitionOf U X w s
      (fun i => (⟨τ.2 i, t.emb i⟩ :
        Σ π : Equiv.Perm (Fin k),
          CompatibleEmbedding U X w π))).blocks
    rw [t.is_type]
    exact hb
  have h := partConsistent_tupleType U X w s
    (TupleOfType.toSigma U X w s t) b hb' p q hp hq
  change (τ.2 p.2) (U.part p.1.1) =
    (τ.2 q.2) (U.part q.1.1)
  exact h

lemma rootFixed_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1)
    (s : ℕ) (τ : TypeSpace U s) (t : TupleOfType U X w s τ) :
    RootFixed U s τ := by
  intro i r
  have h := rootFixed_tupleType U X w hwpart s
    (TupleOfType.toSigma U X w s t) i r
  simpa [RootFixed, tupleType, TupleOfType.toSigma] using h

end Erdos571_hypergraph
