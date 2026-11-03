import Erdos571_hypergraph_L2_Multivariate

namespace Erdos571_hypergraph

lemma card_badUnion_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z) (_hm : 2 ≤ m) (hn : 0 < n) :
    (Finset.univ.filter (fun ℓ : (Fin n → F) →ₗ[F] F =>
        ¬ Function.Injective (fun i : Fin m => ℓ (z i)))).card
      ≤ m.choose 2 * Fintype.card F ^ (n - 1) := by
  classical
  let pairs : Finset (Fin m × Fin m) :=
    ((Finset.univ : Finset (Fin m)).product Finset.univ).filter
      (fun p => p.1 < p.2)
  let bad : Finset ((Fin n → F) →ₗ[F] F) :=
    Finset.univ.filter (fun ℓ => ¬ Function.Injective (fun i : Fin m => ℓ (z i)))
  let badOf : Fin m × Fin m → Finset ((Fin n → F) →ₗ[F] F) :=
    fun p => Finset.univ.filter (fun ℓ => ℓ ∈ badPair z p.1 p.2)
  have hsub : bad ⊆ pairs.biUnion badOf := by
    intro ℓ hℓ
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    rw [Function.Injective] at hℓ
    push_neg at hℓ
    rcases hℓ with ⟨i, j, hij, heq⟩
    rcases lt_or_gt_of_ne heq with hlt | hlt
    · refine Finset.mem_biUnion.mpr ⟨(i, j), ?_, ?_⟩
      · simpa [pairs] using hlt
      · simp [badOf, badPair, evalAt, sub_eq_zero]
        exact hij
    · refine Finset.mem_biUnion.mpr ⟨(j, i), ?_, ?_⟩
      · simpa [pairs] using hlt
      · simp [badOf, badPair, evalAt, sub_eq_zero]
        exact hij.symm
  calc
    bad.card ≤ (pairs.biUnion badOf).card := Finset.card_le_card hsub
    _ ≤ ∑ p ∈ pairs, (badOf p).card := Finset.card_biUnion_le
    _ ≤ ∑ p ∈ pairs, Fintype.card F ^ (n - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hlt : p.1 < p.2 := by simpa [pairs] using hp
      have hne : z p.1 ≠ z p.2 := by
        intro h
        exact (ne_of_lt hlt) (hz h)
      have hcard : (badOf p).card = Nat.card (badPair z p.1 p.2) := by
        simp [badOf, Nat.card_eq_fintype_card, Fintype.card_subtype]
      rw [hcard]
      exact card_badPair_le hne hn
    _ = pairs.card * Fintype.card F ^ (n - 1) := by
      rw [Finset.sum_const, smul_eq_mul]
    _ = m.choose 2 * Fintype.card F ^ (n - 1) := by
      rw [card_pairs]

lemma exists_separating_linear_of_bounds
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hm : 2 ≤ m) (hn : 0 < n) :
    ∃ ℓ : (Fin n → F) →ₗ[F] F,
      Function.Injective (fun i : Fin m => ℓ (z i)) := by
  classical
  let D := (Fin n → F) →ₗ[F] F
  let bad : Finset D :=
    Finset.univ.filter (fun ℓ => ¬ Function.Injective (fun i : Fin m => ℓ (z i)))
  have hle : bad.card ≤ m.choose 2 * Fintype.card F ^ (n - 1) := by
    simpa [bad, D] using card_badUnion_le z hz hm hn
  have hqpos : 0 < Fintype.card F := Fintype.card_pos
  have hpowpos : 0 < Fintype.card F ^ (n - 1) := pow_pos hqpos _
  have hlt1 : m.choose 2 * Fintype.card F ^ (n - 1) <
      Fintype.card F * Fintype.card F ^ (n - 1) :=
    Nat.mul_lt_mul_of_pos_right hq hpowpos
  have hpow : Fintype.card F * Fintype.card F ^ (n - 1) = Fintype.card F ^ n := by
    rw [mul_comm, ← pow_succ]
    congr 1
    omega
  have hcardD : Fintype.card D = Fintype.card F ^ n := by
    simpa [D] using card_dual F n
  have hbad : bad.card < Fintype.card D := by
    rw [hcardD]
    exact lt_of_le_of_lt hle (by simpa [hpow] using hlt1)
  rcases Finset.exists_mem_notMem_of_card_lt_card hbad with ⟨ℓ, -, hℓ⟩
  refine ⟨ℓ, ?_⟩
  by_contra h
  exact hℓ (by simp [bad, h])

theorem exists_separating_linear
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F) :
    ∃ ℓ : (Fin n → F) →ₗ[F] F,
      Function.Injective (fun i : Fin m => ℓ (z i)) := by
  classical
  by_cases hm : m ≤ 1
  · haveI : Subsingleton (Fin m) := by
      constructor
      intro a b
      apply Fin.ext
      have ha := a.isLt
      have hb := b.isLt
      omega
    refine ⟨0, ?_⟩
    intro i j _
    exact Subsingleton.elim i j
  · have hm2 : 2 ≤ m := by omega
    have hn : 0 < n := by
      by_contra h
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
      haveI : Subsingleton (Fin n → F) := by
        rw [hn0]
        infer_instance
      let i0 : Fin m := ⟨0, by omega⟩
      let i1 : Fin m := ⟨1, by omega⟩
      have h01 : i0 = i1 := hz (Subsingleton.elim (z i0) (z i1))
      have hval : (0 : ℕ) = 1 := congrArg Fin.val h01
      omega
    exact exists_separating_linear_of_bounds z hz hq hm2 hn

end Erdos571_hypergraph
