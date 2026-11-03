import Erdos571_hypergraph_L3_Host

open scoped BigOperators

namespace Erdos571_hypergraph

/-- A constructible subset of affine `N`-space over `ZMod q`, together with a
bound on the number and degrees of the defining polynomials. -/
def IsConstructible (q N m D : ℕ) (Y : Set (Fin N → ZMod q)) : Prop :=
  ∃ G H : Finset (MvPolynomial (Fin N) (ZMod q)),
    G.card + H.card ≤ m ∧
      (∀ g ∈ G, g.totalDegree ≤ D) ∧
      (∀ h ∈ H, h.totalDegree ≤ D) ∧
      Y = {x | (∀ g ∈ G, MvPolynomial.eval x g = 0) ∧
        (∀ h ∈ H, MvPolynomial.eval x h ≠ 0)}

/-- The uniform dichotomy of Theorem 2.4, recorded as the single general
algebraic-geometry input. -/
axiom uniformDichotomy (N m D : ℕ) :
    ∃ P q0 : ℕ, ∀ (q : ℕ) [Fact q.Prime], q0 ≤ q →
      ∀ Y : Set (Fin N → ZMod q), IsConstructible q N m D Y →
        Nat.card Y ≤ P ∨ (q : ℚ) / 2 ≤ (Nat.card Y : ℚ)

/-- A finite union of sets, each of which is either small or large, is itself
either small (with the sum of the bounds) or large. -/
lemma IsConstructible.mono {q N m m' D : ℕ} {Y : Set (Fin N → ZMod q)}
    (h : IsConstructible q N m D Y) (hm : m ≤ m') :
    IsConstructible q N m' D Y := by
  rcases h with ⟨G, H, hcard, hg, hh, hY⟩
  exact ⟨G, H, hcard.trans hm, hg, hh, hY⟩

lemma card_biUnion_dichotomy {ι α : Type*} [Fintype ι] [Fintype α]
    [DecidableEq α] (Y : ι → Finset α) (P : ℕ) (q : ℚ)
    (h : ∀ i, (Y i).card ≤ P ∨ q ≤ ((Y i).card : ℚ)) :
    (Finset.univ.biUnion Y).card ≤ Fintype.card ι * P ∨
      q ≤ ((Finset.univ.biUnion Y).card : ℚ) := by
  classical
  by_cases hlarge : ∃ i, q ≤ ((Y i).card : ℚ)
  · right
    obtain ⟨i, hi⟩ := hlarge
    exact le_trans hi (by
      exact_mod_cast Finset.card_le_card (Finset.subset_biUnion_of_mem Y
        (Finset.mem_univ i)))
  · left
    push_neg at hlarge
    have hsmall : ∀ i, (Y i).card ≤ P := by
      intro i
      rcases h i with hP | hQ
      · exact hP
      · exact absurd hQ (not_le_of_gt (hlarge i))
    calc
      (Finset.univ.biUnion Y).card ≤ ∑ i : ι, (Y i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i : ι, P := Finset.sum_le_sum (fun i _ => hsmall i)
      _ = Fintype.card ι * P := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

/-- A finite sum of naturals, each of which is small or large, is itself
small (with the sum of the bounds) or large. -/
lemma sum_dichotomy {ι : Type*} [Fintype ι] (f : ι → ℕ) (P : ℕ) (q : ℚ)
    (h : ∀ i, f i ≤ P ∨ q ≤ (f i : ℚ)) :
    (∑ i, f i) ≤ Fintype.card ι * P ∨ q ≤ ((∑ i, f i : ℕ) : ℚ) := by
  classical
  by_cases hlarge : ∃ i, q ≤ (f i : ℚ)
  · right
    obtain ⟨i, hi⟩ := hlarge
    exact le_trans hi (by
      exact_mod_cast Finset.single_le_sum
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i))
  · left
    push_neg at hlarge
    have hsmall : ∀ i, f i ≤ P := by
      intro i
      rcases h i with hP | hQ
      · exact hP
      · exact absurd hQ (not_le_of_gt (hlarge i))
    calc
      (∑ i, f i) ≤ ∑ _i : ι, P := Finset.sum_le_sum (fun i _ => hsmall i)
      _ = Fintype.card ι * P := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

lemma finset_sum_dichotomy {ι : Type*} (s : Finset ι) (f : ι → ℕ) (P : ℕ) (q : ℚ)
    (h : ∀ i ∈ s, f i ≤ P ∨ q ≤ (f i : ℚ)) :
    ((s.sum f : ℕ) ≤ s.card * P ∨ q ≤ ((s.sum f : ℕ) : ℚ)) := by
  classical
  by_cases hlarge : ∃ i ∈ s, q ≤ (f i : ℚ)
  · right
    obtain ⟨i, hi, hge⟩ := hlarge
    exact le_trans hge (by
      exact_mod_cast Finset.single_le_sum
        (fun j _ => Nat.zero_le _) hi)
  · left
    push_neg at hlarge
    have hsmall : ∀ i ∈ s, f i ≤ P := by
      intro i hi
      rcases h i hi with hP | hQ
      · exact hP
      · exact absurd hQ (not_le_of_gt (hlarge i hi))
    calc
      s.sum f ≤ s.sum (fun _ => P) :=
        Finset.sum_le_sum (fun i hi => hsmall i hi)
      _ = s.card * P := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul]

end Erdos571_hypergraph
