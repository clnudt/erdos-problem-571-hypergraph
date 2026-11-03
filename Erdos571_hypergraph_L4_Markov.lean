import Mathlib

namespace Erdos571_hypergraph

/-- Uniform probability on a finite type. -/
noncomputable def prob {α : Type*} [Fintype α] (E : α → Prop)
    [DecidablePred E] : ℚ :=
  (∑ a, if E a then (1 : ℚ) else 0) / (Fintype.card α : ℚ)

/-- Monotonicity of the uniform probability. -/
lemma prob_mono {α : Type*} [Fintype α] {E F : α → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ a, E a → F a) :
    prob E ≤ prob F := by
  classical
  unfold prob
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  apply Finset.sum_le_sum
  intro a _
  by_cases hE : E a
  · simp [hE, h a hE]
  · by_cases hF : F a <;> simp [hE, hF]

/-- The probability that a nonnegative integer-valued statistic is positive
is at most its expectation. -/
lemma prob_pos_le_expect {α : Type*} [Fintype α] (X : α → ℕ) :
    prob (fun a => 0 < X a) ≤
      (∑ a, (X a : ℚ)) / (Fintype.card α : ℚ) := by
  classical
  unfold prob
  apply div_le_div_of_nonneg_right ?_ (by positivity)
  apply Finset.sum_le_sum
  intro a _
  by_cases h : 0 < X a
  · simp [h]
    exact_mod_cast h
  · simp [h]

/-- Markov's inequality for the `s`-th moment. -/
theorem markov_pow {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℕ) (s : ℕ) (hs : 0 < s)
    (K : ℚ)
    (hX : (∑ a, (X a : ℚ) ^ s) / (Fintype.card α : ℚ) ≤ K)
    (t : ℚ) (ht : 0 < t) :
    prob (fun a => t ≤ (X a : ℚ)) ≤ K / t ^ s := by
  classical
  have hN : (0 : ℚ) < (Fintype.card α : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ a : α,
      (if t ≤ (X a : ℚ) then (1 : ℚ) else 0) ≤
        (X a : ℚ) ^ s / t ^ s := by
    intro a
    by_cases h : t ≤ (X a : ℚ)
    · rw [if_pos h]
      have h1 : (1 : ℚ) ≤ (X a : ℚ) / t := (one_le_div ht).mpr h
      have hpow : (1 : ℚ) ≤ ((X a : ℚ) / t) ^ s := one_le_pow₀ h1
      rwa [div_pow] at hpow
    · rw [if_neg h]
      positivity
  have hsum : (∑ a, (if t ≤ (X a : ℚ) then (1 : ℚ) else 0)) ≤
      ∑ a, (X a : ℚ) ^ s / t ^ s :=
    Finset.sum_le_sum (fun a _ => hterm a)
  have hdiv : (∑ a, (X a : ℚ) ^ s / t ^ s) =
      (∑ a, (X a : ℚ) ^ s) / t ^ s := by
    rw [Finset.sum_div]
  rw [prob, div_le_iff₀ hN]
  calc
    (∑ a, (if t ≤ (X a : ℚ) then (1 : ℚ) else 0)) ≤
        (∑ a, (X a : ℚ) ^ s) / t ^ s := by
      rw [← hdiv]
      exact hsum
    _ = ((∑ a, (X a : ℚ) ^ s) / (Fintype.card α : ℚ)) *
        ((Fintype.card α : ℚ) / t ^ s) := by
      field_simp
    _ ≤ K * ((Fintype.card α : ℚ) / t ^ s) := by
      gcongr
    _ = K / t ^ s * (Fintype.card α : ℚ) := by
      field_simp

/-- Number of bad parameters for a fixed root. -/
noncomputable def badCount {Ω W : Type*} [Fintype W]
    (C : Ω → W → ℕ) (P : ℕ) (ω : Ω) : ℕ :=
  (Finset.univ.filter (fun w => P < C ω w)).card

/-- Expected number of bad roots is at most the number of roots times the
per-root bad probability. -/
theorem expectation_badCount_le {Ω W : Type*} [Fintype Ω] [Fintype W]
    [Nonempty Ω]
    (C : Ω → W → ℕ) (P : ℕ) (ε : ℚ)
    (hprob : ∀ w : W, prob (fun ω => P < C ω w) ≤ ε) :
    (∑ ω, (badCount C P ω : ℚ)) / (Fintype.card Ω : ℚ) ≤
      (Fintype.card W : ℚ) * ε := by
  classical
  have hN : (0 : ℚ) < (Fintype.card Ω : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hcard : ∀ ω : Ω, (badCount C P ω : ℚ) =
      ∑ w : W, (if P < C ω w then (1 : ℚ) else 0) := by
    intro ω
    rw [badCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    push_cast
    rfl
  simp_rw [hcard]
  rw [Finset.sum_comm]
  rw [Finset.sum_div]
  calc
    (∑ w : W, (∑ ω, (if P < C ω w then (1 : ℚ) else 0)) /
        (Fintype.card Ω : ℚ)) ≤ ∑ _w : W, ε := by
      apply Finset.sum_le_sum
      intro w _
      simpa [prob] using hprob w
    _ = (Fintype.card W : ℚ) * ε := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The contribution of a bad event to the expectation is at most the
maximum value times the probability of the event. -/
theorem expected_indicator_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (M : Ω → ℕ) (B : Ω → Prop) [DecidablePred B]
    (Q : ℕ) (hM : ∀ ω, M ω ≤ Q) (ε : ℚ)
    (hB : prob B ≤ ε) :
    (∑ ω, (if B ω then (M ω : ℚ) else 0)) /
        (Fintype.card Ω : ℚ) ≤ (Q : ℚ) * ε := by
  classical
  have hN : (0 : ℚ) < (Fintype.card Ω : ℚ) := by
    exact_mod_cast Fintype.card_pos
  have hterm : ∀ ω : Ω,
      (if B ω then (M ω : ℚ) else 0) ≤
        (Q : ℚ) * (if B ω then (1 : ℚ) else 0) := by
    intro ω
    by_cases h : B ω
    · simp [h]
      exact_mod_cast hM ω
    · simp [h]
  have hsum : (∑ ω, (if B ω then (M ω : ℚ) else 0)) ≤
      (Q : ℚ) * ∑ ω, (if B ω then (1 : ℚ) else 0) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun ω _ => hterm ω)
  rw [div_le_iff₀ hN]
  calc
    (∑ ω, (if B ω then (M ω : ℚ) else 0)) ≤
        (Q : ℚ) * ∑ ω, (if B ω then (1 : ℚ) else 0) := hsum
    _ ≤ (Q : ℚ) * (ε * (Fintype.card Ω : ℚ)) := by
      gcongr
      rw [prob] at hB
      rw [div_le_iff₀ hN] at hB
      exact hB
    _ = (Q : ℚ) * ε * (Fintype.card Ω : ℚ) := by ring

end Erdos571_hypergraph
