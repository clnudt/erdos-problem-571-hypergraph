import Erdos571_hypergraph_L7_Existence

namespace Erdos571_hypergraph

/-- Explicit eventual lower and upper bounds imply `IsTheta`, i.e. the
`RealizesExponent` predicate. -/
theorem realizesExponent_of_eventually {k : ℕ} (F : FiniteKHypergraph k)
    {α : ℝ}
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ α ≤ (turanNumber F n : ℝ))
    (hupper : ∃ C : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      (turanNumber F n : ℝ) ≤ C * (n : ℝ) ^ α) :
    RealizesExponent F α := by
  classical
  constructor
  · obtain ⟨C, hC⟩ := hupper
    refine Asymptotics.IsBigO.of_bound (max C 0) ?_
    filter_upwards [hC] with n hn
    have hfn : 0 ≤ (turanNumber F n : ℝ) := by positivity
    have hgn : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (by positivity) α
    rw [Real.norm_eq_abs, abs_of_nonneg hfn,
      Real.norm_eq_abs, abs_of_nonneg hgn]
    exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgn)
  · obtain ⟨c, hc, hc'⟩ := hlower
    refine Asymptotics.IsBigO.of_bound (1 / c) ?_
    filter_upwards [hc'] with n hn
    have hfn : 0 ≤ (turanNumber F n : ℝ) := by positivity
    have hgn : 0 ≤ (n : ℝ) ^ α := Real.rpow_nonneg (by positivity) α
    rw [Real.norm_eq_abs, abs_of_nonneg hgn,
      Real.norm_eq_abs, abs_of_nonneg hfn]
    have hdiv : (n : ℝ) ^ α ≤ (turanNumber F n : ℝ) / c := by
      rw [le_div_iff₀ hc]
      calc
        (n : ℝ) ^ α * c = c * (n : ℝ) ^ α := by ring
        _ ≤ (turanNumber F n : ℝ) := hn
    calc
      (n : ℝ) ^ α ≤ (turanNumber F n : ℝ) / c := hdiv
      _ = (1 / c) * (turanNumber F n : ℝ) := by ring

end Erdos571_hypergraph
