import Erdos571_hypergraph_L9_Bridge
import Erdos571_hypergraph_L7_Existence

namespace Erdos571_hypergraph

lemma rpow_pow_identity {q b k a : ℕ} (hq : 0 ≤ (q : ℝ)) (hb : 0 < b)
    (ha : a ≤ b * k) :
    ((q : ℝ) ^ b) ^ ((k : ℝ) - (a : ℝ) / b) = (q : ℝ) ^ (b * k - a) := by
  rw [show ((q : ℝ) ^ b) = (q : ℝ) ^ ((b : ℕ) : ℝ) from
    (Real.rpow_natCast (q : ℝ) b).symm]
  rw [← Real.rpow_mul hq]
  have hexp : ((b : ℕ) : ℝ) * ((k : ℝ) - (a : ℝ) / b) =
      ((b * k - a : ℕ) : ℝ) := by
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    rw [Nat.cast_sub ha]
    push_cast
    field_simp
  rw [hexp]
  rw [Real.rpow_natCast]

lemma rpow_div_const_eq {n C : ℕ} {α : ℝ} (hC : 0 < (C : ℝ)) :
    ((n : ℝ) / (C : ℝ)) ^ α = (n : ℝ) ^ α * (C : ℝ) ^ (-α) := by
  rw [Real.div_rpow (by positivity) (le_of_lt hC)]
  rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hC) α]

lemma rpow_div_le {n C q b k a : ℕ} (hC : 0 < C) (hb : 0 < b)
    (ha : a ≤ b * k) (hn : n ≤ C * q ^ b) :
    ((n : ℝ) / (C : ℝ)) ^ ((k : ℝ) - (a : ℝ) / b) ≤
      (q : ℝ) ^ (b * k - a) := by
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC
  have hα : 0 ≤ (k : ℝ) - (a : ℝ) / b := by
    have hab : (a : ℝ) ≤ (b : ℝ) * k := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb
    field_simp
    nlinarith
  have hnC : (n : ℝ) / (C : ℝ) ≤ (q : ℝ) ^ b := by
    rw [div_le_iff₀ hCR]
    have h : (n : ℝ) ≤ (C : ℝ) * (q : ℝ) ^ b := by exact_mod_cast hn
    linarith
  have h1 : ((n : ℝ) / (C : ℝ)) ^ ((k : ℝ) - (a : ℝ) / b) ≤
      (((q : ℝ) ^ b) ^ ((k : ℝ) - (a : ℝ) / b)) :=
    Real.rpow_le_rpow (by positivity) hnC hα
  rwa [rpow_pow_identity (by positivity) hb ha] at h1

/-- Eventual lower bound for the forbidden power. -/
theorem eventual_lower_bound {k b a s : ℕ}
    (hk : 2 ≤ k) (hb : 0 < b) (B : BipartiteRootedGraph)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1) :
    ∃ Pstar : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      c * (n : ℝ) ^ ((k : ℝ) - (a : ℝ) / b) ≤
        (turanNumber (FkrFinite hk B (Pstar + 1) (by omega)) n : ℝ) := by
  classical
  have hkpos : 0 < k := by omega
  obtain ⟨Pstar, Q, hhost⟩ :=
    eventually_exists_free_host_unconditional hk hb B hbal ha hs
  obtain ⟨C, hC⟩ := exists_prime_pow_comparable (b := b) (k := k) hb hkpos
  have hCpos : 0 < C := by
    obtain ⟨q, hpq, hkq, hnq⟩ := hC (2 * k * 2 ^ b) (le_refl _)
    have hqpos : 0 < q := hpq.pos
    have hqpow : 0 < q ^ b := pow_pos hqpos b
    have : 0 < C * q ^ b := lt_of_lt_of_le (by positivity) hnq
    exact Nat.pos_of_mul_pos_right this
  let α : ℝ := (k : ℝ) - (a : ℝ) / b
  let c : ℝ := (1 / 2) * (C : ℝ) ^ (-α)
  refine ⟨Pstar, c, ?_, ?_⟩
  · dsimp [c]
    have : 0 < (C : ℝ) ^ (-α) := Real.rpow_pos_of_pos (by exact_mod_cast hCpos) _
    positivity
  · let n0 := max (2 * k * 2 ^ b) (C * (Q + 1) ^ b)
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hbase : 2 * k * 2 ^ b ≤ n := (le_max_left _ _).trans hn
    obtain ⟨q, hpq, hkq, hnq⟩ := hC n hbase
    letI : Fact q.Prime := ⟨hpq⟩
    have hQ : Q ≤ q := by
      have hn0 : C * (Q + 1) ^ b ≤ n := (le_max_right _ _).trans hn
      have hpow : (Q + 1) ^ b ≤ q ^ b := by
        have hmul : C * (Q + 1) ^ b ≤ C * q ^ b := le_trans hn0 hnq
        exact Nat.le_of_mul_le_mul_left hmul hCpos
      have hQ1 : Q + 1 ≤ q :=
        (Nat.pow_le_pow_iff_left (a := Q + 1) (b := q) hb.ne').mp hpow
      omega
    obtain ⟨P, hzero, hedges, hfree⟩ := hhost q hQ
    have hp : 0 < Pstar + 1 := by omega
    have hkq' : k * Fintype.card (ZMod q) ^ b ≤ n := by
      simpa [ZMod.card] using hkq
    have hfin : (hostEdges P).card ≤
        turanNumber (FkrFinite hk B (Pstar + 1) hp) n :=
      turanNumber_ge_host_fin hk B hp P hfree hkq'
    have hchain : (q : ℚ) ^ (b * k - a) / 2 ≤
        (turanNumber (FkrFinite hk B (Pstar + 1) hp) n : ℚ) :=
      hedges.trans (by exact_mod_cast hfin)
    have hreal : (1 / 2) * (q : ℝ) ^ (b * k - a) ≤
        (turanNumber (FkrFinite hk B (Pstar + 1) hp) n : ℝ) := by
      have h : (((q : ℚ) ^ (b * k - a) : ℚ) / 2 : ℝ) ≤
          (turanNumber (FkrFinite hk B (Pstar + 1) hp) n : ℝ) := by
        exact_mod_cast hchain
      push_cast at h
      linarith
    have hqle : ((n : ℝ) / (C : ℝ)) ^ α ≤ (q : ℝ) ^ (b * k - a) :=
      rpow_div_le hCpos hb (le_of_lt ha) hnq
    have hdiv : ((n : ℝ) / (C : ℝ)) ^ α =
        (n : ℝ) ^ α * (C : ℝ) ^ (-α) :=
      rpow_div_const_eq (α := α) (by exact_mod_cast hCpos)
    have hc : c * (n : ℝ) ^ α = (1 / 2) * ((n : ℝ) / (C : ℝ)) ^ α := by
      dsimp [c, α] at *
      rw [hdiv]
      ring
    rw [show (k : ℝ) - (a : ℝ) / b = α from rfl]
    rw [hc]
    calc
      (1 / 2) * ((n : ℝ) / (C : ℝ)) ^ α ≤
          (1 / 2) * (q : ℝ) ^ (b * k - a) := by
        exact mul_le_mul_of_nonneg_left hqle (by norm_num)
      _ ≤ (turanNumber (FkrFinite hk B (Pstar + 1) hp) n : ℝ) := hreal

/-- Proposition 2.1 together with Lemma 2.2: for the balanced rooted graph
given by Proposition 2.1, every rooted power has the required upper bound. -/
axiom rootedES_upper {k a b : ℕ} (hk : 2 ≤ k) (ha0 : 0 < a) (hb : 0 < b)
    (ha : a ≤ b) :
    ∃ B : BipartiteRootedGraph, Balanced B.T a b ∧
      ∀ (p : ℕ) (hp : 0 < p), ∃ C : ℝ,
        ∀ᶠ n : ℕ in Filter.atTop,
          (turanNumber (FkrFinite hk B p hp) n : ℝ) ≤
            C * (n : ℝ) ^ ((k : ℝ) - (a : ℝ) / b)

/-- Theorem 1.2: for every `k ≥ 2` and rational `r = a/b ∈ (0,1]`, there is a
single forbidden `k`-graph whose Turán number is `Θ(n^(k-a/b))`. -/
theorem main {k a b : ℕ} (hk : 2 ≤ k) (ha0 : 0 < a) (hb : 0 < b)
    (ha : a ≤ b) :
    ∃ (B : BipartiteRootedGraph) (Pstar : ℕ),
      RealizesExponent (FkrFinite hk B (Pstar + 1) (by omega))
        ((k : ℝ) - (a : ℝ) / b) := by
  classical
  obtain ⟨B, hbal, hupperAll⟩ := rootedES_upper hk ha0 hb ha
  have habk : a < b * k := by nlinarith [ha, hk, hb]
  let s := b * Fintype.card (suspensionPartite k hk B).R + a + 1
  obtain ⟨Pstar, c, hc, hlower⟩ :=
    eventual_lower_bound (s := s) hk hb B hbal habk rfl
  have hp : 0 < Pstar + 1 := by omega
  have hupper := hupperAll (Pstar + 1) hp
  refine ⟨B, Pstar, ?_⟩
  exact realizesExponent_of_eventually (FkrFinite hk B (Pstar + 1) hp)
    ⟨c, hc, hlower⟩ hupper

end Erdos571_hypergraph
