import Erdos571_hypergraph_L6_Lower

namespace Erdos571_hypergraph

/-- Concrete lower bound for the Turán number, assuming the numerical
hypotheses of the random algebraic construction at a prime `q`. -/
theorem turanNumber_ge_of_hypotheses {k b a D p s Pstar : ℕ}
    (q : ℕ) [Fact q.Prime] (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (hp : 0 < p) (hP : p = Pstar + 1) (hbal : Balanced B.T a b)
    (ha : a ≤ b * k) (hs : 0 < s)
    (hq : ∀ τ : TypeSpace (suspensionPartite k hk B) s,
      (eτ (suspensionPartite k hk B) s τ).choose 2 < q)
    (hD : ∀ τ : TypeSpace (suspensionPartite k hk B) s,
      eτ (suspensionPartite k hk B) s τ ≤ D + 1)
    (hPstar : (Pstar : ℚ) < (q : ℚ) / 2)
    (hdich : ∀ (P : HostParams (ZMod q) k b a D)
        (w : LegalRoot (suspensionPartite k hk B) (ZMod q) b),
      Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
        (q : ℚ) / 2 ≤
          (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ))
    (P₀ : HostParams (ZMod q) k b a D)
    (hgap : (q : ℚ) ^ (b * k) *
        ((Fintype.card (LegalRoot (suspensionPartite k hk B) (ZMod q) b) : ℚ) *
          ((Fintype.card (TypeSpace (suspensionPartite k hk B) s) : ℚ) /
            ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2) :
    (q : ℚ) ^ (b * k - a) / 2 ≤
      (turanNumber (FkrFinite hk B p hp) (k * q ^ b) : ℚ) := by
  classical
  have hq' : ∀ τ : TypeSpace (suspensionPartite k hk B) s,
      (eτ (suspensionPartite k hk B) s τ).choose 2 <
        Fintype.card (ZMod q) := by
    simpa [ZMod.card] using hq
  have hPstar' : (Pstar : ℚ) < (Fintype.card (ZMod q) : ℚ) / 2 := by
    simpa [ZMod.card] using hPstar
  have hdich' : ∀ (P : HostParams (ZMod q) k b a D)
      (w : LegalRoot (suspensionPartite k hk B) (ZMod q) b),
      Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card (ZMod q) : ℚ) / 2 ≤
          (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ) := by
    simpa [ZMod.card] using hdich
  have hgap' : (Fintype.card (ZMod q) : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot (suspensionPartite k hk B) (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace (suspensionPartite k hk B) s) : ℚ) /
          ((Fintype.card (ZMod q) : ℚ) / 2) ^ s)) <
      (Fintype.card (ZMod q) : ℚ) ^ (b * k - a) / 2 := by
    simpa [ZMod.card] using hgap
  obtain ⟨P, -, hedges, hfree⟩ :=
    exists_free_host (F := ZMod q) hk B hp Pstar hP hbal ha hs hq' hD
      hPstar' hdich' P₀ hgap'
  have hle := turanNumber_ge_host hk B hp P hfree
  have hcard : Fintype.card (HostVertex (ZMod q) k b) = k * q ^ b := by
    simp [HostVertex, ZMod.card]
  rw [hcard] at hle
  have hleQ : ((hostEdges P).card : ℚ) ≤
      (turanNumber (FkrFinite hk B p hp) (k * q ^ b) : ℚ) := by
    exact_mod_cast hle
  simpa [ZMod.card] using hedges.trans hleQ

/-- There are arbitrarily large primes. -/
lemma exists_prime_gt (N : ℕ) : ∃ q : ℕ, Nat.Prime q ∧ N < q := by
  obtain ⟨q, hq, hp⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨q, hp, by omega⟩

/-- The choice `D = s |E(U)|` satisfies the hypothesis of the moment bound. -/
lemma hD_self {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ) :
    ∀ τ : TypeSpace U s, eτ U s τ ≤ s * U.G.edges.card + 1 :=
  hD_of_edges_le U s (s * U.G.edges.card) le_rfl

/-- The algebraic core of the `hgap` estimate. -/
lemma hgap_algebra {q k b a s rho T0 : ℕ} (hq : 0 < q)
    (hs : s = b * rho + a + 1) (ha : a < b * k)
    (hQ : 2 * Nat.factorial k * T0 * 2 ^ s < q) :
    (q : ℚ) ^ (b * k) *
      ((Nat.factorial k : ℚ) * (q : ℚ) ^ (b * rho) *
        (T0 / ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2 := by
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have h2Q : (0 : ℚ) < 2 := by norm_num
  rw [div_pow]
  field_simp [hqQ.ne', h2Q.ne']
  have hexp : s + (b * k - a) = b * k + b * rho + 1 := by omega
  have hQ' : (2 * (Nat.factorial k : ℚ) * T0 * 2 ^ s) < q := by
    exact_mod_cast hQ
  have hQ'' : (Nat.factorial k : ℚ) * T0 * 2 ^ s * 2 < q := by
    nlinarith
  calc
    (q : ℚ) ^ (b * k) * (Nat.factorial k : ℚ) * (q : ℚ) ^ (b * rho) *
        T0 * 2 ^ s * 2
        = (q : ℚ) ^ (b * k + b * rho) *
            ((Nat.factorial k : ℚ) * T0 * 2 ^ s * 2) := by
          rw [pow_add]
          ring
    _ < (q : ℚ) ^ (b * k + b * rho) * q := by
          exact mul_lt_mul_of_pos_left hQ'' (pow_pos hqQ _)
    _ = (q : ℚ) ^ s * (q : ℚ) ^ (b * k - a) := by
          rw [← pow_add, hexp, pow_succ]

/-- The legal-root count, with the field cardinality specialized to `q`. -/
lemma legalRoot_card_le_pow_q {k b : ℕ} (U : PartiteRootedKHypergraph k)
    (q : ℕ) [NeZero q] :
    (Fintype.card (LegalRoot U (ZMod q) b) : ℚ) ≤
      (Nat.factorial k : ℚ) * (q : ℚ) ^ (b * Fintype.card U.R) := by
  have h := legalRoot_card_le_pow U (ZMod q) b
  rw [ZMod.card] at h
  exact_mod_cast h

/-- The `hgap` hypothesis holds once `q` exceeds an explicit threshold. -/
lemma hgap_of_large {k b a s : ℕ} (U : PartiteRootedKHypergraph k)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    (hs : s = b * Fintype.card U.R + a + 1)
    (ha : a < b * k)
    (hQ : 2 * Nat.factorial k *
      Fintype.card (TypeSpace U s) * 2 ^ s < q) :
    (q : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2 := by
  have hLR := legalRoot_card_le_pow_q (b := b) U q
  have hbase := hgap_algebra (q := q) (k := k) (b := b) (a := a)
    (s := s) (rho := Fintype.card U.R)
    (T0 := Fintype.card (TypeSpace U s)) hq hs ha hQ
  have hmono : (q : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) ≤
      (q : ℚ) ^ (b * k) *
        ((Nat.factorial k : ℚ) *
          (q : ℚ) ^ (b * Fintype.card U.R) *
          ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) := by
    gcongr
  exact lt_of_le_of_lt hmono hbase

/-- The `hq` hypothesis holds once `q` exceeds `(s |E(U)|)^2`. -/
lemma hq_of_large {k : ℕ} (U : PartiteRootedKHypergraph k) (s q : ℕ)
    (h : (s * U.G.edges.card) ^ 2 < q) :
    ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < q := by
  intro τ
  have h1 := eτ_le_edges U s τ
  calc
    (eτ U s τ).choose 2 ≤ (eτ U s τ) ^ 2 := Nat.choose_le_pow _ _
    _ ≤ (s * U.G.edges.card) ^ 2 := Nat.pow_le_pow_left h1 2
    _ < q := h

/-- The `hPstar` hypothesis holds once `q > 2 P_*`. -/
lemma hPstar_of_large {Pstar q : ℕ} (h : 2 * Pstar < q) :
    (Pstar : ℚ) < (q : ℚ) / 2 := by
  have h' : (2 * Pstar : ℚ) < q := by exact_mod_cast h
  linarith

end Erdos571_hypergraph
