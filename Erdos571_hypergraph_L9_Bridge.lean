import Erdos571_hypergraph_L8_Upper

namespace Erdos571_hypergraph

/-- The number of vertices of the polynomial host. -/
lemma card_hostVertex (F : Type) [Fintype F] (k b : ℕ) :
    Fintype.card (HostVertex F k b) = k * Fintype.card F ^ b := by
  simp [HostVertex, Fintype.card_fun]

/-- A free host on `k q^b` vertices gives a lower bound on `Fin n` whenever
`k q^b ≤ n`, by adding isolated vertices. -/
theorem turanNumber_ge_host_fin {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D p : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (hp : 0 < p)
    (P : HostParams F k b a D)
    (hfree : ¬ IsCopy
      (partitePower (suspensionPartite k hk B) p hp).G
      (hostPartite P).G)
    {n : ℕ} (hn : k * Fintype.card F ^ b ≤ n) :
    (hostEdges P).card ≤
      turanNumber (FkrFinite hk B p hp) n := by
  classical
  let q := Fintype.card F
  have hqpos : 0 < q := Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hkpos : 0 < k := by omega
  have hcard : Fintype.card (HostVertex F k b) = k * q ^ b := by
    simpa [q] using card_hostVertex F k b
  let e1 : HostVertex F k b ≃ Fin (k * q ^ b) :=
    Fintype.equivFinOfCardEq hcard
  let H1 : KHypergraph k (Fin (k * q ^ b)) :=
    mapKHypergraph e1 (hostPartite P).G
  have hfree1 : ¬ IsCopy
      (partitePower (suspensionPartite k hk B) p hp).G H1 := by
    intro hc
    exact hfree ((isCopy_mapKHypergraph_iff e1
      (partitePower (suspensionPartite k hk B) p hp).G
      (hostPartite P).G).mp hc)
  have hcard1 : H1.edges.card = (hostEdges P).card :=
    card_mapKHypergraph e1 (hostPartite P).G
  have hpos : 0 < k * q ^ b := Nat.mul_pos hkpos (pow_pos hqpos b)
  letI : Nonempty (Fin (k * q ^ b)) := ⟨⟨0, hpos⟩⟩
  have hn' : k * q ^ b ≤ n := by simpa [q] using hn
  let e2 : Fin (k * q ^ b) ↪ Fin n := Fin.castLEEmb hn'
  let H2 : KHypergraph k (Fin n) := mapKHypergraphEmb e2 H1
  have hfree2 : ¬ IsCopy
      (partitePower (suspensionPartite k hk B) p hp).G H2 := by
    intro hc
    exact hfree1 (isCopy_mapEmb_of_no_isolated
      (partitePower (suspensionPartite k hk B) p hp).G
      (Fkr_vertex_covered hk B p hp) e2 H1 hc)
  have hcard2 : H2.edges.card = H1.edges.card :=
    card_mapKHypergraphEmb e2 H1
  calc
    (hostEdges P).card = H2.edges.card := by rw [hcard2, hcard1]
    _ ≤ turanNumber (FkrFinite hk B p hp) n :=
      le_turanNumber (FkrFinite hk B p hp) ⟨H2, hfree2, rfl⟩

/-- The largest `N` with `N^b ≤ M`. -/
noncomputable def maxPowRoot (b M : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (fun N => N ^ b ≤ M) M

lemma maxPowRoot_pow_le {b M : ℕ} (hb : 0 < b) :
    (maxPowRoot b M) ^ b ≤ M := by
  classical
  unfold maxPowRoot
  exact Nat.findGreatest_spec (P := fun N => N ^ b ≤ M)
    (Nat.zero_le M) (by simp [hb.ne'])

lemma lt_maxPowRoot_succ_pow {b M : ℕ} (hb : 0 < b) (hM : 0 < M) :
    M < (maxPowRoot b M + 1) ^ b := by
  classical
  by_contra h
  push_neg at h
  have hle : maxPowRoot b M + 1 ≤ M := by
    have h1 : maxPowRoot b M + 1 ≤ (maxPowRoot b M + 1) ^ b :=
      le_self_pow (by omega) (by omega)
    omega
  have hcontra : maxPowRoot b M + 1 ≤ maxPowRoot b M := by
    unfold maxPowRoot
    exact Nat.le_findGreatest hle h
  omega

/-- For every large `n` there is a prime `q` with `k q^b ≤ n` and
`q^b` comparable to `n`. -/
lemma exists_prime_pow_comparable {b k : ℕ} (hb : 0 < b) (hk : 0 < k) :
    ∃ C : ℕ, ∀ n : ℕ, 2 * k * 2 ^ b ≤ n →
      ∃ q : ℕ, Nat.Prime q ∧ k * q ^ b ≤ n ∧ n ≤ C * q ^ b := by
  classical
  let d := k * 2 ^ b
  refine ⟨2 * d, ?_⟩
  intro n hn
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.mul_pos hk (pow_pos (by norm_num) b)
  let M := n / d
  have hM2 : 2 ≤ M := by
    apply (Nat.le_div_iff_mul_le hdpos).mpr
    simpa [d, Nat.mul_assoc] using hn
  have hMpos : 0 < M := by omega
  let N := maxPowRoot b M
  have hN1 : 1 ≤ N := by
    dsimp [N]
    unfold maxPowRoot
    have h1M : 1 ≤ M := by omega
    have h1b : 1 ^ b ≤ M := by simpa using h1M
    exact Nat.le_findGreatest h1M h1b
  have hN0 : N ≠ 0 := by omega
  obtain ⟨q, hpq, hNq, hq2N⟩ :=
    Nat.exists_prime_lt_and_le_two_mul N hN0
  refine ⟨q, hpq, ?_, ?_⟩
  · -- `k q^b ≤ n`
    have hqpow : q ^ b ≤ (2 * N) ^ b := Nat.pow_le_pow_left hq2N b
    have hNpow : N ^ b ≤ M := by
      dsimp [N]
      exact maxPowRoot_pow_le (M := M) hb
    have h2 : (2 * N) ^ b = 2 ^ b * N ^ b := by
      rw [Nat.mul_pow]
    have hqpow' : q ^ b ≤ 2 ^ b * N ^ b := by
      simpa [h2] using hqpow
    have hkey : k * q ^ b ≤ k * (2 ^ b * N ^ b) :=
      Nat.mul_le_mul_left k hqpow'
    have hdM : k * (2 ^ b * N ^ b) = d * N ^ b := by
      dsimp [d]
      ring
    calc
      k * q ^ b ≤ k * (2 ^ b * N ^ b) := hkey
      _ = d * N ^ b := hdM
      _ ≤ d * M := Nat.mul_le_mul_left d hNpow
      _ ≤ n := Nat.mul_div_le n d
  · -- `n ≤ (2*d) * q^b`
    have hMlt : M < (N + 1) ^ b := by
      dsimp [N]
      exact lt_maxPowRoot_succ_pow hb hMpos
    have hq_ge : N + 1 ≤ q := by omega
    have hqpow : (N + 1) ^ b ≤ q ^ b := Nat.pow_le_pow_left hq_ge b
    have hM_q : M < q ^ b := lt_of_lt_of_le hMlt hqpow
    have hmod : n % d < d := Nat.mod_lt n hdpos
    have hdecomp : n = d * M + n % d := by
      dsimp [M]
      exact (Nat.div_add_mod n d).symm
    have hM1 : M + 1 ≤ q ^ b := by omega
    have hlt : n < (2 * d) * q ^ b := by
      calc
        n = d * M + n % d := hdecomp
        _ < d * M + d := by omega
        _ = d * (M + 1) := by ring
        _ ≤ d * q ^ b := Nat.mul_le_mul_left d hM1
        _ ≤ (2 * d) * q ^ b := by
          apply Nat.mul_le_mul_right
          omega
    exact le_of_lt hlt

end Erdos571_hypergraph
