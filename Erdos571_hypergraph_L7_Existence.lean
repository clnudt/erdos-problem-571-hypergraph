import Erdos571_hypergraph_L6_Instantiate
import Erdos571_hypergraph_L25_RootFibreProof

set_option maxHeartbeats 1000000

namespace Erdos571_hypergraph

/-- Proposition 2.5 (root-fibre dichotomy), proved from `uniformDichotomy`.
The constants `Pstar` and `qstar` depend only on `U`, `a`, `b` and `D`. -/
theorem rootFibreDichotomy {k b : ℕ} (U : PartiteRootedKHypergraph k)
    (a D : ℕ) (hb : 0 < b) :
    ∃ Pstar qstar : ℕ, ∀ (q : ℕ) [Fact q.Prime], qstar ≤ q →
      ∀ (P : HostParams (ZMod q) k b a D)
        (w : LegalRoot U (ZMod q) b),
        Cw U (hostPartite P) w.toFun ≤ Pstar ∨
          (q : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ) := by
  obtain ⟨Pstar, qstar, h⟩ := rootFibreDichotomy_proved hb U
  refine ⟨Pstar, qstar, ?_⟩
  intro q _ hq P w
  rcases h q hq P w.toFun with hsmall | hlarge
  · exact Or.inl hsmall
  · exact Or.inr (by exact_mod_cast hlarge)

/-- For sufficiently large prime `q`, the concrete lower bound holds, assuming
the root-fibre dichotomy beyond `qstar`. -/
theorem exists_prime_turanNumber_lower {k b a s Pstar qstar : ℕ}
    (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) (hP : p = Pstar + 1)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1)
    (hdich : ∀ (q : ℕ) [Fact q.Prime], qstar ≤ q →
      ∀ (P : HostParams (ZMod q) k b a
          (s * (suspensionPartite k hk B).G.edges.card))
        (w : LegalRoot (suspensionPartite k hk B) (ZMod q) b),
        Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
          (q : ℚ) / 2 ≤
            (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ)) :
    ∃ q : ℕ, Nat.Prime q ∧
      (q : ℚ) ^ (b * k - a) / 2 ≤
        (turanNumber (FkrFinite hk B p hp) (k * q ^ b) : ℚ) := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  let T0 := Fintype.card (TypeSpace U s)
  let N := max qstar
    (max ((s * E) ^ 2) (max (2 * Pstar) (2 * Nat.factorial k * T0 * 2 ^ s)))
  obtain ⟨q, hpq, hqN⟩ := exists_prime_gt N
  have hq : 0 < q := hpq.pos
  letI : Fact q.Prime := ⟨hpq⟩
  have hqstar : qstar ≤ q := (le_max_left _ _).trans (le_of_lt hqN)
  have hq1 : (s * E) ^ 2 < q :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hqN
  have hPstar_le : 2 * Pstar ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hgap_le : 2 * Nat.factorial k * T0 * 2 ^ s ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hPstar_bound : 2 * Pstar < q := lt_of_le_of_lt hPstar_le hqN
  have hgap_bound : 2 * Nat.factorial k * T0 * 2 ^ s < q :=
    lt_of_le_of_lt hgap_le hqN
  have hq' : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < q :=
    hq_of_large U s q (by simpa [E] using hq1)
  have hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ s * E + 1 := by
    simpa [E] using hD_self U s
  have hPstar' : (Pstar : ℚ) < (q : ℚ) / 2 :=
    hPstar_of_large hPstar_bound
  have hgap : (q : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2 := by
    simpa [U, E, T0] using
      hgap_of_large U q hq (by simpa [U] using hs) ha (by simpa [T0] using hgap_bound)
  let P₀ : HostParams (ZMod q) k b a (s * E) := ⟨fun _ => 0⟩
  have hdich' : ∀ (P : HostParams (ZMod q) k b a (s * E))
      (w : LegalRoot U (ZMod q) b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (q : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ) := by
    simpa [U, E] using hdich q hqstar
  have hmain := turanNumber_ge_of_hypotheses (q := q) hk B hp hP hbal
    (le_of_lt ha) (by omega) hq' hD hPstar' hdich' P₀ (by simpa [U, E] using hgap)
  exact ⟨q, hpq, by simpa [U, E] using hmain⟩

/-- The lower bound holds for every sufficiently large prime `q`, with the
same forbidden graph. -/
theorem eventually_prime_turanNumber_lower {k b a s Pstar qstar : ℕ}
    (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) (hP : p = Pstar + 1)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1)
    (hdich : ∀ (q : ℕ) [Fact q.Prime], qstar ≤ q →
      ∀ (P : HostParams (ZMod q) k b a
          (s * (suspensionPartite k hk B).G.edges.card))
        (w : LegalRoot (suspensionPartite k hk B) (ZMod q) b),
        Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
          (q : ℚ) / 2 ≤
            (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ)) :
    ∃ Q : ℕ, ∀ q : ℕ, Nat.Prime q → Q ≤ q →
      (q : ℚ) ^ (b * k - a) / 2 ≤
        (turanNumber (FkrFinite hk B p hp) (k * q ^ b) : ℚ) := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  let T0 := Fintype.card (TypeSpace U s)
  let Q := max qstar
    (max ((s * E) ^ 2 + 1)
      (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)))
  refine ⟨Q, ?_⟩
  intro q hpq hQ
  have hq : 0 < q := hpq.pos
  letI : Fact q.Prime := ⟨hpq⟩
  have hqstar : qstar ≤ q := (le_max_left _ _).trans hQ
  have hq1 : (s * E) ^ 2 < q := by
    have : (s * E) ^ 2 + 1 ≤ Q := by
      calc
        (s * E) ^ 2 + 1 ≤
            max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_left _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hPstar_bound : 2 * Pstar < q := by
    have : 2 * Pstar + 1 ≤ Q := by
      calc
        2 * Pstar + 1 ≤
            max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1) :=
          le_max_left _ _
        _ ≤ max ((s * E) ^ 2 + 1)
            (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_right _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hgap_bound : 2 * Nat.factorial k * T0 * 2 ^ s < q := by
    have : 2 * Nat.factorial k * T0 * 2 ^ s + 1 ≤ Q := by
      calc
        2 * Nat.factorial k * T0 * 2 ^ s + 1 ≤
            max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1) :=
          le_max_right _ _
        _ ≤ max ((s * E) ^ 2 + 1)
            (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_right _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hq' : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < q :=
    hq_of_large U s q (by simpa [E] using hq1)
  have hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ s * E + 1 := by
    simpa [E] using hD_self U s
  have hPstar' : (Pstar : ℚ) < (q : ℚ) / 2 :=
    hPstar_of_large hPstar_bound
  have hgap : (q : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2 := by
    simpa [U, E, T0] using
      hgap_of_large U q hq (by simpa [U] using hs) ha
        (by simpa [T0] using hgap_bound)
  let P₀ : HostParams (ZMod q) k b a (s * E) := ⟨fun _ => 0⟩
  have hdich' : ∀ (P : HostParams (ZMod q) k b a (s * E))
      (w : LegalRoot U (ZMod q) b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (q : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ) := by
    simpa [U, E] using hdich q hqstar
  have hmain := turanNumber_ge_of_hypotheses (q := q) hk B hp hP hbal
    (le_of_lt ha) (by omega) hq' hD hPstar' hdich' P₀ (by simpa [U, E] using hgap)
  simpa [U, E] using hmain

/-- For every sufficiently large prime there is an actual free host with the
required number of edges. -/
theorem eventually_prime_exists_free_host {k b a s Pstar qstar : ℕ}
    (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) (hP : p = Pstar + 1)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1)
    (hdich : ∀ (q : ℕ) [Fact q.Prime], qstar ≤ q →
      ∀ (P : HostParams (ZMod q) k b a
          (s * (suspensionPartite k hk B).G.edges.card))
        (w : LegalRoot (suspensionPartite k hk B) (ZMod q) b),
        Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
          (q : ℚ) / 2 ≤
            (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ)) :
    ∃ Q : ℕ, ∀ (q : ℕ) [Fact q.Prime], Q ≤ q →
      ∃ P : HostParams (ZMod q) k b a
          (s * (suspensionPartite k hk B).G.edges.card),
        badRootCount (suspensionPartite k hk B) P Pstar = 0 ∧
        (q : ℚ) ^ (b * k - a) / 2 ≤ (hostEdges P).card ∧
        ¬ IsCopy
          (partitePower (suspensionPartite k hk B) p hp).G
          (hostPartite P).G := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  let T0 := Fintype.card (TypeSpace U s)
  let Q := max qstar
    (max ((s * E) ^ 2 + 1)
      (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)))
  refine ⟨Q, ?_⟩
  intro q _ hQ
  have hpq : Nat.Prime q := Fact.out
  have hq : 0 < q := hpq.pos
  have hqstar : qstar ≤ q := (le_max_left _ _).trans hQ
  have hq1 : (s * E) ^ 2 < q := by
    have : (s * E) ^ 2 + 1 ≤ Q := by
      calc
        (s * E) ^ 2 + 1 ≤
            max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_left _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hPstar_bound : 2 * Pstar < q := by
    have : 2 * Pstar + 1 ≤ Q := by
      calc
        2 * Pstar + 1 ≤
            max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1) :=
          le_max_left _ _
        _ ≤ max ((s * E) ^ 2 + 1)
            (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_right _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hgap_bound : 2 * Nat.factorial k * T0 * 2 ^ s < q := by
    have : 2 * Nat.factorial k * T0 * 2 ^ s + 1 ≤ Q := by
      calc
        2 * Nat.factorial k * T0 * 2 ^ s + 1 ≤
            max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1) :=
          le_max_right _ _
        _ ≤ max ((s * E) ^ 2 + 1)
            (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1)) :=
          le_max_right _ _
        _ ≤ max qstar
            (max ((s * E) ^ 2 + 1)
              (max (2 * Pstar + 1) (2 * Nat.factorial k * T0 * 2 ^ s + 1))) :=
          le_max_right _ _
    omega
  have hq' : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < q :=
    hq_of_large U s q (by simpa [E] using hq1)
  have hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ s * E + 1 := by
    simpa [E] using hD_self U s
  have hPstar' : (Pstar : ℚ) < (q : ℚ) / 2 :=
    hPstar_of_large hPstar_bound
  have hgap : (q : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) / ((q : ℚ) / 2) ^ s)) <
      (q : ℚ) ^ (b * k - a) / 2 := by
    simpa [U, E, T0] using
      hgap_of_large U q hq (by simpa [U] using hs) ha
        (by simpa [T0] using hgap_bound)
  let P₀ : HostParams (ZMod q) k b a (s * E) := ⟨fun _ => 0⟩
  have hdich' : ∀ (P : HostParams (ZMod q) k b a (s * E))
      (w : LegalRoot U (ZMod q) b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (q : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ) := by
    simpa [U, E] using hdich q hqstar
  have hq'' : ∀ τ : TypeSpace U s,
      (eτ U s τ).choose 2 < Fintype.card (ZMod q) := by
    simpa [ZMod.card] using hq'
  have hPstar'' : (Pstar : ℚ) < (Fintype.card (ZMod q) : ℚ) / 2 := by
    simpa [ZMod.card] using hPstar'
  have hdich'' : ∀ (P : HostParams (ZMod q) k b a (s * E))
      (w : LegalRoot U (ZMod q) b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card (ZMod q) : ℚ) / 2 ≤
          (Cw U (hostPartite P) w.toFun : ℚ) := by
    simpa [ZMod.card] using hdich'
  have hgap'' : (Fintype.card (ZMod q) : ℚ) ^ (b * k) *
      ((Fintype.card (LegalRoot U (ZMod q) b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) /
          ((Fintype.card (ZMod q) : ℚ) / 2) ^ s)) <
      (Fintype.card (ZMod q) : ℚ) ^ (b * k - a) / 2 := by
    simpa [ZMod.card] using hgap
  obtain ⟨P, hzero, hedges, hfree⟩ :=
    exists_free_host (F := ZMod q) hk B hp Pstar hP hbal (le_of_lt ha)
      (by omega) hq'' hD hPstar'' hdich'' P₀ (by simpa [U, E] using hgap'')
  refine ⟨P, hzero, ?_, hfree⟩
  simpa [ZMod.card] using hedges

/-- Unconditional version: one fixed forbidden graph, and free hosts with the
required edge count for every sufficiently large prime. -/
theorem eventually_exists_free_host_unconditional {k b a s : ℕ}
    (hk : 2 ≤ k) (hb : 0 < b) (B : BipartiteRootedGraph)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1) :
    ∃ Pstar : ℕ, ∃ Q : ℕ, ∀ (q : ℕ) [Fact q.Prime], Q ≤ q →
      ∃ P : HostParams (ZMod q) k b a
          (s * (suspensionPartite k hk B).G.edges.card),
        badRootCount (suspensionPartite k hk B) P Pstar = 0 ∧
        (q : ℚ) ^ (b * k - a) / 2 ≤ (hostEdges P).card ∧
        ¬ IsCopy
          (partitePower (suspensionPartite k hk B) (Pstar + 1) (by omega)).G
          (hostPartite P).G := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  obtain ⟨Pstar, qstar, hdich⟩ := rootFibreDichotomy (b := b) U a (s * E) hb
  have hp : 0 < Pstar + 1 := by omega
  obtain ⟨Q, hQ⟩ :=
    eventually_prime_exists_free_host (k := k) (b := b) (a := a) (s := s)
      (Pstar := Pstar) (qstar := qstar) hk B (Pstar + 1) hp rfl hbal ha hs
      (by simpa [U, E] using hdich)
  exact ⟨Pstar, Q, hQ⟩

/-- Unconditional existence of a prime `q` and a forbidden power `(S^k T)^(p)`
for which the lower bound holds. -/
theorem exists_prime_turanNumber_lower_unconditional {k b a s : ℕ}
    (hk : 2 ≤ k) (hb : 0 < b) (B : BipartiteRootedGraph)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1) :
    ∃ Pstar : ℕ, ∃ q : ℕ, Nat.Prime q ∧
      (q : ℚ) ^ (b * k - a) / 2 ≤
        (turanNumber (FkrFinite hk B (Pstar + 1) (by omega))
          (k * q ^ b) : ℚ) := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  obtain ⟨Pstar, qstar, hdich⟩ := rootFibreDichotomy (b := b) U a (s * E) hb
  have hp : 0 < Pstar + 1 := by omega
  obtain ⟨q, hpq, hbound⟩ :=
    exists_prime_turanNumber_lower (k := k) (b := b) (a := a) (s := s)
      (Pstar := Pstar) (qstar := qstar) hk B (Pstar + 1) hp rfl hbal ha hs
      (by simpa [U, E] using hdich)
  exact ⟨Pstar, q, hpq, hbound⟩

/-- The same lower bound holds for every sufficiently large prime, with one
fixed forbidden graph. -/
theorem eventually_prime_turanNumber_lower_unconditional {k b a s : ℕ}
    (hk : 2 ≤ k) (hb : 0 < b) (B : BipartiteRootedGraph)
    (hbal : Balanced B.T a b) (ha : a < b * k)
    (hs : s = b * Fintype.card (suspensionPartite k hk B).R + a + 1) :
    ∃ Pstar : ℕ, ∃ Q : ℕ, ∀ q : ℕ, Nat.Prime q → Q ≤ q →
      (q : ℚ) ^ (b * k - a) / 2 ≤
        (turanNumber (FkrFinite hk B (Pstar + 1) (by omega))
          (k * q ^ b) : ℚ) := by
  classical
  let U := suspensionPartite k hk B
  let E := U.G.edges.card
  obtain ⟨Pstar, qstar, hdich⟩ := rootFibreDichotomy (b := b) U a (s * E) hb
  have hp : 0 < Pstar + 1 := by omega
  obtain ⟨Q, hQ⟩ :=
    eventually_prime_turanNumber_lower (k := k) (b := b) (a := a) (s := s)
      (Pstar := Pstar) (qstar := qstar) hk B (Pstar + 1) hp rfl hbal ha hs
      (by simpa [U, E] using hdich)
  exact ⟨Pstar, Q, hQ⟩

end Erdos571_hypergraph
