import Erdos571_hypergraph_L4_Roots
import Erdos571_hypergraph_L4_Edges

set_option maxHeartbeats 1000000

namespace Erdos571_hypergraph

/-- The expected number of edges lost on the bad event. -/
theorem expected_bad_edges_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ} (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (Pstar : ℕ)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (hPstar : (Pstar : ℚ) < (Fintype.card F : ℚ) / 2)
    (hdich : ∀ (P : HostParams F k b a D) (w : LegalRoot U F b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card F : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ))
    (P₀ : HostParams F k b a D) :
    (∑ P : HostParams F k b a D,
        (if 0 < badRootCount U P Pstar then
          ((hostEdges P).card : ℚ) else 0)) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≤
      (Fintype.card F : ℚ) ^ (b * k) *
        ((Fintype.card (LegalRoot U F b) : ℚ) *
          ((Fintype.card (TypeSpace U s) : ℚ) /
            ((Fintype.card F : ℚ) / 2) ^ s)) := by
  classical
  haveI : Nonempty (HostParams F k b a D) :=
    ⟨⟨fun _ => 0⟩⟩
  have hB := prob_badRoots_le U a D Pstar hbal hs hq hD hPstar hdich P₀
  have hM : ∀ P : HostParams F k b a D,
      (hostEdges P).card ≤ Fintype.card F ^ (b * k) :=
    fun P => edgeCount_le P
  have h := expected_indicator_le
    (M := fun P => (hostEdges P).card)
    (B := fun P => 0 < badRootCount U P Pstar)
    (Q := Fintype.card F ^ (b * k))
    hM _ hB
  simpa [Nat.cast_pow] using h

theorem expected_good_edges_ge {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ} (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (Pstar : ℕ) (ha : a ≤ b * k)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (hPstar : (Pstar : ℚ) < (Fintype.card F : ℚ) / 2)
    (hdich : ∀ (P : HostParams F k b a D) (w : LegalRoot U F b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card F : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ))
    (P₀ : HostParams F k b a D) :
    (∑ P : HostParams F k b a D,
        (if 0 < badRootCount U P Pstar then 0 else
          ((hostEdges P).card : ℚ))) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≥
      (Fintype.card F : ℚ) ^ (b * k - a) -
        (Fintype.card F : ℚ) ^ (b * k) *
          ((Fintype.card (LegalRoot U F b) : ℚ) *
            ((Fintype.card (TypeSpace U s) : ℚ) /
              ((Fintype.card F : ℚ) / 2) ^ s)) := by
  classical
  let B : HostParams F k b a D → Prop :=
    fun P => 0 < badRootCount U P Pstar
  have hsplit : (∑ P : HostParams F k b a D,
        ((hostEdges P).card : ℚ)) =
      (∑ P : HostParams F k b a D,
        (if B P then ((hostEdges P).card : ℚ) else 0)) +
      (∑ P : HostParams F k b a D,
        (if B P then 0 else ((hostEdges P).card : ℚ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro P _
    by_cases h : B P <;> simp [h]
  have hE := edgeAverage_eq_pow (F := F) (k := k) (b := b) (a := a)
    (D := D) ha
  have hbad := expected_bad_edges_le U a D Pstar hbal hs hq hD
    hPstar hdich P₀
  have hN : (0 : ℚ) < (Fintype.card (HostParams F k b a D) : ℚ) := by
    have : 0 < Fintype.card (HostParams F k b a D) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨fun _ => (0 : PolyCoeff F (k * b) D)⟩⟩
    exact_mod_cast this
  have hdiv : (∑ P : HostParams F k b a D,
        ((hostEdges P).card : ℚ)) /
        (Fintype.card (HostParams F k b a D) : ℚ) =
      (∑ P : HostParams F k b a D,
        (if B P then ((hostEdges P).card : ℚ) else 0)) /
          (Fintype.card (HostParams F k b a D) : ℚ) +
      (∑ P : HostParams F k b a D,
        (if B P then 0 else ((hostEdges P).card : ℚ))) /
          (Fintype.card (HostParams F k b a D) : ℚ) := by
    rw [hsplit, add_div]
  change (∑ P : HostParams F k b a D,
      (if B P then 0 else ((hostEdges P).card : ℚ))) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≥ _
  linarith [hE, hbad, hdiv]

theorem exists_good_coeff {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ} (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (Pstar : ℕ) (ha : a ≤ b * k)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (hPstar : (Pstar : ℚ) < (Fintype.card F : ℚ) / 2)
    (hdich : ∀ (P : HostParams F k b a D) (w : LegalRoot U F b),
      Cw U (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card F : ℚ) / 2 ≤ (Cw U (hostPartite P) w.toFun : ℚ))
    (P₀ : HostParams F k b a D)
    (hgap : (Fintype.card F : ℚ) ^ (b * k) *
        ((Fintype.card (LegalRoot U F b) : ℚ) *
          ((Fintype.card (TypeSpace U s) : ℚ) /
            ((Fintype.card F : ℚ) / 2) ^ s)) <
      (Fintype.card F : ℚ) ^ (b * k - a) / 2) :
    ∃ P : HostParams F k b a D,
      badRootCount U P Pstar = 0 ∧
        (Fintype.card F : ℚ) ^ (b * k - a) / 2 ≤
          ((hostEdges P).card : ℚ) := by
  classical
  let H : ℚ := (Fintype.card F : ℚ) ^ (b * k - a)
  let B : HostParams F k b a D → Prop :=
    fun P => 0 < badRootCount U P Pstar
  have hgood := expected_good_edges_ge U a D Pstar ha hbal hs hq hD
    hPstar hdich P₀
  have hgt : H / 2 < (∑ P : HostParams F k b a D,
        (if B P then 0 else ((hostEdges P).card : ℚ))) /
        (Fintype.card (HostParams F k b a D) : ℚ) := by
    have h := hgood
    change _ ≤ (∑ P : HostParams F k b a D,
        (if B P then 0 else ((hostEdges P).card : ℚ))) /
        (Fintype.card (HostParams F k b a D) : ℚ) at h
    linarith
  by_contra h
  push_neg at h
  have hterm : ∀ P : HostParams F k b a D,
      (if B P then (0 : ℚ) else ((hostEdges P).card : ℚ)) ≤
        (H / 2) * (if B P then (0 : ℚ) else 1) := by
    intro P
    by_cases hB : B P
    · simp [hB]
    · simp [hB]
      have hZ : badRootCount U P Pstar = 0 := by
        by_contra hne
        have : 0 < badRootCount U P Pstar := Nat.pos_of_ne_zero hne
        exact hB this
      have := h P hZ
      linarith
  have hsum : (∑ P : HostParams F k b a D,
        (if B P then (0 : ℚ) else ((hostEdges P).card : ℚ))) ≤
      ∑ P : HostParams F k b a D,
        (H / 2) * (if B P then (0 : ℚ) else 1) :=
    Finset.sum_le_sum (fun P _ => hterm P)
  have hind : (∑ P : HostParams F k b a D,
        (if B P then (0 : ℚ) else 1)) ≤
      (Fintype.card (HostParams F k b a D) : ℚ) := by
    calc
      (∑ P, (if B P then (0 : ℚ) else 1)) ≤
          ∑ _P : HostParams F k b a D, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro P _
        by_cases hB : B P <;> simp [hB]
      _ = (Fintype.card (HostParams F k b a D) : ℚ) := by
        simp
  have hN : (0 : ℚ) < (Fintype.card (HostParams F k b a D) : ℚ) := by
    have : 0 < Fintype.card (HostParams F k b a D) :=
      Fintype.card_pos_iff.mpr
        ⟨⟨fun _ => (0 : PolyCoeff F (k * b) D)⟩⟩
    exact_mod_cast this
  have hle : (∑ P : HostParams F k b a D,
        (if B P then (0 : ℚ) else ((hostEdges P).card : ℚ))) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≤ H / 2 := by
    rw [div_le_iff₀ hN]
    calc
      (∑ P, (if B P then (0 : ℚ) else ((hostEdges P).card : ℚ))) ≤
          ∑ P, (H / 2) * (if B P then (0 : ℚ) else 1) := hsum
      _ = (H / 2) * (∑ P, (if B P then (0 : ℚ) else 1)) := by
        rw [Finset.mul_sum]
      _ ≤ (H / 2) * (Fintype.card (HostParams F k b a D) : ℚ) := by
        exact mul_le_mul_of_nonneg_left hind (by positivity)
  linarith

end Erdos571_hypergraph
