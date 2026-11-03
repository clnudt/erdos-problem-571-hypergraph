import Erdos571_hypergraph_L3_Expectation
import Erdos571_hypergraph_L3_TypeBalance

namespace Erdos571_hypergraph

lemma toSigma_tupleToTupleOfType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    TupleOfType.toSigma U X w s
      (tupleToTupleOfType U X w s φ) = φ := by
  funext i
  rfl

/-- Every tuple is counted by the type-parametrized tuple family, so the
number of tuples is at most the sum of the fixed-type counts. -/
lemma Cw_pow_le_sum_NτFixed {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ) :
    Cw U X w ^ s ≤ ∑ τ : TypeSpace U s, NτFixed U X w s τ := by
  classical
  rw [← card_tuple U X w s]
  let f : Tuple U X w s → Σ τ : TypeSpace U s, TupleOfType U X w s τ :=
    fun φ => ⟨tupleType U X w s φ, tupleToTupleOfType U X w s φ⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    have h1 := congrArg
      (fun p : Σ τ : TypeSpace U s, TupleOfType U X w s τ =>
        TupleOfType.toSigma U X w s p.2) h
    change TupleOfType.toSigma U X w s (tupleToTupleOfType U X w s φ) =
      TupleOfType.toSigma U X w s (tupleToTupleOfType U X w s ψ) at h1
    rwa [toSigma_tupleToTupleOfType, toSigma_tupleToTupleOfType] at h1
  have h := Fintype.card_le_of_injective f hf
  simpa [NτFixed, Fintype.card_sigma] using h

lemma sum_NτFixed_le_hostParams {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hτa : TypeAdmissible U s τ)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hsep : ∀ i : Fin s, Function.Injective
      (fun x : Interior U => blockOf U s τ x i))
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i))
    (hs : 0 < s)
    (hq : (eτ U s τ).choose 2 < Fintype.card F)
    (hD : eτ U s τ ≤ D + 1)
    (P₀ : HostParams F k b a D)
    [DecidableEq (HostParams F k b a D)] :
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
      Fintype.card (HostParams F k b a D) := by
  classical
  have hExp := Nτ_expectation_sum_le U a D w τ h hgood hwpart hτa hs hq hD P₀
  have hTB := type_balance U τ a b hbal hτa hsep hinj
  have hpow : Fintype.card F ^ (b * hτ U s τ) ≤
      Fintype.card F ^ (a * eτ U s τ) :=
    Nat.pow_le_pow_right (Fintype.card_pos_iff.mpr ⟨(0 : F)⟩) hTB
  have hle : (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card F ^ (a * eτ U s τ) *
        Fintype.card (HostParams F k b a D) := by
    calc
      (∑ P, NτFixed U (hostPartite P) w s τ) *
          Fintype.card F ^ (a * eτ U s τ) ≤
          Fintype.card F ^ (b * hτ U s τ) *
            Fintype.card (HostParams F k b a D) := hExp
      _ ≤ Fintype.card F ^ (a * eτ U s τ) *
            Fintype.card (HostParams F k b a D) :=
        Nat.mul_le_mul_right _ hpow
  have hle' : (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card (HostParams F k b a D) *
        Fintype.card F ^ (a * eτ U s τ) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle
  exact Nat.le_of_mul_le_mul_right hle'
    (pow_pos (Fintype.card_pos_iff.mpr ⟨(0 : F)⟩) _)

lemma sum_Cw_pow_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b)
    (hbound : ∀ τ : TypeSpace U s,
      (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
        Fintype.card (HostParams F k b a D))
    [DecidableEq (TypeSpace U s)] :
    (∑ P : HostParams F k b a D,
        Cw U (hostPartite P) w ^ s) ≤
      Fintype.card (TypeSpace U s) *
        Fintype.card (HostParams F k b a D) := by
  classical
  calc
    (∑ P : HostParams F k b a D,
        Cw U (hostPartite P) w ^ s) ≤
        ∑ P : HostParams F k b a D,
          ∑ τ : TypeSpace U s,
            NτFixed U (hostPartite P) w s τ := by
      apply Finset.sum_le_sum
      intro P _
      exact Cw_pow_le_sum_NτFixed U (hostPartite P) w s
    _ = ∑ τ : TypeSpace U s,
        ∑ P : HostParams F k b a D,
          NτFixed U (hostPartite P) w s τ :=
      Finset.sum_comm
    _ ≤ ∑ _τ : TypeSpace U s,
        Fintype.card (HostParams F k b a D) := by
      apply Finset.sum_le_sum
      intro τ _
      exact hbound τ
    _ = Fintype.card (TypeSpace U s) *
        Fintype.card (HostParams F k b a D) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

theorem momentAverage_le_of_bounds {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ) (w : U.R → HostVertex F k b)
    (hbound : ∀ τ : TypeSpace U s,
      (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
        Fintype.card (HostParams F k b a D))
    [DecidableEq (TypeSpace U s)] :
    momentAverage (a := a) (D := D) U w s ≤
      (Fintype.card (TypeSpace U s) : ℚ) := by
  classical
  have hsum := sum_Cw_pow_le U a D w hbound
  have hHpos : (0 : ℚ) < (Fintype.card (HostParams F k b a D) : ℚ) := by
    have hpos : 0 < Fintype.card (HostParams F k b a D) :=
      Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0⟩⟩
    exact_mod_cast hpos
  change ((∑ P : HostParams F k b a D,
      ((Cw U (hostPartite P) w) ^ s : ℚ)) /
      (Fintype.card (HostParams F k b a D) : ℚ)) ≤
    (Fintype.card (TypeSpace U s) : ℚ)
  rw [div_le_iff₀ hHpos]
  have hsum' : ((∑ P : HostParams F k b a D,
        Cw U (hostPartite P) w ^ s : ℕ) : ℚ) ≤
      ((Fintype.card (TypeSpace U s) *
        Fintype.card (HostParams F k b a D) : ℕ) : ℚ) := by
    exact_mod_cast hsum
  simpa [Nat.cast_sum, Nat.cast_mul] using hsum'

end Erdos571_hypergraph
