import Erdos571_hypergraph_L3_Moment
import Erdos571_hypergraph_L3_TypeEmbedInj

namespace Erdos571_hypergraph

/-- A fixed-type tuple witnesses that the type is edge-transversal. -/
lemma edgeTransversal_of_tuple {k : ℕ}
    (U : PartiteRootedKHypergraph k) (X : PartiteKHypergraph k)
    (w : U.R → X.V) (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1)
    (s : ℕ) (τ : TypeSpace U s) (t : TupleOfType U X w s τ) :
    EdgeTransversal U s τ (partConsistent_of_tuple U X w s τ t) := by
  classical
  let φ := TupleOfType.toSigma U X w s t
  have hτ : tupleType U X w s φ = τ := by
    cases τ with
    | mk part perm =>
      apply Prod.ext
      · change partitionOf U X w s (fun i =>
          (⟨perm i, t.emb i⟩ :
            Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)) = part
        exact t.is_type
      · rfl
  have h := edgeTransversal_tupleType U X w hwpart s φ
  simpa [hτ] using h

/-- For every type, the total number of fixed-type tuples over all hosts is
at most the number of hosts. -/
theorem hbound_all {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (P₀ : HostParams F k b a D)
    [DecidableEq (HostParams F k b a D)] :
    ∀ τ : TypeSpace U s,
      (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
        Fintype.card (HostParams F k b a D) := by
  classical
  intro τ
  by_cases hT : ∃ P : HostParams F k b a D,
      Nonempty (TupleOfType U (hostPartite P) w s τ)
  · rcases hT with ⟨P₁, ⟨t⟩⟩
    let hpc := partConsistent_of_tuple U (hostPartite P₁) w s τ t
    let hgood := edgeTransversal_of_tuple U (hostPartite P₁) w
      (fun r => hwpart r) s τ t
    let hτa := typeAdmissible_of_tuple U (hostPartite P₁) w s τ t
    have hsep : ∀ i : Fin s, Function.Injective
        (fun x : Interior U => blockOf U s τ x i) :=
      fun i => blockOf_injective_of_tuple U (hostPartite P₁) w s τ t i
    have hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i) :=
      fun i => typeEmbed_injective_of_tuple U (hostPartite P₁) w s τ t i
    exact sum_NτFixed_le_hostParams U a D w τ hpc hgood hwpart hτa
      hbal hsep hinj hs (hq τ) (hD τ) P₀
  · have hzero : ∀ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ = 0 := by
      intro P
      letI : Fintype (TupleOfType U (hostPartite P) w s τ) :=
        tupleOfTypeFintype U (hostPartite P) w s τ
      change Fintype.card (TupleOfType U (hostPartite P) w s τ) = 0
      exact Fintype.card_eq_zero_iff.mpr
        ⟨fun t => hT ⟨P, ⟨t⟩⟩⟩
    simp [hzero]

/-- Moment bound for the random polynomial host, with the paper's uniform
numerical hypotheses. -/
theorem momentAverage_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (P₀ : HostParams F k b a D) :
    momentAverage (a := a) (D := D) U w s ≤
      (Fintype.card (TypeSpace U s) : ℚ) := by
  classical
  apply momentAverage_le_of_bounds U a D w
  exact hbound_all U a D w hbal hwpart hs hq hD P₀

end Erdos571_hypergraph
