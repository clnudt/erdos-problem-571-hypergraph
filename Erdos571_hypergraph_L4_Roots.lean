import Erdos571_hypergraph_L3_HBound
import Erdos571_hypergraph_L3_Host
import Erdos571_hypergraph_L4_Markov

set_option maxHeartbeats 1000000

namespace Erdos571_hypergraph

/-- A legal root position, in the sense of the manuscript: an injective root
map together with a single global permutation of the `k` parts. -/
structure LegalRoot {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) (b : ℕ) where
  toFun : U.R → HostVertex F k b
  inj : Function.Injective toFun
  sigma : Equiv.Perm (Fin k)
  part_eq : ∀ r : U.R, (toFun r).1 = sigma (U.part r.1)

instance legalRootCoeFun {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) (b : ℕ) :
    CoeFun (LegalRoot U F b) (fun _ => U.R → HostVertex F k b) :=
  ⟨LegalRoot.toFun⟩

lemma LegalRoot.toIsLegalRoot {k b a D q : ℕ} [Fact q.Prime]
    {U : PartiteRootedKHypergraph k}
    {P : HostParams (ZMod q) k b a D}
    (w : LegalRoot U (ZMod q) b) :
    IsLegalRoot U (hostPartite P) w.toFun := by
  refine ⟨w.inj, w.sigma, ?_⟩
  intro r
  simpa [hostPartite] using w.part_eq r

lemma IsLegalRoot.exists_legalRoot {k b a D q : ℕ} [Fact q.Prime]
    {U : PartiteRootedKHypergraph k}
    {P : HostParams (ZMod q) k b a D}
    {w : U.R → HostVertex (ZMod q) k b}
    (h : IsLegalRoot U (hostPartite P) w) :
    ∃ w' : LegalRoot U (ZMod q) b, w'.toFun = w := by
  rcases h with ⟨hinj, σ, hσ⟩
  refine ⟨⟨w, hinj, σ, ?_⟩, rfl⟩
  intro r
  simpa [hostPartite] using hσ r

/-- The key of a legal root: its part permutation and the coordinates of the
root images.  This is injective because the prescribed part of each root is
determined by the permutation. -/
noncomputable def legalRootKey {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) (b : ℕ) (w : LegalRoot U F b) :
    Equiv.Perm (Fin k) × (U.R → (Fin b → F)) :=
  (w.sigma, fun r => (w.toFun r).2)

lemma legalRootKey_injective {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) (b : ℕ) :
    Function.Injective (legalRootKey U F b) := by
  intro w v h
  obtain ⟨wt, wi, ws, wp⟩ := w
  obtain ⟨vt, vi, vs, vp⟩ := v
  simp only [legalRootKey, Prod.mk.injEq] at h
  obtain ⟨hσ, hc⟩ := h
  subst hσ
  have ht : wt = vt := by
    funext r
    exact Prod.ext (by rw [wp r, vp r]) (congrFun hc r)
  subst ht
  rfl

noncomputable instance legalRootFintype {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) [Fintype F] (b : ℕ) :
    Fintype (LegalRoot U F b) :=
  Fintype.ofInjective (legalRootKey U F b) (legalRootKey_injective U F b)

/-- The number of legal root positions is at most `k!` times the number of
choices of one `b`-vector in each prescribed part. -/
lemma legalRoot_card_le {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) [Fintype F] (b : ℕ) :
    Fintype.card (LegalRoot U F b) ≤
      Nat.factorial k * (Fintype.card F ^ b) ^ Fintype.card U.R := by
  classical
  have h := Fintype.card_le_of_injective (legalRootKey U F b)
    (legalRootKey_injective U F b)
  calc
    Fintype.card (LegalRoot U F b) ≤
        Fintype.card (Equiv.Perm (Fin k) × (U.R → (Fin b → F))) := h
    _ = Nat.factorial k * (Fintype.card F ^ b) ^ Fintype.card U.R := by
      rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
        Fintype.card_fun]
      simp [Fintype.card_fin]

lemma legalRoot_card_le_pow {k : ℕ} (U : PartiteRootedKHypergraph k)
    (F : Type) [Fintype F] (b : ℕ) :
    Fintype.card (LegalRoot U F b) ≤
      Nat.factorial k * Fintype.card F ^ (b * Fintype.card U.R) := by
  calc
    Fintype.card (LegalRoot U F b) ≤
        Nat.factorial k * (Fintype.card F ^ b) ^ Fintype.card U.R :=
      legalRoot_card_le U F b
    _ = Nat.factorial k * Fintype.card F ^ (b * Fintype.card U.R) := by
      rw [← pow_mul]

/-- Averaging `C_w^s` is invariant under relabelling the parts of `U`. -/
lemma momentAverage_partPermute {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (σ : Equiv.Perm (Fin k))
    (hσ : ∀ r : U.R, (w r).1 = σ (U.part r.1)) :
    momentAverage (a := a) (D := D) U w s =
      momentAverage (a := a) (D := D) (partPermute U σ) w s := by
  classical
  simp only [momentAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro P _
  rw [Cw_partPermute]

/-- The moment estimate of Lemma 3.3 for legal root positions. -/
theorem momentAverage_le_legal {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : LegalRoot U F b)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace U s, (eτ U s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1)
    (P₀ : HostParams F k b a D) :
    momentAverage (a := a) (D := D) U w.toFun s ≤
      (Fintype.card (TypeSpace U s) : ℚ) := by
  classical
  have hEq := momentAverage_partPermute (a := a) (D := D) (s := s) U w.toFun
    w.sigma w.part_eq
  rw [hEq]
  have hbal' : BalancedK (partPermute U w.sigma).toRootedKHypergraph a b := by
    simpa [partPermute] using hbal
  have hq' : ∀ τ : TypeSpace (partPermute U w.sigma) s,
      (eτ (partPermute U w.sigma) s τ).choose 2 < Fintype.card F := hq
  have hD' : ∀ τ : TypeSpace (partPermute U w.sigma) s,
      eτ (partPermute U w.sigma) s τ ≤ D + 1 := hD
  have hm := momentAverage_le (partPermute U w.sigma) a D w.toFun
    hbal' w.part_eq hs hq' hD' P₀
  simpa [partPermute] using hm

/-- Number of legal root positions with `C_w > P_*`. -/
noncomputable def badRootCount {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (U : PartiteRootedKHypergraph k)
    (P : HostParams F k b a D) (Pstar : ℕ) : ℕ :=
  (Finset.univ.filter (fun w : LegalRoot U F b =>
    Pstar < Cw U (hostPartite P) w.toFun)).card

/-- Expected number of bad roots, using the moment bound and the
`P_*`/`q/2` dichotomy. -/
theorem expected_badRoots_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
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
        (badRootCount U P Pstar : ℚ)) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≤
      (Fintype.card (LegalRoot U F b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) /
          ((Fintype.card F : ℚ) / 2) ^ s) := by
  classical
  haveI : Nonempty (HostParams F k b a D) :=
    ⟨⟨fun _ => 0⟩⟩
  let C : HostParams F k b a D → LegalRoot U F b → ℕ :=
    fun P w => Cw U (hostPartite P) w.toFun
  have h : (∑ P : HostParams F k b a D, (badCount C Pstar P : ℚ)) /
        (Fintype.card (HostParams F k b a D) : ℚ) ≤
      (Fintype.card (LegalRoot U F b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) /
          ((Fintype.card F : ℚ) / 2) ^ s) := by
    apply expectation_badCount_le (C := C) (P := Pstar)
      (ε := (Fintype.card (TypeSpace U s) : ℚ) /
        ((Fintype.card F : ℚ) / 2) ^ s)
    intro w
    have hmom := momentAverage_le_legal (a := a) (D := D) U w
      hbal hs hq hD P₀
    have hmark := markov_pow
      (fun P => Cw U (hostPartite P) w.toFun) s hs
      (Fintype.card (TypeSpace U s) : ℚ)
      (by simpa [momentAverage] using hmom)
      ((Fintype.card F : ℚ) / 2) (by positivity)
    refine le_trans ?_ hmark
    apply prob_mono
    intro P hP
    change Pstar < Cw U (hostPartite P) w.toFun at hP
    rcases hdich P w with hle | hge
    · exfalso
      omega
    · exact hge
  simpa [badRootCount, badCount, C] using h

lemma prob_badRoots_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
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
    prob (fun P : HostParams F k b a D =>
        0 < badRootCount U P Pstar) ≤
      (Fintype.card (LegalRoot U F b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) /
          ((Fintype.card F : ℚ) / 2) ^ s) := by
  classical
  haveI : Nonempty (HostParams F k b a D) :=
    ⟨⟨fun _ => 0⟩⟩
  have h1 := prob_pos_le_expect
    (fun P : HostParams F k b a D => badRootCount U P Pstar)
  have h2 := expected_badRoots_le U a D Pstar hbal hs hq hD hPstar hdich P₀
  refine h1.trans ?_
  exact h2

lemma exists_zero_badRoots {F : Type} [Field F] [Fintype F] [DecidableEq F]
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
    (P₀ : HostParams F k b a D)
    (hsmall : (Fintype.card (LegalRoot U F b) : ℚ) *
        ((Fintype.card (TypeSpace U s) : ℚ) /
          ((Fintype.card F : ℚ) / 2) ^ s) < 1) :
    ∃ P : HostParams F k b a D, badRootCount U P Pstar = 0 := by
  classical
  haveI : Nonempty (HostParams F k b a D) :=
    ⟨⟨fun _ => 0⟩⟩
  by_contra h
  push_neg at h
  have hpos : ∀ P : HostParams F k b a D,
      0 < badRootCount U P Pstar := fun P =>
    Nat.pos_of_ne_zero (h P)
  have hprob : prob (fun P : HostParams F k b a D =>
      0 < badRootCount U P Pstar) = 1 := by
    simp [prob, hpos]
  have hle := prob_badRoots_le U a D Pstar hbal hs hq hD hPstar hdich P₀
  rw [hprob] at hle
  linarith

end Erdos571_hypergraph
