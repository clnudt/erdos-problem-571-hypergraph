import Erdos571_hypergraph_L2
import Erdos571_hypergraph_L2_PolySpace
import Erdos571_hypergraph_L2_PolySurj

namespace Erdos571_hypergraph

/-- The zero monomial (constant term). -/
def zeroMonomial (n D : ℕ) : MonomialIndex n D :=
  ⟨0, by simp⟩

/-- The coefficient vector of a constant polynomial. -/
noncomputable def constCoeff {F : Type} [Field F] (n D : ℕ) (c : F) :
    PolyCoeff F n D := by
  classical
  exact fun s => if s = zeroMonomial n D then c else 0

lemma evalPolyAt_constCoeff {F : Type} [Field F] {n D : ℕ}
    (z : Fin n → F) (c : F) :
    evalPolyAt (D := D) z (constCoeff (F := F) n D c) = c := by
  classical
  rw [evalPolyAt]
  rw [Finset.sum_eq_single (zeroMonomial n D)]
  · unfold constCoeff
    rw [if_pos rfl]
    simp [monomialEval, zeroMonomial]
  · intro b _ hb
    simp [constCoeff, hb]
  · intro h
    simp at h

/-- Evaluation at a single point, as an additive homomorphism. -/
noncomputable def evalAtPoint {F : Type} [Field F] {n D : ℕ}
    (z : Fin n → F) : PolyCoeff F n D →+ F where
  toFun f := evalPolyAt (D := D) z f
  map_zero' := by
    simp [evalPolyAt]
  map_add' f g := by
    simp [evalPolyAt, add_mul, Finset.sum_add_distrib]

lemma evalAtPoint_surjective {F : Type} [Field F] {n D : ℕ}
    (z : Fin n → F) : Function.Surjective (evalAtPoint (D := D) z) := by
  intro c
  refine ⟨constCoeff (F := F) n D c, ?_⟩
  exact evalPolyAt_constCoeff z c

/-- The same evaluation, codomain `Fin 1 → F`, for the counting lemma. -/
noncomputable def evalAtPointHom {F : Type} [Field F] {n D : ℕ}
    (z : Fin n → F) : PolyCoeff F n D →+ (Fin 1 → F) where
  toFun f _ := evalPolyAt (D := D) z f
  map_zero' := by
    funext i
    simp [evalPolyAt]
  map_add' f g := by
    funext i
    simp [evalPolyAt, add_mul, Finset.sum_add_distrib]

lemma evalAtPointHom_surjective {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n D : ℕ} (z : Fin n → F) :
    Function.Surjective (evalAtPointHom (D := D) z) := by
  intro y
  refine ⟨constCoeff (F := F) n D (y 0), ?_⟩
  funext i
  have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
  subst hi
  simpa [evalAtPointHom] using evalPolyAt_constCoeff (D := D) z (y 0)

/-- The number of coefficient vectors vanishing at one point is
`|P| / q`. -/
theorem card_ker_evalAtPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n D : ℕ} (z : Fin n → F) :
    (Finset.univ.filter (fun f : PolyCoeff F n D =>
        evalAtPoint (D := D) z f = 0)).card * Fintype.card F =
      Fintype.card (PolyCoeff F n D) := by
  classical
  have h := interpolation_count 1
    (evalAtPointHom (F := F) (n := n) (D := D) z)
    (evalAtPointHom_surjective z)
  have hfilter : (Finset.univ.filter (fun f : PolyCoeff F n D =>
      evalAtPointHom (F := F) (n := n) (D := D) z f = 0)) =
      (Finset.univ.filter (fun f : PolyCoeff F n D =>
        evalAtPoint (D := D) z f = 0)) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      have h0 := congrFun h 0
      change evalPolyAt z f = 0
      simpa [evalAtPointHom] using h0
    · intro h
      funext i
      change evalPolyAt z f = 0
      exact h
  simpa [hfilter] using h

/-- Simultaneous evaluation of `a` polynomials at one point. -/
noncomputable def evalTupleAtPoint {F : Type} [Field F] {n D a : ℕ}
    (z : Fin n → F) : (Fin a → PolyCoeff F n D) →+ (Fin a → F) where
  toFun f j := evalAtPoint (D := D) z (f j)
  map_zero' := by
    funext j
    simp [evalAtPoint]
  map_add' f g := by
    funext j
    simp [evalAtPoint, map_add]

lemma evalTupleAtPoint_surjective {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n D a : ℕ} (z : Fin n → F) :
    Function.Surjective (evalTupleAtPoint (D := D) (a := a) z) := by
  intro y
  refine ⟨fun j => constCoeff (F := F) n D (y j), ?_⟩
  funext j
  change evalPolyAt z (constCoeff n D (y j)) = y j
  exact evalPolyAt_constCoeff (D := D) z (y j)

/-- The number of `a`-tuples of coefficient vectors all vanishing at one
point is `|P|^a / q^a`. -/
theorem card_simultaneous_zero {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n D a : ℕ} (z : Fin n → F) :
    (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        ∀ j : Fin a, evalAtPoint (D := D) z (f j) = 0)).card *
        Fintype.card F ^ a =
      Fintype.card (Fin a → PolyCoeff F n D) := by
  classical
  have h := interpolation_count a
    (evalTupleAtPoint (F := F) (n := n) (D := D) (a := a) z)
    (evalTupleAtPoint_surjective z)
  have hfilter :
      (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        evalTupleAtPoint (F := F) (n := n) (D := D) (a := a) z f = 0)) =
      (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        ∀ j : Fin a, evalAtPoint (D := D) z (f j) = 0)) := by
    ext f
    simp [evalTupleAtPoint, funext_iff]
  simpa [hfilter] using h

/-- One polynomial vanishing at `m` distinct points: the number of coefficient
vectors is `|P| / q^m`.  This is the form used per polynomial in Lemma
3.3. -/
theorem card_zero_at_points {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n m D : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hD : m ≤ D + 1) :
    (Finset.univ.filter (fun f : PolyCoeff F n D =>
        ∀ i : Fin m, evalPolyAt (D := D) (z i) f = 0)).card *
        Fintype.card F ^ m =
      Fintype.card (PolyCoeff F n D) := by
  classical
  have h := multivariate_interpolation_count_full z hz hq hD
  have hfilter :
      (Finset.univ.filter (fun f : PolyCoeff F n D =>
        evalPoly (F := F) (n := n) (m := m) (D := D) z f = 0)) =
      (Finset.univ.filter (fun f : PolyCoeff F n D =>
        ∀ i : Fin m, evalPolyAt (D := D) (z i) f = 0)) := by
    ext f
    simp [evalPoly, funext_iff]
  simpa [hfilter] using h

/-- Tuples all of whose entries lie in a fixed finite set. -/
noncomputable def piSubtypeEquiv {P : Type} (S : Finset P) (a : ℕ) :
    {f : Fin a → P // ∀ j : Fin a, f j ∈ S} ≃
      (Fin a → {x : P // x ∈ S}) where
  toFun f j := ⟨f.1 j, f.2 j⟩
  invFun g := ⟨fun j => (g j).1, fun j => (g j).2⟩
  left_inv f := by
    cases f
    rfl
  right_inv g := by
    funext j
    exact Subtype.ext rfl

lemma card_pi_subtype {P : Type} [Fintype P] [DecidableEq P]
    (S : Finset P) (a : ℕ) :
    (Finset.univ.filter (fun f : Fin a → P => ∀ j : Fin a, f j ∈ S)).card =
      S.card ^ a := by
  classical
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (piSubtypeEquiv S a)]
  rw [Fintype.card_fun]
  simp

/-- The number of `a`-tuples of coefficient vectors all vanishing at `m`
distinct points is `|P|^a / q^(a m)`. -/
theorem card_tuple_zero_at_points {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {n m D a : ℕ} [DecidableEq (PolyCoeff F n D)]
    (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hD : m ≤ D + 1) :
    (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        ∀ j : Fin a, ∀ i : Fin m,
          evalPolyAt (D := D) (z i) (f j) = 0)).card *
        Fintype.card F ^ (a * m) =
      Fintype.card (Fin a → PolyCoeff F n D) := by
  classical
  let S : Finset (PolyCoeff F n D) :=
    Finset.univ.filter (fun f : PolyCoeff F n D =>
      ∀ i : Fin m, evalPolyAt (D := D) (z i) f = 0)
  have hS : S.card * Fintype.card F ^ m =
      Fintype.card (PolyCoeff F n D) :=
    card_zero_at_points z hz hq hD
  have hfilter :
      (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        ∀ j : Fin a, ∀ i : Fin m,
          evalPolyAt (D := D) (z i) (f j) = 0)) =
      (Finset.univ.filter (fun f : Fin a → PolyCoeff F n D =>
        ∀ j : Fin a, f j ∈ S)) := by
    ext f
    simp [S]
  rw [hfilter, card_pi_subtype S a]
  calc
    S.card ^ a * Fintype.card F ^ (a * m) =
        (S.card * Fintype.card F ^ m) ^ a := by
          conv_rhs => rw [mul_pow, ← pow_mul, Nat.mul_comm m a]
    _ = Fintype.card (PolyCoeff F n D) ^ a := by rw [hS]
    _ = Fintype.card (Fin a → PolyCoeff F n D) := by
          rw [Fintype.card_fun]
          simp

end Erdos571_hypergraph
