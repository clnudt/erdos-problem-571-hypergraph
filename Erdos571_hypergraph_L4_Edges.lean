import Erdos571_hypergraph_L3_Expectation
import Erdos571_hypergraph_L3_Host

set_option maxHeartbeats 1000000

namespace Erdos571_hypergraph

lemma hostEdges_card_eq {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D) :
    (hostEdges P).card =
      (Finset.univ.filter (fun t : Fin k → (Fin b → F) =>
        ∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0)).card := by
  classical
  unfold hostEdges
  rw [Finset.card_image_of_injOn]
  intro z _ w _ h
  exact hostEdge_injective h

lemma card_zero_params_at_tuple {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (t : Fin k → (Fin b → F)) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0)).card *
        Fintype.card F ^ a =
      Fintype.card (HostParams F k b a D) := by
  classical
  have h := card_params_zero_on_points (F := F) (k := k) (b := b)
    (m := 1) (D := D) (a := a)
    (fun _ : Fin 1 => flattenTuple t)
    (by
      intro x y _
      exact Subsingleton.elim x y)
    (by simpa using Fintype.card_pos_iff.mpr ⟨(0 : F)⟩)
    (by omega)
  rw [show (Finset.univ.filter (fun P : HostParams F k b a D =>
      ∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0)) =
    (Finset.univ.filter (fun P : HostParams F k b a D =>
      ∀ j : Fin a, ∀ i : Fin 1,
        evalPolyAt (flattenTuple t) (P.coeffs j) = 0)) by
    apply Finset.filter_congr
    intro P _
    simp [evalAtTuple]]
  simpa [Nat.mul_one] using h

lemma sum_edgeCount_mul {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} :
    (∑ P : HostParams F k b a D, (hostEdges P).card) *
        Fintype.card F ^ a =
      Fintype.card F ^ (b * k) *
        Fintype.card (HostParams F k b a D) := by
  classical
  have hcard : ∀ P : HostParams F k b a D, (hostEdges P).card =
      (Finset.univ.filter (fun t : Fin k → (Fin b → F) =>
        ∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0)).card :=
    fun P => hostEdges_card_eq P
  simp_rw [hcard, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [Finset.sum_mul]
  have hinner : ∀ t : Fin k → (Fin b → F),
      (∑ P : HostParams F k b a D,
        (if (∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0) then 1 else 0)) *
        Fintype.card F ^ a =
      Fintype.card (HostParams F k b a D) := by
    intro t
    have h := card_zero_params_at_tuple (F := F) (k := k) (b := b)
      (a := a) (D := D) t
    rw [← h]
    congr 1
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  calc
    ∑ t : Fin k → (Fin b → F),
        (∑ P : HostParams F k b a D,
          (if (∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0) then 1 else 0)) *
          Fintype.card F ^ a =
      ∑ _t : Fin k → (Fin b → F),
        Fintype.card (HostParams F k b a D) := by
      apply Finset.sum_congr rfl
      intro t _
      exact hinner t
    _ = Fintype.card F ^ (b * k) *
        Fintype.card (HostParams F k b a D) := by
      rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
      congr 1
      rw [Fintype.card_fun, Fintype.card_fun]
      simp only [Fintype.card_fin]
      rw [← pow_mul, Nat.mul_comm]

lemma edgeAverage_eq {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} :
    (∑ P : HostParams F k b a D, ((hostEdges P).card : ℚ)) /
        (Fintype.card (HostParams F k b a D) : ℚ) =
      (Fintype.card F : ℚ) ^ (b * k) /
        (Fintype.card F : ℚ) ^ a := by
  classical
  have hH : (Fintype.card (HostParams F k b a D) : ℚ) ≠ 0 := by
    have : 0 < Fintype.card (HostParams F k b a D) :=
      Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0⟩⟩
    exact_mod_cast (ne_of_gt this)
  have hq : (Fintype.card F : ℚ) ^ a ≠ 0 := by positivity
  have h := sum_edgeCount_mul (F := F) (k := k) (b := b) (a := a) (D := D)
  have hQ : ((∑ P : HostParams F k b a D, (hostEdges P).card : ℕ) : ℚ) *
      (Fintype.card F : ℚ) ^ a =
      (Fintype.card F : ℚ) ^ (b * k) *
        (Fintype.card (HostParams F k b a D) : ℚ) := by
    exact_mod_cast h
  rw [div_eq_div_iff hH hq]
  rw [Nat.cast_sum] at hQ
  exact hQ

lemma edgeAverage_eq_pow {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (ha : a ≤ b * k) :
    (∑ P : HostParams F k b a D, ((hostEdges P).card : ℚ)) /
        (Fintype.card (HostParams F k b a D) : ℚ) =
      (Fintype.card F : ℚ) ^ (b * k - a) := by
  rw [edgeAverage_eq,
    pow_sub₀ (Fintype.card F : ℚ)
      (by exact_mod_cast (ne_of_gt (Fintype.card_pos_iff.mpr ⟨(0 : F)⟩))) ha,
    div_eq_mul_inv]

lemma edgeCount_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D) :
    (hostEdges P).card ≤ Fintype.card F ^ (b * k) := by
  classical
  rw [hostEdges_card_eq P]
  calc
    (Finset.univ.filter (fun t : Fin k → (Fin b → F) =>
        ∀ j : Fin a, evalAtTuple (P.coeffs j) t = 0)).card ≤
        (Finset.univ : Finset (Fin k → (Fin b → F))).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card (Fin k → (Fin b → F)) := Finset.card_univ
    _ = Fintype.card F ^ (b * k) := by
      rw [Fintype.card_fun, Fintype.card_fun]
      simp only [Fintype.card_fin]
      rw [← pow_mul, Nat.mul_comm]

end Erdos571_hypergraph
