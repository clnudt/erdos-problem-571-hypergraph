import Erdos571_hypergraph_L10_Main

namespace Erdos571_hypergraph

/-- The complete `k`-uniform hypergraph on `k+1` vertices, i.e.
`K_{k+1}^{(k)}`. -/
noncomputable abbrev completeK (k : ℕ) : FiniteKHypergraph k where
  V := Fin (k + 1)
  graph :=
    { edges := (Finset.univ : Finset (Fin (k + 1))).powersetCard k
      edges_card := by
        intro e he
        exact (Finset.mem_powersetCard.mp he).2 }

lemma completeK_edges_nonempty (k : ℕ) : (completeK k).graph.edges.Nonempty := by
  classical
  unfold completeK
  exact Finset.powersetCard_nonempty.mpr (by simp)

/-- Any `k`-graph on `n` vertices has at most `n.choose k` edges. -/
lemma card_edges_le_choose {k : ℕ} {H : KHypergraph k (Fin n)} :
    H.edges.card ≤ n.choose k := by
  classical
  calc
    H.edges.card ≤ ((Finset.univ : Finset (Fin n)).powersetCard k).card := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, H.edges_card e he⟩
    _ = n.choose k := by
      rw [Finset.card_powersetCard]
      simp

/-- Upper bound for the Turán number. -/
lemma turanNumber_le_choose {k : ℕ} (F : FiniteKHypergraph k)
    (hF : F.graph.edges.Nonempty) (n : ℕ) :
    turanNumber F n ≤ n.choose k := by
  classical
  unfold turanNumber
  apply csSup_le
  · refine ⟨0, ?_⟩
    refine ⟨⟨∅, ?_⟩, ?_, rfl⟩
    · intro e he
      simp at he
    · rintro ⟨f, hf⟩
      obtain ⟨e, he⟩ := hF
      have := hf e he
      simpa using this
  · rintro m ⟨H, -, rfl⟩
    exact card_edges_le_choose

/-- The complete `k`-partite `k`-graph with parts of size `m`. -/
noncomputable abbrev completePartite (k m : ℕ) :
    KHypergraph k (Fin k × Fin m) where
  edges := (Finset.univ : Finset (Fin k → Fin m)).image
    (fun z => Finset.univ.image (fun i => (i, z i)))
  edges_card := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, -, rfl⟩
    rw [Finset.card_image_of_injOn]
    · simp
    · intro i _ j _ h
      exact (Prod.ext_iff.mp h).1

lemma mem_completePartite_edge {k m : ℕ} {e : Finset (Fin k × Fin m)} :
    e ∈ (completePartite k m).edges ↔
      ∃ z : Fin k → Fin m, e = Finset.univ.image (fun i => (i, z i)) := by
  classical
  constructor
  · intro he
    change e ∈ (Finset.univ : Finset (Fin k → Fin m)).image
      (fun z => Finset.univ.image (fun i => (i, z i))) at he
    rcases Finset.mem_image.mp he with ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    change (Finset.univ.image (fun i => (i, z i))) ∈
      (Finset.univ : Finset (Fin k → Fin m)).image
        (fun z => Finset.univ.image (fun i => (i, z i)))
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ _, rfl⟩

lemma completePartite_edge_fst {k m : ℕ} {e : Finset (Fin k × Fin m)}
    (he : e ∈ (completePartite k m).edges) :
    ∀ a ∈ e, ∀ b ∈ e, a.1 = b.1 → a = b := by
  classical
  rw [mem_completePartite_edge] at he
  obtain ⟨z, rfl⟩ := he
  intro a ha b hb hab
  rw [Finset.mem_image] at ha hb
  obtain ⟨i, -, rfl⟩ := ha
  obtain ⟨j, -, rfl⟩ := hb
  have hij : i = j := by
    simpa using hab
  subst hij
  rfl

lemma completePartite_free {k m : ℕ} (hk : 2 ≤ k) :
    ¬ IsCopy (completeK k).graph (completePartite k m) := by
  classical
  rintro ⟨f, hf⟩
  have hcard : Fintype.card (Fin k) < Fintype.card (Fin (k + 1)) := by
    simp
  obtain ⟨x, y, hxy, hsame⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun v : Fin (k + 1) => (f v).1) hcard
  have hz : ∃ z : Fin (k + 1), z ≠ x ∧ z ≠ y := by
    by_contra h
    push_neg at h
    have hsub : (Finset.univ : Finset (Fin (k + 1))) ⊆ {x, y} := by
      intro z _
      by_cases hx : z = x
      · simp [hx]
      · simp [h z hx]
    have hle := Finset.card_le_card hsub
    have h2 : ({x, y} : Finset (Fin (k + 1))).card ≤ 2 := by
      simpa using Finset.card_insert_le x ({y} : Finset (Fin (k + 1)))
    simp at hle
    omega
  obtain ⟨z, hzx, hzy⟩ := hz
  let s : Finset (Fin (k + 1)) := Finset.univ.erase z
  have hscard : s.card = k := by
    dsimp [s]
    rw [Finset.card_erase_of_mem (Finset.mem_univ z)]
    simp
  have hsmem : s ∈ (completeK k).graph.edges := by
    unfold completeK
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hscard⟩
  have hedge := hf s hsmem
  have hx : x ∈ s := by
    dsimp [s]
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hzx, Finset.mem_univ x⟩
  have hy : y ∈ s := by
    dsimp [s]
    rw [Finset.mem_erase]
    exact ⟨Ne.symm hzy, Finset.mem_univ y⟩
  have hx_mem : f x ∈ s.map f := Finset.mem_map.mpr ⟨x, hx, rfl⟩
  have hy_mem : f y ∈ s.map f := Finset.mem_map.mpr ⟨y, hy, rfl⟩
  have hfeq : f x = f y :=
    completePartite_edge_fst hedge (f x) hx_mem (f y) hy_mem hsame
  exact hxy (f.injective hfeq)

lemma completeK_vertex_covered (k : ℕ) (hk : 2 ≤ k) :
    ∀ v : (completeK k).V, ∃ e ∈ (completeK k).graph.edges, v ∈ e := by
  classical
  intro v
  let w : Fin (k + 1) := if v = 0 then ⟨1, by omega⟩ else 0
  have hwv : w ≠ v := by
    dsimp [w]
    split_ifs with hv
    · subst v
      intro h
      have := congrArg Fin.val h
      simp at this
    · intro h
      exact hv h.symm
  refine ⟨Finset.univ.erase w, ?_, ?_⟩
  · unfold completeK
    rw [Finset.mem_powersetCard]
    constructor
    · exact Finset.subset_univ _
    · rw [Finset.card_erase_of_mem (Finset.mem_univ w)]
      simp
  · rw [Finset.mem_erase]
    exact ⟨Ne.symm hwv, Finset.mem_univ v⟩

lemma completePartite_card (k m : ℕ) :
    (completePartite k m).edges.card = m ^ k := by
  classical
  unfold completePartite
  rw [Finset.card_image_of_injOn]
  · simp [Fintype.card_fun]
  · intro z _ z' _ h
    change Finset.univ.image (fun j => (j, z j)) =
      Finset.univ.image (fun j => (j, z' j)) at h
    funext i
    have hmem : (i, z i) ∈ Finset.univ.image (fun j => (j, z j)) :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    rw [h] at hmem
    rcases Finset.mem_image.mp hmem with ⟨j, -, hji⟩
    have hji' : (i, z i) = (j, z' j) := hji.symm
    have hij : i = j := (Prod.ext_iff.mp hji').1
    subst hij
    exact (Prod.ext_iff.mp hji').2

lemma turanNumber_completeK_ge (k m : ℕ) (hk : 2 ≤ k) :
    m ^ k ≤ turanNumber (completeK k) (k * m) := by
  classical
  have hcard : Fintype.card (Fin k × Fin m) = k * m := by simp
  let e : Fin k × Fin m ≃ Fin (k * m) := Fintype.equivFinOfCardEq hcard
  let H := mapKHypergraph e (completePartite k m)
  have hfree : ¬ IsCopy (completeK k).graph H := by
    intro hc
    exact completePartite_free hk
      ((isCopy_mapKHypergraph_iff e (completeK k).graph
        (completePartite k m)).mp hc)
  have hc : H.edges.card = m ^ k := by
    rw [card_mapKHypergraph, completePartite_card]
  rw [← hc]
  exact le_turanNumber (completeK k) ⟨H, hfree, rfl⟩

lemma turanNumber_completeK_ge_fin {k n : ℕ} (hk : 2 ≤ k) (hn : k ≤ n) :
    (n / k) ^ k ≤ turanNumber (completeK k) n := by
  classical
  let m := n / k
  have hmpos : 0 < m := Nat.div_pos hn (by omega)
  have hkm : k * m ≤ n := Nat.mul_div_le n k
  have hcard : Fintype.card (Fin k × Fin m) = k * m := by simp
  let e1 : Fin k × Fin m ≃ Fin (k * m) := Fintype.equivFinOfCardEq hcard
  let H1 := mapKHypergraph e1 (completePartite k m)
  have hfree1 : ¬ IsCopy (completeK k).graph H1 := by
    intro hc
    exact completePartite_free hk
      ((isCopy_mapKHypergraph_iff e1 (completeK k).graph
        (completePartite k m)).mp hc)
  have hcard1 : H1.edges.card = m ^ k := by
    rw [card_mapKHypergraph, completePartite_card]
  have hpos : 0 < k * m := Nat.mul_pos (by omega) hmpos
  letI : Nonempty (Fin (k * m)) := ⟨⟨0, hpos⟩⟩
  let e2 : Fin (k * m) ↪ Fin n := Fin.castLEEmb hkm
  let H2 := mapKHypergraphEmb e2 H1
  have hfree2 : ¬ IsCopy (completeK k).graph H2 := by
    intro hc
    exact hfree1 (isCopy_mapEmb_of_no_isolated (completeK k).graph
      (completeK_vertex_covered k hk) e2 H1 hc)
  have hcard2 : H2.edges.card = H1.edges.card :=
    card_mapKHypergraphEmb e2 H1
  calc
    (n / k) ^ k = H2.edges.card := by rw [hcard2, hcard1]
    _ ≤ turanNumber (completeK k) n :=
      le_turanNumber (completeK k) ⟨H2, hfree2, rfl⟩

/-- The `r = 0` case of Theorem 1.2. -/
theorem main_zero (k : ℕ) (hk : 2 ≤ k) :
    RealizesExponent (completeK k) (k : ℝ) := by
  classical
  apply realizesExponent_of_eventually (completeK k)
  · -- lower bound
    refine ⟨(1 / (4 * (k : ℝ))) ^ k, ?_, ?_⟩
    · positivity
    · filter_upwards [Filter.eventually_ge_atTop (4 * k)] with n hn
      have hn4 : 4 * k ≤ n := hn
      have hk_le : k ≤ n := by omega
      have hge := turanNumber_completeK_ge_fin hk hk_le
      let m := n / k
      have hm1 : 1 ≤ m := by
        dsimp [m]
        exact Nat.div_pos (by omega) (by omega)
      have hdecomp : n = k * m + n % k := by
        dsimp [m]
        exact (Nat.div_add_mod n k).symm
      have hlt : (n : ℝ) < (2 * (k : ℝ)) * m := by
        have hmod : n % k < k := Nat.mod_lt n (by omega)
        have h1 : n < k * (m + 1) := by
          rw [hdecomp, Nat.mul_add, Nat.mul_one]
          omega
        have h2 : k * (m + 1) ≤ 2 * k * m := by nlinarith
        exact_mod_cast lt_of_lt_of_le h1 h2
      have hm_ge : (n : ℝ) / (4 * (k : ℝ)) ≤ (m : ℝ) := by
        have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
        have h4k : (0 : ℝ) < 4 * (k : ℝ) := by positivity
        have hmid : (n : ℝ) / (2 * (k : ℝ)) < m := by
          rw [div_lt_iff₀ h2k]
          nlinarith
        have hle : (n : ℝ) / (4 * (k : ℝ)) ≤
            (n : ℝ) / (2 * (k : ℝ)) := by
          apply div_le_div_of_nonneg_left (by positivity) h2k
          nlinarith
        linarith
      have hpow : ((n : ℝ) / (4 * (k : ℝ))) ^ k ≤ (m : ℝ) ^ k :=
        pow_le_pow_left₀ (by positivity) hm_ge k
      have hfin : (m : ℝ) ^ k ≤
          (turanNumber (completeK k) n : ℝ) := by
        exact_mod_cast hge
      have hc : (1 / (4 * (k : ℝ))) ^ k * (n : ℝ) ^ k =
          ((n : ℝ) / (4 * (k : ℝ))) ^ k := by
        rw [div_pow]
        ring_nf
        rw [show (1 / 4 : ℝ) = 4⁻¹ by norm_num]
        ring
      rw [Real.rpow_natCast, hc]
      exact hpow.trans hfin
  · -- upper bound
    refine ⟨1, ?_⟩
    filter_upwards with n
    have h1 : turanNumber (completeK k) n ≤ n.choose k :=
      turanNumber_le_choose (completeK k) (completeK_edges_nonempty k) n
    have h2 : n.choose k ≤ n ^ k := Nat.choose_le_pow n k
    have h3 : (turanNumber (completeK k) n : ℝ) ≤ (n : ℝ) ^ k := by
      exact_mod_cast h1.trans h2
    simpa [Real.rpow_natCast] using h3

/-- Theorem 1.2 in full: the `r = 0` case and the `0 < r ≤ 1` case. -/
theorem main_all (k : ℕ) (hk : 2 ≤ k) :
    (∃ F : FiniteKHypergraph k, RealizesExponent F (k : ℝ)) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → a ≤ b →
      ∃ F : FiniteKHypergraph k,
        RealizesExponent F ((k : ℝ) - (a : ℝ) / b)) := by
  constructor
  · exact ⟨completeK k, main_zero k hk⟩
  · intro a b ha0 hb ha
    obtain ⟨B, Pstar, h⟩ := main hk ha0 hb ha
    exact ⟨FkrFinite hk B (Pstar + 1) (by omega), h⟩

/-- Theorem 1.2 with a literal rational parameter `r : ℚ`. -/
theorem main_rat (k : ℕ) (hk : 2 ≤ k) (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ F : FiniteKHypergraph k, RealizesExponent F ((k : ℝ) - (r : ℝ)) := by
  by_cases hr : r = 0
  · rw [hr]
    exact ⟨completeK k, by simpa using main_zero k hk⟩
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    let a : ℕ := r.num.natAbs
    let b : ℕ := r.den
    have hnumpos : 0 < r.num := Rat.num_pos.mpr hrpos
    have ha0 : 0 < a := by
      dsimp [a]
      omega
    have hb : 0 < b := by
      dsimp [b]
      exact r.den_pos
    have hle : r.num ≤ (r.den : ℤ) := by
      have hq : (r.num : ℚ) / (r.den : ℚ) ≤ 1 := by
        calc
          (r.num : ℚ) / (r.den : ℚ) = r := Rat.num_div_den r
          _ ≤ 1 := hr1
      exact_mod_cast (div_le_one (by exact_mod_cast r.den_pos)).mp hq
    have ha : a ≤ b := by
      dsimp [a, b]
      omega
    obtain ⟨B, Pstar, h⟩ := main hk ha0 hb ha
    refine ⟨FkrFinite hk B (Pstar + 1) (by omega), ?_⟩
    convert h using 2
    congr 1
    rw [Rat.cast_def]
    have hcast : (a : ℝ) = (r.num : ℝ) := by
      dsimp [a]
      rw [← Int.cast_natCast (R := ℝ)]
      rw [Int.natCast_natAbs]
      rw [abs_of_nonneg (Rat.num_nonneg.mpr hr0)]
    rw [← hcast]

end Erdos571_hypergraph
