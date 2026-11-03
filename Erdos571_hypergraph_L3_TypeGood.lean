import Erdos571_hypergraph_L3_TupleType
import Erdos571_hypergraph_L3_TypeEmbeddingOf

namespace Erdos571_hypergraph

/-- The part permutation of every copy fixes the parts occupied by roots. -/
def RootFixed {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) : Prop :=
  ∀ (i : Fin s) (r : U.R), τ.2 i (U.part r.1) = U.part r.1

lemma rootFixed_tupleType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) :
    RootFixed U s (tupleType U X w s φ) := by
  intro i r
  have hroot : (φ i).2.toFun r.1 = w r :=
    (φ i).2.root_compat r.1 r.2
  have hpart := (φ i).2.part_compat r.1
  have hX : X.part ((φ i).2.toFun r.1) = U.part r.1 := by
    rw [hroot]
    exact hwpart r
  simpa [tupleType] using hpart.symm.trans hX

/-- Every edge of `H_τ` meets each `typeVertexPartOf` fibre exactly once. -/
def EdgeTransversal {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (h : PartConsistent U s τ) : Prop :=
  ∀ (i : Fin s) {e : Finset U.V}, e ∈ U.G.edges →
    ∀ j : Fin k, ∃! v : TypeVertex U τ,
      v ∈ typeEdgeSet U s τ i e ∧
        typeVertexPartOf τ (blockPartOf U s τ h) v = j

/-- The full goodness condition for a type: roots fixed and every edge a
part transversal. -/
def TypeGood {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (h : PartConsistent U s τ) : Prop :=
  RootFixed U s τ ∧ EdgeTransversal U s τ h

lemma partConsistent_tupleType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) :
    PartConsistent U s (tupleType U X w s φ) := by
  classical
  intro b hb p q hp hq
  have hb_eq : b = block U X w s φ p := by
    have h1 : blockOf U s (tupleType U X w s φ) p.1 p.2 = b :=
      blockOf_eq_of_mem U s (tupleType U X w s φ) ⟨b, hb⟩ hp
    have h2 : blockOf U s (tupleType U X w s φ) p.1 p.2 =
        block U X w s φ p := by
      change blockOf U s (partitionOf U X w s φ, fun i => (φ i).1)
        p.1 p.2 = block U X w s φ p
      rw [blockOf_partitionOf]
    exact h1.symm.trans h2
  have hq_block : q ∈ block U X w s φ p := by
    rw [← hb_eq]
    exact hq
  have hpq : tupleImage U X w s φ q = tupleImage U X w s φ p :=
    (mem_block_iff U X w s φ p q).mp hq_block
  have hp_part := (φ p.2).2.part_compat p.1.1
  have hq_part := (φ q.2).2.part_compat q.1.1
  calc
    (tupleType U X w s φ).2 p.2 (U.part p.1.1) =
        X.part (tupleImage U X w s φ p) := by
      simpa [tupleType, tupleImage] using hp_part.symm
    _ = X.part (tupleImage U X w s φ q) := by rw [hpq]
    _ = (tupleType U X w s φ).2 q.2 (U.part q.1.1) := by
      simpa [tupleType, tupleImage] using hq_part

lemma edgeTransversal_tupleType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) :
    EdgeTransversal U s (tupleType U X w s φ)
      (partConsistent_tupleType U X w s φ) := by
  classical
  let τ := tupleType U X w s φ
  let h := partConsistent_tupleType U X w s φ
  intro i e he j
  let E := e.image (φ i).2.toFun
  have hE : E ∈ X.G.edges := by
    simpa [E, Finset.map_eq_image] using (φ i).2.edge_map e he
  let x := (X.edge_part E hE j).choose
  have hx_mem : x ∈ E := ((X.edge_part E hE j).choose_spec).1.1
  have hx_part : X.part x = j := ((X.edge_part E hE j).choose_spec).1.2
  obtain ⟨y, hye, hyx⟩ := Finset.mem_image.mp hx_mem
  have hpart_y : typeVertexPartOf τ (blockPartOf U s τ h)
      (typeEmbed U s τ i y) = X.part ((φ i).2.toFun y) := by
    by_cases hyR : y ∈ U.R
    · have hroot := (φ i).2.root_compat y hyR
      have hw := hwpart ⟨y, hyR⟩
      simp [typeEmbed, hyR, typeVertexPartOf, hroot, hw]
    · have hte : typeEmbed U s τ i y =
          Sum.inr ⟨blockOf U s τ ⟨y, hyR⟩ i,
            blockOf_mem U s τ ⟨y, hyR⟩ i⟩ := by
        simp [typeEmbed, hyR]
      rw [hte]
      simp only [typeVertexPartOf]
      rw [blockPartOf_eq U s τ h _ (mem_blockOf U s τ ⟨y, hyR⟩ i)]
      exact ((φ i).2.part_compat y).symm
  refine ⟨typeEmbed U s τ i y, ⟨?_, ?_⟩, ?_⟩
  · exact Finset.mem_image.mpr ⟨y, hye, rfl⟩
  · rw [hpart_y, hyx, hx_part]
  · intro v' hv'
    have hpart_v' : typeVertexPartOf τ (blockPartOf U s τ h) v' = j := hv'.2
    rcases Finset.mem_image.mp hv'.1 with ⟨y', hy'e, rfl⟩
    have hpart_y' : typeVertexPartOf τ (blockPartOf U s τ h)
        (typeEmbed U s τ i y') = X.part ((φ i).2.toFun y') := by
      by_cases hyR : y' ∈ U.R
      · have hroot := (φ i).2.root_compat y' hyR
        have hw := hwpart ⟨y', hyR⟩
        simp [typeEmbed, hyR, typeVertexPartOf, hroot, hw]
      · have hte : typeEmbed U s τ i y' =
            Sum.inr ⟨blockOf U s τ ⟨y', hyR⟩ i,
              blockOf_mem U s τ ⟨y', hyR⟩ i⟩ := by
          simp [typeEmbed, hyR]
        rw [hte]
        simp only [typeVertexPartOf]
        rw [blockPartOf_eq U s τ h _ (mem_blockOf U s τ ⟨y', hyR⟩ i)]
        exact ((φ i).2.part_compat y').symm
    have hx'_mem : (φ i).2.toFun y' ∈ E :=
      Finset.mem_image.mpr ⟨y', hy'e, rfl⟩
    have hx'_part : X.part ((φ i).2.toFun y') = j := by
      rw [← hpart_y']
      exact hpart_v'
    have hx_eq : (φ i).2.toFun y' = x :=
      (X.edge_part E hE j).unique ⟨hx'_mem, hx'_part⟩ ⟨hx_mem, hx_part⟩
    have hy_eq : y' = y := (φ i).2.inj (by rw [hx_eq, hyx])
    subst hy_eq
    rfl

lemma typeGood_tupleType {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V)
    (hwpart : ∀ r : U.R, X.part (w r) = U.part r.1) (s : ℕ)
    (φ : Tuple U X w s) :
    TypeGood U s (tupleType U X w s φ)
      (partConsistent_tupleType U X w s φ) :=
  ⟨rootFixed_tupleType U X w hwpart s φ,
    edgeTransversal_tupleType U X w hwpart s φ⟩

lemma typeEdgeSet_eq_image_choose {k : ℕ}
    (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    typeEdgeSet U s τ i e =
      Finset.univ.image (fun j : Fin k => (hgood i he j).choose) := by
  classical
  ext v
  constructor
  · intro hv
    let j := typeVertexPartOf τ (blockPartOf U s τ h) v
    have hv_eq : v = (hgood i he j).choose :=
      (hgood i he j).unique ⟨hv, rfl⟩
        ⟨(hgood i he j).choose_spec.1.1,
          (hgood i he j).choose_spec.1.2⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hv_eq.symm⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨j, -, rfl⟩
    exact (hgood i he j).choose_spec.1.1

end Erdos571_hypergraph
