import Erdos571_hypergraph_L3_Host
import Erdos571_hypergraph_L3_TypeEmbeddingOf
import Erdos571_hypergraph_L3_TypeGood

namespace Erdos571_hypergraph

/-- The unique vertex of an edge in a prescribed part. -/
noncomputable def edgeVertex {k : ℕ} (U : PartiteRootedKHypergraph k)
    {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k) : U.V :=
  (U.edge_part e he j).choose

lemma edgeVertex_mem {k : ℕ} (U : PartiteRootedKHypergraph k)
    {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k) :
    edgeVertex U he j ∈ e :=
  ((U.edge_part e he j).choose_spec).1.1

lemma edgeVertex_part {k : ℕ} (U : PartiteRootedKHypergraph k)
    {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k) :
    U.part (edgeVertex U he j) = j :=
  ((U.edge_part e he j).choose_spec).1.2

/-- A block map into the polynomial host, respecting the part of each block. -/
abbrev HostBlockMap (F : Type) [Field F] {k : ℕ} (b : ℕ)
    (U : PartiteRootedKHypergraph k) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :=
  {β : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} →
      HostVertex F k b //
    ∀ b, (β b).1 = blockPartOf U s τ h b}

/-- The host `k`-tuple associated with an edge of `H_τ` and a block map. -/
noncomputable def hostBlockEdgeTuple {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k)
    (w : U.R → HostVertex F k b) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) (β : HostBlockMap F b U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    Fin k → (Fin b → F) :=
  fun j =>
    let v := edgeVertex U he ((τ.2 i).symm j)
    if hv : v ∈ U.R then (w ⟨v, hv⟩).2
    else
      (β.1 ⟨blockOf U s τ ⟨v, hv⟩ i,
        blockOf_mem U s τ ⟨v, hv⟩ i⟩).2

/-- The combined map from `V(H_τ)` to the host, sending roots by `w` and
blocks by `β`. -/
noncomputable def hostBlockVertexMap {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h) :
    TypeVertex U τ → HostVertex F k b
  | Sum.inl r => w r
  | Sum.inr bl => β.1 bl

lemma hostBlockEdgeTuple_eq {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h) (i : Fin s) {e : Finset U.V}
    (he : e ∈ U.G.edges) (j : Fin k) :
    hostBlockEdgeTuple U w s τ h β i he j =
      (hostBlockVertexMap U w s τ h β
        (typeEmbed U s τ i (edgeVertex U he ((τ.2 i).symm j)))).2 := by
  classical
  unfold hostBlockEdgeTuple hostBlockVertexMap
  by_cases hv : edgeVertex U he ((τ.2 i).symm j) ∈ U.R
  · simp [hv, typeEmbed]
  · simp [hv, typeEmbed]

lemma hostBlockVertexMap_part {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (v : TypeVertex U τ) :
    (hostBlockVertexMap U w s τ h β v).1 =
      typeVertexPartOf τ (blockPartOf U s τ h) v := by
  cases v with
  | inl r => exact hwpart r
  | inr bl => exact β.2 bl

/-- The host edge tuple of a good type, choosing the unique type vertex in
each host part.  This is the correct definition for types with roots. -/
noncomputable def hostBlockEdgeTupleGood {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (β : HostBlockMap F b U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    Fin k → (Fin b → F) :=
  fun j =>
    let v := (hgood i he j).choose
    match v with
    | Sum.inl r => (w r).2
    | Sum.inr bl => (β.1 bl).2

/-- The block map associated with a tuple in the polynomial host. -/
noncomputable def tupleBlockMap {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → (hostPartite P).V) (s : ℕ)
    (φ : Tuple U (hostPartite P) w s) :
    HostBlockMap F b U s (tupleType U (hostPartite P) w s φ)
      (partConsistent_tupleType U (hostPartite P) w s φ) :=
  ⟨fun bl => blockImage U (hostPartite P) w s φ bl, by
    intro bl
    classical
    obtain ⟨p, hp⟩ := (tupleType U (hostPartite P) w s φ).1.nonempty bl.1 bl.2
    change (hostPartite P).part
      (blockImage U (hostPartite P) w s φ bl) =
      blockPartOf U s (tupleType U (hostPartite P) w s φ)
        (partConsistent_tupleType U (hostPartite P) w s φ) bl
    rw [blockImage_eq U (hostPartite P) w s φ bl hp]
    rw [blockPartOf_eq U s (tupleType U (hostPartite P) w s φ)
      (partConsistent_tupleType U (hostPartite P) w s φ) bl hp]
    simpa [tupleType, tupleImage] using
      (φ p.2).2.part_compat p.1.1⟩

lemma hostBlockEdgeTupleGood_inl {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k)
    {r : U.R} (hv : (hgood i he j).choose = Sum.inl r) :
    hostBlockEdgeTupleGood U w s τ h hgood β i he j = (w r).2 := by
  unfold hostBlockEdgeTupleGood
  rw [hv]

lemma hostBlockEdgeTupleGood_inr {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k)
    {bl : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}}
    (hv : (hgood i he j).choose = Sum.inr bl) :
    hostBlockEdgeTupleGood U w s τ h hgood β i he j = (β.1 bl).2 := by
  unfold hostBlockEdgeTupleGood
  rw [hv]

lemma hostBlockEdgeTupleGood_tuple_eq {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → (hostPartite P).V)
    (hwpart : ∀ r : U.R, (hostPartite P).part (w r) = U.part r.1)
    (s : ℕ) (φ : Tuple U (hostPartite P) w s)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k)
    {y : U.V} (hy : typeEmbed U s (tupleType U (hostPartite P) w s φ) i y =
      (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ i he j).choose) :
    hostBlockEdgeTupleGood U w s
      (tupleType U (hostPartite P) w s φ)
      (partConsistent_tupleType U (hostPartite P) w s φ)
      (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ)
      (tupleBlockMap U P w s φ) i he j =
    ((φ i).2.toFun y).2 := by
  classical
  by_cases hyR : y ∈ U.R
  · have hte : typeEmbed U s (tupleType U (hostPartite P) w s φ) i y =
        Sum.inl ⟨y, hyR⟩ := by
      simp [typeEmbed, hyR]
    have hv : (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ
        i he j).choose = Sum.inl ⟨y, hyR⟩ := by
      rw [← hy, hte]
    rw [hostBlockEdgeTupleGood_inl U w s
      (tupleType U (hostPartite P) w s φ)
      (partConsistent_tupleType U (hostPartite P) w s φ)
      (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ)
      (tupleBlockMap U P w s φ) i he j hv]
    rw [(φ i).2.root_compat y hyR]
  · let bl : {b : Finset (Interior U × Fin s) //
        b ∈ (tupleType U (hostPartite P) w s φ).1.blocks} :=
      ⟨blockOf U s (tupleType U (hostPartite P) w s φ) ⟨y, hyR⟩ i,
        blockOf_mem U s (tupleType U (hostPartite P) w s φ) ⟨y, hyR⟩ i⟩
    have hte : typeEmbed U s (tupleType U (hostPartite P) w s φ) i y =
        Sum.inr bl := by
      simp [typeEmbed, hyR, bl]
    have hv : (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ
        i he j).choose = Sum.inr bl := by
      rw [← hy, hte]
    rw [hostBlockEdgeTupleGood_inr U w s
      (tupleType U (hostPartite P) w s φ)
      (partConsistent_tupleType U (hostPartite P) w s φ)
      (edgeTransversal_tupleType U (hostPartite P) w hwpart s φ)
      (tupleBlockMap U P w s φ) i he j hv]
    change (blockImage U (hostPartite P) w s φ bl).2 =
      ((φ i).2.toFun y).2
    rw [blockImage_eq U (hostPartite P) w s φ bl
      (mem_blockOf U s (tupleType U (hostPartite P) w s φ) ⟨y, hyR⟩ i)]
    rfl

lemma hostBlockEdgeTupleGood_eq_snd {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) (j : Fin k) :
    hostBlockEdgeTupleGood U w s τ h hgood β i he j =
      (hostBlockVertexMap U w s τ h β (hgood i he j).choose).2 := by
  unfold hostBlockEdgeTupleGood hostBlockVertexMap
  cases (hgood i he j).choose <;> rfl

lemma hostBlockVertexMap_snd {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h) (v : TypeVertex U τ) :
    (hostBlockVertexMap U w s τ h β v).2 =
      (match v with
        | Sum.inl r => (w r).2
        | Sum.inr bl => (β.1 bl).2) := by
  cases v <;> rfl

lemma hostBlockEdgeTupleGood_choose_eq {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges)
    (i' : Fin s) {e' : Finset U.V} (he' : e' ∈ U.G.edges)
    (hEq : hostBlockEdgeTupleGood U w s τ h hgood β i he =
      hostBlockEdgeTupleGood U w s τ h hgood β i' he') :
    ∀ j : Fin k, (hgood i he j).choose = (hgood i' he' j).choose := by
  intro j
  apply hΦ
  apply Prod.ext
  · rw [hostBlockVertexMap_part U w s τ h β hwpart,
        hostBlockVertexMap_part U w s τ h β hwpart,
        (hgood i he j).choose_spec.1.2,
        (hgood i' he' j).choose_spec.1.2]
  · have hz := congrFun hEq j
    rw [hostBlockVertexMap_snd, hostBlockVertexMap_snd]
    simpa [hostBlockEdgeTupleGood] using hz

lemma typeEdgeSet_eq_of_hostBlockEdgeTupleGood_eq {F : Type} [Field F]
    [Fintype F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges)
    (i' : Fin s) {e' : Finset U.V} (he' : e' ∈ U.G.edges)
    (hEq : hostBlockEdgeTupleGood U w s τ h hgood β i he =
      hostBlockEdgeTupleGood U w s τ h hgood β i' he') :
    typeEdgeSet U s τ i e = typeEdgeSet U s τ i' e' := by
  classical
  rw [typeEdgeSet_eq_image_choose U s τ h hgood i he,
    typeEdgeSet_eq_image_choose U s τ h hgood i' he']
  congr 1
  funext j
  exact hostBlockEdgeTupleGood_choose_eq U w s τ h hgood β hwpart hΦ i he i' he' hEq j

lemma image_typeEdgeSet_eq_hostEdge {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (i : Fin s) {e : Finset U.V} (he : e ∈ U.G.edges) :
    (typeEdgeSet U s τ i e).image (hostBlockVertexMap U w s τ h β) =
      hostEdge (hostBlockEdgeTupleGood U w s τ h hgood β i he) := by
  classical
  rw [typeEdgeSet_eq_image_choose U s τ h hgood i he, Finset.image_image]
  apply Finset.image_congr
  intro j _
  apply Prod.ext
  · change (hostBlockVertexMap U w s τ h β (hgood i he j).choose).1 = j
    rw [hostBlockVertexMap_part U w s τ h β hwpart,
      (hgood i he j).choose_spec.1.2]
  · change (hostBlockVertexMap U w s τ h β (hgood i he j).choose).2 =
      hostBlockEdgeTupleGood U w s τ h hgood β i he j
    exact (hostBlockEdgeTupleGood_eq_snd U w s τ h hgood β i he j).symm

end Erdos571_hypergraph
