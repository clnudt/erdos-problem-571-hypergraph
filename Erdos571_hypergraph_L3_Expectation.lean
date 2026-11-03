import Erdos571_hypergraph_L3_HostBlock
import Erdos571_hypergraph_L3_EdgeCount

namespace Erdos571_hypergraph

/-- A host `k`-tuple associated with a type edge.  A type edge may have many
representations `(i,e)`; choose one arbitrarily. -/
noncomputable def hostTupleOfTypeEdge {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (i : Fin s) (e : Finset U.V) (he : e ∈ U.G.edges) :
    Fin k → (Fin b → F) :=
  hostBlockEdgeTupleGood U w s τ h hgood β i he

/-- The set of host tuples coming from the type edges. -/
noncomputable def hostTuplesOfType {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hτa : TypeAdmissible U s τ) :
    Finset (Fin k → (Fin b → F)) := by
  classical
  exact Finset.univ.image (fun p : Fin s × {e : Finset U.V // e ∈ U.G.edges} =>
    hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1 p.2.1 p.2.2)

lemma hostTupleOfTypeEdge_eq_typeEdgeSet {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (i : Fin s) (e : Finset U.V) (he : e ∈ U.G.edges)
    (i' : Fin s) (e' : Finset U.V) (he' : e' ∈ U.G.edges)
    (hEq : hostTupleOfTypeEdge (F := F) U w s τ h hgood β i e he =
      hostTupleOfTypeEdge (F := F) U w s τ h hgood β i' e' he') :
    typeEdgeSet U s τ i e = typeEdgeSet U s τ i' e' :=
  typeEdgeSet_eq_of_hostBlockEdgeTupleGood_eq U w s τ h hgood β hwpart hΦ
    i he i' he' hEq

lemma hostTupleOfTypeEdge_eq_of_typeEdgeSet_eq {F : Type} [Field F]
    [Fintype F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (i : Fin s) (e : Finset U.V) (he : e ∈ U.G.edges)
    (i' : Fin s) (e' : Finset U.V) (he' : e' ∈ U.G.edges)
    (hE : typeEdgeSet U s τ i e = typeEdgeSet U s τ i' e') :
    hostTupleOfTypeEdge (F := F) U w s τ h hgood β i e he =
      hostTupleOfTypeEdge (F := F) U w s τ h hgood β i' e' he' := by
  classical
  funext j
  have hchoose : (hgood i he j).choose = (hgood i' he' j).choose := by
    exact (hgood i' he' j).unique
      ⟨by rw [← hE]; exact (hgood i he j).choose_spec.1.1,
        (hgood i he j).choose_spec.1.2⟩
      ⟨(hgood i' he' j).choose_spec.1.1,
        (hgood i' he' j).choose_spec.1.2⟩
  change hostBlockEdgeTupleGood U w s τ h hgood β i he j =
    hostBlockEdgeTupleGood U w s τ h hgood β i' he' j
  rw [hostBlockEdgeTupleGood_eq_snd U w s τ h hgood β i he j,
    hostBlockEdgeTupleGood_eq_snd U w s τ h hgood β i' he' j,
    hchoose]

/-- Enumerate a finset of host `k`-tuples as `(k*b)`-vectors. -/
noncomputable def hostTuplesToFin {F : Type} {k b : ℕ}
    (Z : Finset (Fin k → (Fin b → F))) :
    Fin Z.card → (Fin (k * b) → F) :=
  fun i => flattenTuple ((Finset.equivFin Z).symm i).1

lemma hostTuplesToFin_injective {F : Type} {k b : ℕ}
    (Z : Finset (Fin k → (Fin b → F))) :
    Function.Injective (hostTuplesToFin Z) := by
  intro i j h
  have h1 : ((Finset.equivFin Z).symm i).1 = ((Finset.equivFin Z).symm j).1 :=
    flattenTuple_injective h
  have h2 : (Finset.equivFin Z).symm i = (Finset.equivFin Z).symm j :=
    Subtype.ext h1
  exact (Finset.equivFin Z).symm.injective h2

/-- The coefficient data of the host is equivalent to a tuple of `a`
polynomials. -/
noncomputable def hostParamsEquiv {F : Type} [Field F] (k b a D : ℕ) :
    HostParams F k b a D ≃ (Fin a → PolyCoeff F (k * b) D) where
  toFun P := P.coeffs
  invFun f := ⟨f⟩
  left_inv P := by
    cases P
    rfl
  right_inv f := rfl

/-- The number of coefficient data vanishing on `m` prescribed points. -/
lemma card_params_zero_on_points {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b m D a : ℕ} [DecidableEq (PolyCoeff F (k * b) D)]
    (z : Fin m → (Fin (k * b) → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F)
    (hD : m ≤ D + 1) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ (j : Fin a) (i : Fin m),
          evalPolyAt (D := D) (z i) (P.coeffs j) = 0)).card *
        Fintype.card F ^ (a * m) =
      Fintype.card (HostParams F k b a D) := by
  classical
  let qpred : (Fin a → PolyCoeff F (k * b) D) → Prop :=
    fun f => ∀ (j : Fin a) (i : Fin m),
      evalPolyAt (D := D) (z i) (f j) = 0
  have hcard : (Finset.univ.filter (fun P : HostParams F k b a D =>
        qpred P.coeffs)).card =
      (Finset.univ.filter qpred).card := by
    apply Finset.card_bij (fun P _ => P.coeffs)
    · intro P hP
      simpa [qpred] using hP
    · intro P₁ _ P₂ _ h
      cases P₁
      cases P₂
      simpa using h
    · intro f hf
      exact ⟨⟨f⟩, by simpa [qpred] using hf, rfl⟩
  rw [hcard]
  rw [card_tuple_zero_at_points (F := F) (n := k * b) (m := m)
    (D := D) (a := a) z hz hq hD]
  exact (Fintype.card_congr (hostParamsEquiv k b a D)).symm

/-- Conditional form of the type-edge parameter bound: once the count for
the host-tuple finset is known, the count for all type edges is bounded. -/
lemma typeEdge_params_le_of_bound {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hτa : TypeAdmissible U s τ)
    (Z : Finset (Fin k → (Fin b → F)))
    (hZ : Z = hostTuplesOfType U w s τ h hgood β hτa)
    (hbound :
      (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ z ∈ Z, ∀ j : Fin a,
          evalAtTuple (D := D) (P.coeffs j) z = 0)).card *
        Fintype.card F ^ (a * eτ U s τ) =
      Fintype.card (HostParams F k b a D)) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
      ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
        evalAtTuple (D := D) (P.coeffs j)
          (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
            p.2.1 p.2.2) = 0)).card *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card (HostParams F k b a D) := by
  classical
  let Zfilter := Finset.univ.filter (fun P : HostParams F k b a D =>
    ∀ z ∈ Z, ∀ j : Fin a,
      evalAtTuple (D := D) (P.coeffs j) z = 0)
  let Pfilter := Finset.univ.filter (fun P : HostParams F k b a D =>
    ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
      evalAtTuple (D := D) (P.coeffs j)
        (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
          (e := p.2.1) (he := p.2.2)) = 0)
  have hsub : Pfilter ⊆ Zfilter := by
    intro P hP
    simp only [Pfilter, Zfilter, Finset.mem_filter, Finset.mem_univ, true_and] at hP ⊢
    intro z hz
    rw [hZ] at hz
    rcases Finset.mem_image.mp hz with ⟨p, -, rfl⟩
    exact hP p
  have hcard : Pfilter.card ≤ Zfilter.card :=
    Finset.card_le_card hsub
  calc
    Pfilter.card * Fintype.card F ^ (a * eτ U s τ) ≤
        Zfilter.card * Fintype.card F ^ (a * eτ U s τ) :=
      Nat.mul_le_mul_right _ hcard
    _ = Fintype.card (HostParams F k b a D) := hbound

lemma hostTuplesToFin_mem {F : Type} {k b : ℕ}
    (Z : Finset (Fin k → (Fin b → F))) (i : Fin Z.card) :
    ((Finset.equivFin Z).symm i).1 ∈ Z :=
  ((Finset.equivFin Z).symm i).2

lemma hostTuplesToFin_surj {F : Type} {k b : ℕ}
    (Z : Finset (Fin k → (Fin b → F))) {z : Fin k → (Fin b → F)}
    (hz : z ∈ Z) :
    ∃ i : Fin Z.card, ((Finset.equivFin Z).symm i).1 = z := by
  classical
  let i : Fin Z.card := Finset.equivFin Z ⟨z, hz⟩
  refine ⟨i, ?_⟩
  have h : (Finset.equivFin Z).symm i = ⟨z, hz⟩ := by
    simp [i]
  rw [h]

lemma params_zero_on_finset {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} [DecidableEq (PolyCoeff F (k * b) D)]
    (Z : Finset (Fin k → (Fin b → F)))
    (hq : (Z.card.choose 2 : ℕ) < Fintype.card F)
    (hD : Z.card ≤ D + 1) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ z ∈ Z, ∀ j : Fin a,
          evalAtTuple (D := D) (P.coeffs j) z = 0)).card *
        Fintype.card F ^ (a * Z.card) =
      Fintype.card (HostParams F k b a D) := by
  classical
  let z := hostTuplesToFin Z
  have hz : Function.Injective z := hostTuplesToFin_injective Z
  have h := card_params_zero_on_points (F := F) (k := k) (b := b)
    (m := Z.card) (D := D) (a := a) z hz hq hD
  have hfilter :
      (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ z' ∈ Z, ∀ j : Fin a,
          evalAtTuple (D := D) (P.coeffs j) z' = 0)) =
      (Finset.univ.filter (fun P : HostParams F k b a D =>
        ∀ (j : Fin a) (i : Fin Z.card),
          evalPolyAt (D := D) (z i) (P.coeffs j) = 0)) := by
    apply Finset.filter_congr
    intro P _
    constructor
    · intro hP j i
      have hmem := hostTuplesToFin_mem Z i
      have := hP ((Finset.equivFin Z).symm i).1 hmem j
      simpa [z, hostTuplesToFin, evalAtTuple] using this
    · intro hP z' hz' j
      obtain ⟨i, hi⟩ := hostTuplesToFin_surj Z hz'
      have := hP j i
      simpa [z, hostTuplesToFin, hi, evalAtTuple] using this
  rw [hfilter]
  exact h

/-- Type-edge parameter bound, conditional only on the cardinality of the
host-tuple finset being `eτ`. -/
lemma typeEdge_params_le_of_card {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hτa : TypeAdmissible U s τ)
    (Z : Finset (Fin k → (Fin b → F)))
    (hZ : Z = hostTuplesOfType U w s τ h hgood β hτa)
    (hcard : Z.card = eτ U s τ)
    (hq : (eτ U s τ).choose 2 < Fintype.card F)
    (hD : eτ U s τ ≤ D + 1) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
      ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
        evalAtTuple (D := D) (P.coeffs j)
          (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
            p.2.1 p.2.2) = 0)).card *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card (HostParams F k b a D) := by
  classical
  have hq' : (Z.card.choose 2 : ℕ) < Fintype.card F := by
    rwa [hcard]
  have hD' : Z.card ≤ D + 1 := by
    rwa [hcard]
  have hbound := params_zero_on_finset (F := F) (k := k) (b := b)
    (a := a) (D := D) Z hq' hD'
  rw [hcard] at hbound
  exact typeEdge_params_le_of_bound U w τ h hgood β hτa Z hZ hbound

/-- If two functions have the same fibres, their images have the same
cardinality. -/
lemma card_image_eq_of_fiber {α β γ : Type} [Fintype α]
    [DecidableEq β] [DecidableEq γ]
    (f : α → β) (g : α → γ)
    (h : ∀ a b, f a = f b ↔ g a = g b) :
    (Finset.univ.image f).card = (Finset.univ.image g).card := by
  classical
  apply Finset.card_bij
    (fun y hy =>
      let a := Classical.choose (Finset.mem_image.mp hy)
      g a)
  · intro y hy
    let a := Classical.choose (Finset.mem_image.mp hy)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    let a₁ := Classical.choose (Finset.mem_image.mp hy₁)
    let a₂ := Classical.choose (Finset.mem_image.mp hy₂)
    have hf₁ : f a₁ = y₁ := (Classical.choose_spec (Finset.mem_image.mp hy₁)).2
    have hf₂ : f a₂ = y₂ := (Classical.choose_spec (Finset.mem_image.mp hy₂)).2
    have hg : g a₁ = g a₂ := heq
    have hf : f a₁ = f a₂ := (h a₁ a₂).mpr hg
    rw [hf₁, hf₂] at hf
    exact hf
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨a, -, rfl⟩
    have hmem : f a ∈ Finset.univ.image f :=
      Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    let a' := Classical.choose (Finset.mem_image.mp hmem)
    have hf' : f a' = f a :=
      (Classical.choose_spec (Finset.mem_image.mp hmem)).2
    have hg' : g a' = g a := (h a' a).mp hf'
    refine ⟨f a, hmem, ?_⟩
    exact hg'

lemma hostTuplesOfType_card_eq_eτ {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (hτa : TypeAdmissible U s τ) :
    (hostTuplesOfType U w s τ h hgood β hτa).card = eτ U s τ := by
  classical
  let g : (Fin s × {e : Finset U.V // e ∈ U.G.edges}) →
      Finset (TypeVertex U τ) :=
    fun p => typeEdgeSet U s τ p.1 p.2.1
  let f : (Fin s × {e : Finset U.V // e ∈ U.G.edges}) →
      (Fin k → (Fin b → F)) :=
    fun p => hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1 p.2.1 p.2.2
  have hfiber : ∀ a b, f a = f b ↔ g a = g b := by
    intro a b
    constructor
    · intro hf
      exact hostTupleOfTypeEdge_eq_typeEdgeSet U w s τ h hgood β hwpart hΦ
        a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2 hf
    · intro hg
      exact hostTupleOfTypeEdge_eq_of_typeEdgeSet_eq U w s τ h hgood β
        a.1 a.2.1 a.2.2 b.1 b.2.1 b.2.2 hg
  have hcard := card_image_eq_of_fiber f g hfiber
  have hf : Finset.univ.image f =
      hostTuplesOfType U w s τ h hgood β hτa := rfl
  have hg : Finset.univ.image g = (typeGraph U s τ hτa).edges := rfl
  rw [hf, hg] at hcard
  rw [eτ_eq_typeGraph_edges U s τ hτa]
  exact hcard

/-- Unconditional type-edge parameter bound (for a fixed block map). -/
lemma typeEdge_params_le {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (hτa : TypeAdmissible U s τ)
    (hq : (eτ U s τ).choose 2 < Fintype.card F)
    (hD : eτ U s τ ≤ D + 1) :
    (Finset.univ.filter (fun P : HostParams F k b a D =>
      ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
        evalAtTuple (D := D) (P.coeffs j)
          (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
            p.2.1 p.2.2) = 0)).card *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card (HostParams F k b a D) := by
  classical
  let Z := hostTuplesOfType U w s τ h hgood β hτa
  have hcard : Z.card = eτ U s τ :=
    hostTuplesOfType_card_eq_eτ U w s τ h hgood β hwpart hΦ hτa
  exact typeEdge_params_le_of_card U w τ h hgood β hτa Z rfl hcard hq hD

/-- The block maps realized by tuples of type `τ` in the host `P`. -/
noncomputable def realizedHostBlockMaps {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    Finset (HostBlockMap F b U s τ h) :=
  Finset.image
    (fun t : TupleOfType U (hostPartite P) w s τ =>
      tupleToPartRespectingBlockMap U (hostPartite P) w s h t)
    (@Finset.univ (TupleOfType U (hostPartite P) w s τ)
      (tupleOfTypeFintype U (hostPartite P) w s τ))

lemma NτFixed_le_card_realized {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    NτFixed U (hostPartite P) w s τ ≤
      (realizedHostBlockMaps U P w τ h).card := by
  classical
  change @Fintype.card (TupleOfType U (hostPartite P) w s τ)
      (tupleOfTypeFintype U (hostPartite P) w s τ) ≤
    (realizedHostBlockMaps U P w τ h).card
  letI : Fintype (TupleOfType U (hostPartite P) w s τ) :=
    tupleOfTypeFintype U (hostPartite P) w s τ
  let f : TupleOfType U (hostPartite P) w s τ →
      {β : HostBlockMap F b U s τ h //
        β ∈ realizedHostBlockMaps U P w τ h} :=
    fun t => ⟨tupleToPartRespectingBlockMap U (hostPartite P) w s h t,
      Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
  have hf : Function.Injective f := by
    intro t u htu
    have hval : tupleToPartRespectingBlockMap U (hostPartite P) w s h t =
        tupleToPartRespectingBlockMap U (hostPartite P) w s h u :=
      congrArg Subtype.val htu
    exact tupleToPartRespectingBlockMap_injective U (hostPartite P) w s h hval
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hcard
  exact hcard

/-- The coefficient data for which all type edges of `β` are host edges. -/
noncomputable def edgeData {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (a D : ℕ)
    (β : HostBlockMap F b U s τ h) :
    Finset (HostParams F k b a D) :=
  Finset.univ.filter (fun P : HostParams F k b a D =>
    ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
      evalAtTuple (D := D) (P.coeffs j)
        (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
          p.2.1 p.2.2) = 0)

lemma edgeData_card_mul_le {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (a D : ℕ) (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hΦ : Function.Injective (hostBlockVertexMap U w s τ h β))
    (hτa : TypeAdmissible U s τ)
    (hq : (eτ U s τ).choose 2 < Fintype.card F)
    (hD : eτ U s τ ≤ D + 1) :
    (edgeData U w τ h hgood a D β).card *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card (HostParams F k b a D) :=
  typeEdge_params_le U w τ h hgood β hwpart hΦ hτa hq hD

lemma mem_edgeData {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h) (a D : ℕ)
    (β : HostBlockMap F b U s τ h) (P : HostParams F k b a D) :
    P ∈ edgeData U w τ h hgood a D β ↔
      ∀ (p : Fin s × {e : Finset U.V // e ∈ U.G.edges}) (j : Fin a),
        evalAtTuple (D := D) (P.coeffs j)
          (hostTupleOfTypeEdge (F := F) U w s τ h hgood β p.1
            p.2.1 p.2.2) = 0 := by
  classical
  simp [edgeData]

lemma hostBlockVertexMap_typeEmbed_eq {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h)
    (t : TupleOfType U (hostPartite P) w s τ)
    (hβ : β = tupleToPartRespectingBlockMap U (hostPartite P) w s h t)
    (i : Fin s) (v : U.V) :
    hostBlockVertexMap U w s τ h β (typeEmbed U s τ i v) =
      (t.emb i).toFun v := by
  classical
  by_cases hv : v ∈ U.R
  · have hte : typeEmbed U s τ i v = Sum.inl ⟨v, hv⟩ := by
      simp [typeEmbed, hv]
    rw [hte]
    simp [hostBlockVertexMap, (t.emb i).root_compat v hv]
  · have hte : typeEmbed U s τ i v =
        Sum.inr ⟨blockOf U s τ ⟨v, hv⟩ i,
          blockOf_mem U s τ ⟨v, hv⟩ i⟩ := by
      simp [typeEmbed, hv]
    rw [hte]
    simp only [hostBlockVertexMap]
    rw [hβ]
    change blockMapOfTupleOfType U (hostPartite P) w s t
        ⟨blockOf U s τ ⟨v, hv⟩ i, blockOf_mem U s τ ⟨v, hv⟩ i⟩ =
      (t.emb i).toFun v
    unfold blockMapOfTupleOfType
    rw [blockImage_eq U (hostPartite P) w s
      (TupleOfType.toSigma U (hostPartite P) w s t) _
      (mem_blockOf U s τ ⟨v, hv⟩ i)]
    rfl

lemma image_typeEdgeSet_eq_image_emb {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h)
    (t : TupleOfType U (hostPartite P) w s τ)
    (hβ : β = tupleToPartRespectingBlockMap U (hostPartite P) w s h t)
    (i : Fin s) {e : Finset U.V} :
    (typeEdgeSet U s τ i e).image (hostBlockVertexMap U w s τ h β) =
      e.image (t.emb i).toFun := by
  classical
  rw [typeEdgeSet, Finset.image_image]
  apply Finset.image_congr
  intro v _
  exact hostBlockVertexMap_typeEmbed_eq U P w τ h β t hβ i v

lemma realized_subset_edgeData {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (β : HostBlockMap F b U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hβ : β ∈ realizedHostBlockMaps U P w τ h) :
    P ∈ edgeData U w τ h hgood a D β := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨t, -, hβeq⟩
  have hβ' : β = tupleToPartRespectingBlockMap U (hostPartite P) w s h t :=
    hβeq.symm
  unfold edgeData
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  intro p j
  let i := p.1
  let e := p.2.1
  have he : e ∈ U.G.edges := p.2.2
  have hmem : e.image (t.emb i).toFun ∈ (hostPartite P).G.edges := by
    simpa [Finset.map_eq_image] using (t.emb i).edge_map e he
  rcases Finset.mem_image.mp hmem with ⟨z, hz, hzedge⟩
  have hz_zero : ∀ j : Fin a, evalAtTuple (D := D) (P.coeffs j) z = 0 :=
    (Finset.mem_filter.mp hz).2
  have himg1 : (typeEdgeSet U s τ i e).image
      (hostBlockVertexMap U w s τ h β) =
      hostEdge (hostBlockEdgeTupleGood U w s τ h hgood β i he) :=
    image_typeEdgeSet_eq_hostEdge U w s τ h hgood β hwpart i he
  have himg2 : (typeEdgeSet U s τ i e).image
      (hostBlockVertexMap U w s τ h β) =
      e.image (t.emb i).toFun :=
    image_typeEdgeSet_eq_image_emb U P w τ h β t hβ' i
  have hEdgeEq : hostEdge (hostBlockEdgeTupleGood U w s τ h hgood β i he) =
      hostEdge z := by
    rw [← himg1, himg2, ← hzedge]
  have htuple : hostBlockEdgeTupleGood U w s τ h hgood β i he = z :=
    hostEdge_injective hEdgeEq
  change evalAtTuple (D := D) (P.coeffs j)
      (hostBlockEdgeTupleGood U w s τ h hgood β i he) = 0
  rw [htuple]
  exact hz_zero j

lemma NτFixed_le_edgeData_card {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    [DecidableEq (HostParams F k b a D)] :
    NτFixed U (hostPartite P) w s τ ≤
      (Finset.univ.filter (fun β : HostBlockMap F b U s τ h =>
        P ∈ edgeData U w τ h hgood a D β)).card := by
  classical
  have hsub : realizedHostBlockMaps U P w τ h ⊆
      Finset.univ.filter (fun β : HostBlockMap F b U s τ h =>
        P ∈ edgeData U w τ h hgood a D β) := by
    intro β hβ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact realized_subset_edgeData U a D P w τ h hgood β hwpart hβ
  calc
    NτFixed U (hostPartite P) w s τ ≤
        (realizedHostBlockMaps U P w τ h).card :=
      NτFixed_le_card_realized U P w τ h
    _ ≤ (Finset.univ.filter (fun β : HostBlockMap F b U s τ h =>
        P ∈ edgeData U w τ h hgood a D β)).card :=
      Finset.card_le_card hsub

lemma sum_NτFixed_le_sum_edgeData {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    [DecidableEq (HostParams F k b a D)] :
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
      ∑ β : HostBlockMap F b U s τ h,
        (edgeData U w τ h hgood a D β).card := by
  classical
  calc
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
        ∑ P : HostParams F k b a D,
          (Finset.univ.filter (fun β : HostBlockMap F b U s τ h =>
            P ∈ edgeData U w τ h hgood a D β)).card := by
      apply Finset.sum_le_sum
      intro P _
      exact NτFixed_le_edgeData_card U a D P w τ h hgood hwpart
    _ = ∑ β : HostBlockMap F b U s τ h,
        (edgeData U w τ h hgood a D β).card := by
      have hcard : ∀ P : HostParams F k b a D,
          (Finset.univ.filter (fun β : HostBlockMap F b U s τ h =>
            P ∈ edgeData U w τ h hgood a D β)).card =
          ∑ β : HostBlockMap F b U s τ h,
            if P ∈ edgeData U w τ h hgood a D β then 1 else 0 := by
        intro P
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simp_rw [hcard]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β _
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      simp

/-- A block map is good if the combined map on `V(H_τ)` is injective. -/
def GoodBlockMap {F : Type} [Field F] [Fintype F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ)
    (β : HostBlockMap F b U s τ h) : Prop :=
  Function.Injective (hostBlockVertexMap U w s τ h β)

lemma tupleToPartRespectingBlockMap_inj_blocks {F : Type} [Field F]
    [Fintype F] [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (t : TupleOfType U (hostPartite P) w s τ)
    {b1 b2 : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}}
    (h12 : (tupleToPartRespectingBlockMap U (hostPartite P) w s h t).1 b1 =
      (tupleToPartRespectingBlockMap U (hostPartite P) w s h t).1 b2) :
    b1 = b2 := by
  classical
  change blockImage U (hostPartite P) w s
      (TupleOfType.toSigma U (hostPartite P) w s t)
      ⟨b1.1, cast (congrArg (fun p : Partition (Interior U × Fin s) =>
        b1.1 ∈ p.blocks) t.is_type.symm) b1.2⟩ =
    blockImage U (hostPartite P) w s
      (TupleOfType.toSigma U (hostPartite P) w s t)
      ⟨b2.1, cast (congrArg (fun p : Partition (Interior U × Fin s) =>
        b2.1 ∈ p.blocks) t.is_type.symm) b2.2⟩ at h12
  have hcast := blockImage_injective U (hostPartite P) w s
    (TupleOfType.toSigma U (hostPartite P) w s t) h12
  exact Subtype.ext (congrArg
    (fun x : {b : Finset (Interior U × Fin s) //
      b ∈ (tupleType U (hostPartite P) w s
        (TupleOfType.toSigma U (hostPartite P) w s t)).1.blocks} => x.1) hcast)

lemma realized_good {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D s : ℕ}
    (U : PartiteRootedKHypergraph k) (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hs : 0 < s)
    (β : HostBlockMap F b U s τ h)
    (hβ : β ∈ realizedHostBlockMaps U P w τ h) :
    GoodBlockMap U w s τ h β := by
  classical
  rcases Finset.mem_image.mp hβ with ⟨t, -, hβeq⟩
  have hβ' : β = tupleToPartRespectingBlockMap U (hostPartite P) w s h t :=
    hβeq.symm
  let i0 : Fin s := ⟨0, hs⟩
  intro v1 v2 hΦ
  rw [hβ'] at hΦ
  simp only [hostBlockVertexMap] at hΦ
  cases v1 with
  | inl r1 =>
    cases v2 with
    | inl r2 =>
      have h1 : (t.emb i0).toFun r1.1 = w r1 :=
        (t.emb i0).root_compat r1.1 r1.2
      have h2 : (t.emb i0).toFun r2.1 = w r2 :=
        (t.emb i0).root_compat r2.1 r2.2
      have heq : (t.emb i0).toFun r1.1 = (t.emb i0).toFun r2.1 := by
        rw [h1, h2]
        exact hΦ
      have hr : r1.1 = r2.1 := (t.emb i0).inj heq
      exact congrArg Sum.inl (Subtype.ext hr)
    | inr b2 =>
      let p := (τ.1.nonempty b2.1 b2.2).choose
      have hp : p ∈ b2.1 := (τ.1.nonempty b2.1 b2.2).choose_spec
      have hroot : (t.emb p.2).toFun r1.1 = w r1 :=
        (t.emb p.2).root_compat r1.1 r1.2
      have hblock : (t.emb p.2).toFun p.1.1 =
          (tupleToPartRespectingBlockMap U (hostPartite P) w s h t).1 b2 := by
        change (t.emb p.2).toFun p.1.1 =
          blockMapOfTupleOfType U (hostPartite P) w s t b2
        unfold blockMapOfTupleOfType
        rw [blockImage_eq U (hostPartite P) w s
          (TupleOfType.toSigma U (hostPartite P) w s t) _ (by exact hp)]
        rfl
      have heq : (t.emb p.2).toFun r1.1 = (t.emb p.2).toFun p.1.1 := by
        rw [hroot]
        exact hΦ.trans hblock.symm
      have hr : r1.1 = p.1.1 := (t.emb p.2).inj heq
      have hrootmem : p.1.1 ∈ U.R := by
        rw [← hr]
        exact r1.2
      exact False.elim (p.1.2 hrootmem)
  | inr b1 =>
    cases v2 with
    | inl r2 =>
      let p := (τ.1.nonempty b1.1 b1.2).choose
      have hp : p ∈ b1.1 := (τ.1.nonempty b1.1 b1.2).choose_spec
      have hroot : (t.emb p.2).toFun r2.1 = w r2 :=
        (t.emb p.2).root_compat r2.1 r2.2
      have hblock : (t.emb p.2).toFun p.1.1 =
          (tupleToPartRespectingBlockMap U (hostPartite P) w s h t).1 b1 := by
        change (t.emb p.2).toFun p.1.1 =
          blockMapOfTupleOfType U (hostPartite P) w s t b1
        unfold blockMapOfTupleOfType
        rw [blockImage_eq U (hostPartite P) w s
          (TupleOfType.toSigma U (hostPartite P) w s t) _ (by exact hp)]
        rfl
      have heq : (t.emb p.2).toFun r2.1 = (t.emb p.2).toFun p.1.1 := by
        rw [hroot]
        exact hΦ.symm.trans hblock.symm
      have hr : r2.1 = p.1.1 := (t.emb p.2).inj heq
      have hrootmem : p.1.1 ∈ U.R := by
        rw [← hr]
        exact r2.2
      exact False.elim (p.1.2 hrootmem)
    | inr b2 =>
      have hb : b1 = b2 :=
        tupleToPartRespectingBlockMap_inj_blocks U P w τ h t hΦ
      exact congrArg Sum.inr hb

/-- Good block maps, as a subtype. -/
abbrev GoodHostBlockMap {F : Type} [Field F] [Fintype F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ) :=
  {β : HostBlockMap F b U s τ h // GoodBlockMap U w s τ h β}

noncomputable instance goodHostBlockMapFintype {F : Type} [Field F] [Fintype F]
    {k b : ℕ} (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (s : ℕ) (τ : TypeSpace U s) (h : PartConsistent U s τ) :
    Fintype (GoodHostBlockMap U w s τ h) :=
  Fintype.ofInjective (fun β : GoodHostBlockMap U w s τ h => β.1) (by
    intro β γ hβγ
    cases β
    cases γ
    simpa using hβγ)

lemma NτFixed_le_goodEdgeData_card {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hs : 0 < s)
    [DecidableEq (HostParams F k b a D)] :
    NτFixed U (hostPartite P) w s τ ≤
      (Finset.univ.filter (fun β : GoodHostBlockMap U w s τ h =>
        P ∈ edgeData U w τ h hgood a D β.1)).card := by
  classical
  letI : Fintype (GoodHostBlockMap U w s τ h) :=
    goodHostBlockMapFintype U w s τ h
  let G := Finset.univ.filter (fun β : GoodHostBlockMap U w s τ h =>
    P ∈ edgeData U w τ h hgood a D β.1)
  let f : {β // β ∈ realizedHostBlockMaps U P w τ h} → {β // β ∈ G} :=
    fun β => ⟨⟨β.1, realized_good U P w τ h hs β.1 β.2⟩, by
      simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]
      exact realized_subset_edgeData U a D P w τ h hgood β.1 hwpart β.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hxy
  calc
    NτFixed U (hostPartite P) w s τ ≤
        (realizedHostBlockMaps U P w τ h).card :=
      NτFixed_le_card_realized U P w τ h
    _ ≤ G.card := by
      have h := Fintype.card_le_of_injective f hf
      simpa only [Fintype.card_coe] using h

lemma sum_NτFixed_le_sum_goodEdgeData {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hs : 0 < s)
    [DecidableEq (HostParams F k b a D)] :
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
      ∑ β : GoodHostBlockMap U w s τ h,
        (edgeData U w τ h hgood a D β.1).card := by
  classical
  letI : Fintype (GoodHostBlockMap U w s τ h) :=
    goodHostBlockMapFintype U w s τ h
  calc
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) ≤
        ∑ P : HostParams F k b a D,
          (Finset.univ.filter (fun β : GoodHostBlockMap U w s τ h =>
            P ∈ edgeData U w τ h hgood a D β.1)).card := by
      apply Finset.sum_le_sum
      intro P _
      exact NτFixed_le_goodEdgeData_card U a D P w τ h hgood hwpart hs
    _ = ∑ β : GoodHostBlockMap U w s τ h,
        (edgeData U w τ h hgood a D β.1).card := by
      have hcard : ∀ P : HostParams F k b a D,
          (Finset.univ.filter (fun β : GoodHostBlockMap U w s τ h =>
            P ∈ edgeData U w τ h hgood a D β.1)).card =
          ∑ β : GoodHostBlockMap U w s τ h,
            if P ∈ edgeData U w τ h hgood a D β.1 then 1 else 0 := by
        intro P
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      simp_rw [hcard]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro β _
      rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
      simp

noncomputable def hostBlockMapEquivPart {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    HostBlockMap F b U s τ h ≃
      PartRespectingBlockMaps U (hostPartite P) w s τ h where
  toFun β := ⟨β.1, by
    intro bl
    exact β.2 bl⟩
  invFun β := ⟨β.1, by
    intro bl
    exact β.2 bl⟩
  left_inv β := by
    cases β
    rfl
  right_inv β := by
    cases β
    rfl

lemma card_hostBlockMap_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    Fintype.card (HostBlockMap F b U s τ h) ≤
      Fintype.card F ^ (b * hτ U s τ) := by
  classical
  have hcard := card_partRespectingBlockMaps U (hostPartite P) w s τ h b
    (by
      intro i
      exact hostPart_fiber_card k b i)
  have heq : Fintype.card (HostBlockMap F b U s τ h) =
      Fintype.card (PartRespectingBlockMaps U (hostPartite P) w s τ h) :=
    Fintype.card_congr (hostBlockMapEquivPart U a D P w s τ h)
  rw [heq]
  exact hcard.le

lemma card_goodHostBlockMap_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (P : HostParams F k b a D)
    (w : U.R → HostVertex F k b) (s : ℕ) (τ : TypeSpace U s)
    (h : PartConsistent U s τ) :
    Fintype.card (GoodHostBlockMap U w s τ h) ≤
      Fintype.card F ^ (b * hτ U s τ) := by
  classical
  letI : Fintype (GoodHostBlockMap U w s τ h) :=
    goodHostBlockMapFintype U w s τ h
  have hle : Fintype.card (GoodHostBlockMap U w s τ h) ≤
      Fintype.card (HostBlockMap F b U s τ h) :=
    Fintype.card_le_of_injective (fun β : GoodHostBlockMap U w s τ h => β.1)
      (by
        intro β γ hβγ
        cases β
        cases γ
        simpa using hβγ)
  exact hle.trans (card_hostBlockMap_le U a D P w s τ h)

theorem Nτ_expectation_sum_le {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b s : ℕ}
    (U : PartiteRootedKHypergraph k) (a D : ℕ)
    (w : U.R → HostVertex F k b) (τ : TypeSpace U s)
    (h : PartConsistent U s τ)
    (hgood : EdgeTransversal U s τ h)
    (hwpart : ∀ r : U.R, (w r).1 = U.part r.1)
    (hτa : TypeAdmissible U s τ)
    (hs : 0 < s)
    (hq : (eτ U s τ).choose 2 < Fintype.card F)
    (hD : eτ U s τ ≤ D + 1)
    (P₀ : HostParams F k b a D)
    [DecidableEq (HostParams F k b a D)] :
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) *
        Fintype.card F ^ (a * eτ U s τ) ≤
      Fintype.card F ^ (b * hτ U s τ) *
        Fintype.card (HostParams F k b a D) := by
  classical
  letI : Fintype (GoodHostBlockMap U w s τ h) :=
    goodHostBlockMapFintype U w s τ h
  have hsum := sum_NτFixed_le_sum_goodEdgeData U a D w τ h hgood hwpart hs
  calc
    (∑ P : HostParams F k b a D,
        NτFixed U (hostPartite P) w s τ) *
        Fintype.card F ^ (a * eτ U s τ) ≤
        (∑ β : GoodHostBlockMap U w s τ h,
          (edgeData U w τ h hgood a D β.1).card) *
          Fintype.card F ^ (a * eτ U s τ) :=
      Nat.mul_le_mul_right _ hsum
    _ = ∑ β : GoodHostBlockMap U w s τ h,
        (edgeData U w τ h hgood a D β.1).card *
          Fintype.card F ^ (a * eτ U s τ) :=
      by rw [Finset.sum_mul]
    _ ≤ ∑ _β : GoodHostBlockMap U w s τ h,
        Fintype.card (HostParams F k b a D) := by
      apply Finset.sum_le_sum
      intro β _
      exact edgeData_card_mul_le U w τ h hgood a D β.1 hwpart β.2 hτa hq hD
    _ = Fintype.card (GoodHostBlockMap U w s τ h) *
        Fintype.card (HostParams F k b a D) := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ Fintype.card F ^ (b * hτ U s τ) *
        Fintype.card (HostParams F k b a D) :=
      Nat.mul_le_mul_right _ (card_goodHostBlockMap_le U a D P₀ w s τ h)

end Erdos571_hypergraph
