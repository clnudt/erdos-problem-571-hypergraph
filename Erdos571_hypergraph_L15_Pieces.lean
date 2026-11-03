import Erdos571_hypergraph_L14_Embedding

namespace Erdos571_hypergraph

/-- Pairs of distinct `U`-vertices lying in the same host part under `π`. -/
abbrev SamePartPair {k : ℕ} (U : PartiteRootedKHypergraph k)
    (π : Equiv.Perm (Fin k)) :=
  {p : U.V × U.V // p.1 ≠ p.2 ∧ π (U.part p.1) = π (U.part p.2)}

noncomputable instance samePartPairFintype {k : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k)) :
    Fintype (SamePartPair U π) :=
  Fintype.ofInjective (fun p : SamePartPair U π => p.1) (by
    intro a b h
    exact Subtype.ext h)

/-- The equations fixing the root coordinates. -/
noncomputable def rootEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b) :
    Finset (MvPolynomial (Fin (b * Fintype.card U.V)) F) :=
  Finset.univ.image (fun q : U.R × Fin b => rootPoly U w q.1 q.2)

/-- The edge equations. -/
noncomputable def edgeEqs {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k)) :
    Finset (MvPolynomial (Fin (b * Fintype.card U.V)) F) :=
  Finset.univ.image (fun q : {e : Finset U.V // e ∈ U.G.edges} × Fin a =>
    edgePoly P U q.1.2 π q.2)

/-- The equality equations for a choice of the first differing coordinate. -/
noncomputable def pairEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) :
    Finset (MvPolynomial (Fin (b * Fintype.card U.V)) F) :=
  Finset.univ.image (fun q : SamePartPair U π × Fin b =>
    if q.2 < c q.1 then pairEqPoly U q.1.1.1 q.1.1.2 q.2 else 0)

/-- The nonvanishing conditions for a choice of the first differing coordinate. -/
noncomputable def pairNeEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) :
    Finset (MvPolynomial (Fin (b * Fintype.card U.V)) F) :=
  Finset.univ.image (fun p : SamePartPair U π =>
    pairNePoly U p.1.1 p.1.2 (c p))

/-- The constructible piece defined by a root position, a part permutation,
and a choice of the first differing coordinate for every same-part pair. -/
noncomputable def pieceSet {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b) :
    Set (Fin (b * Fintype.card U.V) → F) :=
  {z | (∀ g ∈ rootEqs U w ∪ edgeEqs P U π ∪ pairEqs U π c,
      MvPolynomial.eval z g = 0) ∧
    (∀ h ∈ pairNeEqs U π c, MvPolynomial.eval z h ≠ 0)}

lemma rootEqs_card_le {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b) :
    (rootEqs U w).card ≤ b * Fintype.card U.R := by
  classical
  rw [rootEqs]
  calc
    (Finset.univ.image (fun q : U.R × Fin b => rootPoly U w q.1 q.2)).card ≤
        Fintype.card (U.R × Fin b) := Finset.card_image_le
    _ = Fintype.card U.R * b := by simp
    _ = b * Fintype.card U.R := Nat.mul_comm _ _

lemma edgeEqs_card_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k)) :
    (edgeEqs P U π).card ≤ a * U.G.edges.card := by
  classical
  rw [edgeEqs]
  calc
    (Finset.univ.image (fun q : {e : Finset U.V // e ∈ U.G.edges} × Fin a =>
      edgePoly P U q.1.2 π q.2)).card ≤
        Fintype.card ({e : Finset U.V // e ∈ U.G.edges} × Fin a) :=
      Finset.card_image_le
    _ = U.G.edges.card * a := by simp [Fintype.card_coe]
    _ = a * U.G.edges.card := Nat.mul_comm _ _

lemma pairEqs_card_le {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) :
    (pairEqs (F := F) U π c).card ≤ b * Fintype.card (SamePartPair U π) := by
  classical
  rw [pairEqs]
  calc
    (Finset.univ.image (fun q : SamePartPair U π × Fin b =>
      if q.2 < c q.1 then pairEqPoly (F := F) U q.1.1.1 q.1.1.2 q.2 else 0)).card ≤
        Fintype.card (SamePartPair U π × Fin b) := Finset.card_image_le
    _ = Fintype.card (SamePartPair U π) * b := by simp
    _ = b * Fintype.card (SamePartPair U π) := Nat.mul_comm _ _

lemma pairNeEqs_card_le {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) :
    (pairNeEqs (F := F) U π c).card ≤ Fintype.card (SamePartPair U π) := by
  classical
  rw [pairNeEqs]
  calc
    (Finset.univ.image (fun p : SamePartPair U π =>
      pairNePoly (F := F) U p.1.1 p.1.2 (c p))).card ≤
        Fintype.card (SamePartPair U π) := Finset.card_image_le

/-- Evaluation of an edge polynomial is the original host polynomial evaluated
at the selected vertex tuple. -/
lemma edgePoly_eval {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) {e : Finset U.V} (he : e ∈ U.G.edges)
    (π : Equiv.Perm (Fin k)) (j : Fin a)
    (z : Fin (b * Fintype.card U.V) → F) :
    MvPolynomial.eval z (edgePoly P U he π j) =
      evalAtTuple (P.coeffs j)
        (fun i : Fin k => fun l : Fin b =>
          z (edgeVar U b he π (finProdFinEquiv (i, l)))) := by
  classical
  rw [edgePoly, MvPolynomial.eval_rename]
  have h : (z ∘ edgeVar U b he π) =
      flattenTuple (fun i : Fin k => fun l : Fin b =>
        z (edgeVar U b he π (finProdFinEquiv (i, l)))) := by
    funext q
    simp [Function.comp, flattenTuple, edgeVar]
  rw [h]
  exact (evalAtTuple_toMvPoly (P.coeffs j) _).symm

/-- Each piece is constructible, with the complexity bound used in the
manuscript. -/
theorem pieceSet_isConstructible (q : ℕ) [Fact q.Prime] {k b a D : ℕ}
    (P : HostParams (ZMod q) k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex (ZMod q) k b)
    (π : Equiv.Perm (Fin k)) (c : SamePartPair U π → Fin b) :
    IsConstructible q (b * Fintype.card U.V)
      (b * Fintype.card U.R + a * U.G.edges.card +
        (b + 1) * Fintype.card (SamePartPair U π))
      (max D 1) (pieceSet P U w π c) := by
  classical
  refine ⟨rootEqs U w ∪ edgeEqs P U π ∪ pairEqs (F := ZMod q) U π c,
    pairNeEqs (F := ZMod q) U π c, ?_, ?_, ?_, ?_⟩
  · -- cardinality bound
    have hroot := rootEqs_card_le (F := ZMod q) U w
    have hedge := edgeEqs_card_le (F := ZMod q) P U π
    have hpair := pairEqs_card_le (F := ZMod q) U π c
    have hne := pairNeEqs_card_le (F := ZMod q) U π c
    have hG : (rootEqs U w ∪ edgeEqs P U π ∪ pairEqs (F := ZMod q) U π c).card ≤
        (rootEqs U w).card + (edgeEqs P U π).card +
          (pairEqs (F := ZMod q) U π c).card := by
      calc
        (rootEqs U w ∪ edgeEqs P U π ∪ pairEqs (F := ZMod q) U π c).card ≤
            (rootEqs U w ∪ edgeEqs P U π).card +
              (pairEqs (F := ZMod q) U π c).card := Finset.card_union_le _ _
        _ ≤ ((rootEqs U w).card + (edgeEqs P U π).card) +
              (pairEqs (F := ZMod q) U π c).card := by
          gcongr
          exact Finset.card_union_le _ _
    have hm : (b + 1) * Fintype.card (SamePartPair U π) =
        b * Fintype.card (SamePartPair U π) +
          Fintype.card (SamePartPair U π) := by ring
    omega
  · -- equations have degree at most D' = max D 1
    intro g hg
    rw [Finset.mem_union] at hg
    rcases hg with hg | hg
    · rw [Finset.mem_union] at hg
      rcases hg with hg | hg
      · rw [rootEqs] at hg
        rcases Finset.mem_image.mp hg with ⟨r, -, rfl⟩
        exact (rootPoly_totalDegree (F := ZMod q) U w r.1 r.2).trans
          (le_max_right _ _)
      · rw [edgeEqs] at hg
        rcases Finset.mem_image.mp hg with ⟨e, -, rfl⟩
        exact (edgePoly_totalDegree P U e.1.2 π e.2).trans
          (le_max_left _ _)
    · rw [pairEqs] at hg
      rcases Finset.mem_image.mp hg with ⟨p, -, hp⟩
      rw [← hp]
      by_cases h : p.2 < c p.1
      · simp only [h, if_true]
        exact (pairEqPoly_totalDegree (F := ZMod q) U p.1.1.1 p.1.1.2 p.2).trans
          (le_max_right _ _)
      · simp only [h, if_false]
        exact Nat.zero_le _
  · -- nonvanishing equations have degree at most D'
    intro h hh
    rw [pairNeEqs] at hh
    rcases Finset.mem_image.mp hh with ⟨p, -, rfl⟩
    exact (pairEqPoly_totalDegree (F := ZMod q) U p.1.1 p.1.2 (c p)).trans
      (le_max_right _ _)
  · rfl

end Erdos571_hypergraph
