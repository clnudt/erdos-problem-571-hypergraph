import Erdos571_hypergraph_L15_Pieces

namespace Erdos571_hypergraph

/-- The host vertex assigned to a `U`-vertex by a point of the ambient space. -/
noncomputable def vertexImage {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (z : Fin (b * Fintype.card U.V) → F) (v : U.V) :
    HostVertex F k b :=
  (π (U.part v), fun j => z (varIndex U b v j))

lemma vertexImage_fst {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (z : Fin (b * Fintype.card U.V) → F) (v : U.V) :
    (vertexImage U π z v).1 = π (U.part v) := rfl

lemma vertexImage_snd {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (z : Fin (b * Fintype.card U.V) → F) (v : U.V) (j : Fin b) :
    (vertexImage U π z v).2 j = z (varIndex U b v j) := rfl

lemma rootPoly_mem_rootEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (r : U.R) (j : Fin b) :
    rootPoly U w r j ∈ rootEqs U w := by
  classical
  rw [rootEqs]
  exact Finset.mem_image.mpr ⟨(r, j), Finset.mem_univ _, rfl⟩

lemma vertexImage_root {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (hwpart : ∀ r : U.R, (w r).1 = π (U.part r.1))
    (z : Fin (b * Fintype.card U.V) → F)
    (hroot : ∀ g ∈ rootEqs U w, MvPolynomial.eval z g = 0) (r : U.R) :
    vertexImage U π z r.1 = w r := by
  classical
  ext j
  · rw [vertexImage_fst, hwpart]
  · rw [vertexImage_snd]
    have h := hroot (rootPoly U w r j) (rootPoly_mem_rootEqs U w r j)
    simp [rootPoly] at h
    exact sub_eq_zero.mp h

lemma pairNe_mem_pairNeEqs {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b) (p : SamePartPair U π) :
    pairNePoly (F := F) U p.1.1 p.1.2 (c p) ∈ pairNeEqs (F := F) U π c := by
  classical
  unfold pairNeEqs
  exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩

lemma vertexImage_injective {F : Type} [Field F] [DecidableEq F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (π : Equiv.Perm (Fin k))
    (c : SamePartPair U π → Fin b)
    (z : Fin (b * Fintype.card U.V) → F)
    (hne : ∀ h ∈ pairNeEqs U π c, MvPolynomial.eval z h ≠ 0) :
    Function.Injective (vertexImage U π z) := by
  classical
  intro v v' h
  by_contra hvv
  have hfst : π (U.part v) = π (U.part v') := by
    simpa [vertexImage] using congrArg Prod.fst h
  let p : SamePartPair U π := ⟨(v, v'), ⟨hvv, hfst⟩⟩
  have hmem := pairNe_mem_pairNeEqs (F := F) U π c p
  have hzero := hne _ hmem
  apply hzero
  have hsnd : (vertexImage U π z v).2 = (vertexImage U π z v').2 :=
    congrArg Prod.snd h
  have := congrFun hsnd (c p)
  simpa [pairNePoly, pairEqPoly, vertexImage, sub_eq_zero] using this

end Erdos571_hypergraph
