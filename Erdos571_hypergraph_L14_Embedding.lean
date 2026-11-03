import Erdos571_hypergraph_L13_PolyEncode
import Erdos571_hypergraph_EdgePerm

namespace Erdos571_hypergraph

/-- The equivalence between `(vertex, coordinate)` pairs and the flattened
ambient coordinates used for the constructible sets. -/
noncomputable def vertexVarEquiv {k : ℕ} (U : PartiteRootedKHypergraph k)
    (b : ℕ) : U.V × Fin b ≃ Fin (b * Fintype.card U.V) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_comm _ _)

/-- The flattened coordinate of the `j`-th coordinate of `v`. -/
noncomputable def varIndex {k : ℕ} (U : PartiteRootedKHypergraph k)
    (b : ℕ) (v : U.V) (j : Fin b) : Fin (b * Fintype.card U.V) :=
  vertexVarEquiv U b (v, j)

/-- For an edge `e` and a part permutation `π`, the tuple coordinate of host
part `i`, coordinate `j`, is the coordinate of the unique vertex of `e` in
U-part `π⁻¹ i`. -/
noncomputable def edgeVar {k : ℕ} (U : PartiteRootedKHypergraph k)
    (b : ℕ) {e : Finset U.V} (he : e ∈ U.G.edges)
    (π : Equiv.Perm (Fin k)) (q : Fin (k * b)) :
    Fin (b * Fintype.card U.V) :=
  let p := finProdFinEquiv.symm q
  varIndex U b (edgeVertexEmb he (π.symm p.1)) p.2

/-- The edge polynomial in the ambient variables: the original host polynomial
with the `k` host vertices replaced by the selected U-vertices. -/
noncomputable def edgePoly {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) {e : Finset U.V} (he : e ∈ U.G.edges)
    (π : Equiv.Perm (Fin k)) (j : Fin a) :
    MvPolynomial (Fin (b * Fintype.card U.V)) F :=
  MvPolynomial.rename (edgeVar U b he π) (toMvPoly (P.coeffs j))

lemma edgePoly_totalDegree {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) {e : Finset U.V} (he : e ∈ U.G.edges)
    (π : Equiv.Perm (Fin k)) (j : Fin a) :
    (edgePoly P U he π j).totalDegree ≤ D := by
  classical
  exact (MvPolynomial.totalDegree_rename_le _ _).trans
    (toMvPoly_totalDegree (P.coeffs j))

/-- The linear equation fixing a root coordinate. -/
noncomputable def rootPoly {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (r : U.R) (j : Fin b) :
    MvPolynomial (Fin (b * Fintype.card U.V)) F :=
  MvPolynomial.X (varIndex U b r.1 j) - MvPolynomial.C ((w r).2 j)

lemma rootPoly_totalDegree {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (r : U.R) (j : Fin b) :
    (rootPoly U w r j).totalDegree ≤ 1 := by
  classical
  rw [rootPoly, sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_C]
    omega

/-- The linear form equating two vertex coordinates. -/
noncomputable def pairEqPoly {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (v v' : U.V) (j : Fin b) :
    MvPolynomial (Fin (b * Fintype.card U.V)) F :=
  MvPolynomial.X (varIndex U b v j) - MvPolynomial.X (varIndex U b v' j)

/-- The linear form detecting a difference of two vertex coordinates. -/
noncomputable def pairNePoly {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (v v' : U.V) (j : Fin b) :
    MvPolynomial (Fin (b * Fintype.card U.V)) F :=
  pairEqPoly (F := F) U v v' j

lemma pairEqPoly_totalDegree {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (v v' : U.V) (j : Fin b) :
    (pairEqPoly (F := F) U v v' j).totalDegree ≤ 1 := by
  classical
  rw [pairEqPoly, sub_eq_add_neg]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_X]
  · rw [MvPolynomial.totalDegree_neg, MvPolynomial.totalDegree_X]

end Erdos571_hypergraph
