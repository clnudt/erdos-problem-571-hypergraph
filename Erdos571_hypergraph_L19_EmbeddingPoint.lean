import Erdos571_hypergraph_L18_FirstDiff

namespace Erdos571_hypergraph

/-- The ambient point determined by a compatible embedding. -/
noncomputable def embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π) :
    Fin (b * Fintype.card U.V) → F :=
  fun q =>
    let p := (vertexVarEquiv U b).symm q
    (φ.toFun p.1).2 p.2

lemma vertexImage_embeddingPoint {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π) (v : U.V) :
    vertexImage U π (embeddingPoint (P := P) U π φ) v = φ.toFun v := by
  classical
  apply Prod.ext
  · change π (U.part v) = (φ.toFun v).1
    exact (φ.part_compat v).symm
  · funext j
    rw [vertexImage_snd]
    simp [embeddingPoint, varIndex]

/-- The choice of the first differing coordinate induced by an embedding. -/
noncomputable def embeddingChoice {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π) :
    SamePartPair U π → Fin b :=
  fun p =>
    firstDiff (φ.toFun p.1.1).2 (φ.toFun p.1.2).2 (by
      intro h
      have hfst : (φ.toFun p.1.1).1 = (φ.toFun p.1.2).1 := by
        have h1 : (φ.toFun p.1.1).1 = π (U.part p.1.1) :=
          φ.part_compat p.1.1
        have h2 : (φ.toFun p.1.2).1 = π (U.part p.1.2) :=
          φ.part_compat p.1.2
        rw [h1, h2, p.2.2]
      exact p.2.1 (φ.inj (Prod.ext hfst h)))

lemma embeddingChoice_spec {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    (p : SamePartPair U π) :
    (φ.toFun p.1.1).2 (embeddingChoice U π φ p) ≠
      (φ.toFun p.1.2).2 (embeddingChoice U π φ p) :=
  firstDiff_spec _ _ _

lemma embeddingChoice_min {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ}
    (U : PartiteRootedKHypergraph k) {P : HostParams F k b a D}
    {w : U.R → HostVertex F k b}
    (π : Equiv.Perm (Fin k))
    (φ : CompatibleEmbedding U (hostPartite P) w π)
    (p : SamePartPair U π) {j : Fin b}
    (hj : j < embeddingChoice U π φ p) :
    (φ.toFun p.1.1).2 j = (φ.toFun p.1.2).2 j :=
  firstDiff_min _ _ _ hj

end Erdos571_hypergraph
