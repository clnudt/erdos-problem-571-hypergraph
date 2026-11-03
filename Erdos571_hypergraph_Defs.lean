import Mathlib

open Asymptotics
open Filter

namespace Erdos571_hypergraph

/-- A finite simple `k`-uniform hypergraph on a vertex type `V`. -/
structure KHypergraph (k : ℕ) (V : Type*) where
  edges : Finset (Finset V)
  edges_card : ∀ e ∈ edges, e.card = k

/-- A finite `k`-uniform hypergraph, with its vertex type bundled. -/
structure FiniteKHypergraph (k : ℕ) where
  V : Type
  [fintype : Fintype V]
  graph : KHypergraph k V

/-- A copy of `F` in `H`: an injective edge-preserving map. -/
def IsCopy {k : ℕ} {V W : Type*}
    (F : KHypergraph k V) (H : KHypergraph k W) : Prop :=
  ∃ f : V ↪ W, ∀ e ∈ F.edges, e.map f ∈ H.edges

/-- The Turán number `ex_k(n, F)`. -/
noncomputable def turanNumber {k : ℕ} (F : FiniteKHypergraph k) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ H : KHypergraph k (Fin n),
    ¬ IsCopy F.graph H ∧ H.edges.card = m}

/-- `ex_k(n, F) = Θ(n ^ α)`. -/
def RealizesExponent {k : ℕ} (F : FiniteKHypergraph k) (α : ℝ) : Prop :=
  Asymptotics.IsTheta atTop
    (fun n : ℕ => (turanNumber F n : ℝ))
    (fun n : ℕ => (n : ℝ) ^ α)

/-- A finite rooted `k`-uniform hypergraph. -/
structure RootedKHypergraph (k : ℕ) where
  V : Type
  [fintype : Fintype V]
  [decEq : DecidableEq V]
  G : KHypergraph k V
  R : Finset V
  proper : R ≠ Finset.univ
  nonempty : R.Nonempty

attribute [instance] RootedKHypergraph.fintype RootedKHypergraph.decEq

/-- A rooted graph is a rooted 2-uniform hypergraph. -/
abbrev RootedGraph := RootedKHypergraph 2

/-- The number of edges of a rooted `k`-graph meeting `S`. -/
noncomputable def eK {k : ℕ} (U : RootedKHypergraph k) (S : Finset U.V) : ℕ := by
  classical
  exact (U.G.edges.filter (fun e => (e ∩ S).Nonempty)).card

/-- `eT` is `eK` for rooted graphs. -/
noncomputable abbrev eT (T : RootedGraph) (S : Finset T.V) : ℕ := eK T S

/-- Balance with density `b / a`. -/
noncomputable def BalancedK {k : ℕ} (U : RootedKHypergraph k) (a b : ℕ) : Prop :=
  ∀ S : Finset U.V, S ⊆ Finset.univ \ U.R → S.Nonempty →
    b * S.card ≤ a * eK U S

/-- `Balanced` is `BalancedK` for rooted graphs. -/
noncomputable abbrev Balanced (T : RootedGraph) (a b : ℕ) : Prop := BalancedK T a b

/-- The embedding of the old vertices into the suspension. -/
def inlEmb (V : Type*) (n : ℕ) : V ↪ Sum V (Fin n) :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- The embedding of the new vertices into the suspension. -/
def inrEmb (V : Type*) (n : ℕ) : Fin n ↪ Sum V (Fin n) :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- The new vertices of the `k`-uniform suspension. -/
noncomputable def suspW (k : ℕ) (T : RootedGraph) :
    Finset (Sum T.V (Fin (k - 2))) :=
  (Finset.univ : Finset (Fin (k - 2))).map (inrEmb T.V (k - 2))

/-- The edge set of the `k`-uniform suspension. -/
noncomputable def suspEdges (k : ℕ) (T : RootedGraph) :
    Finset (Finset (Sum T.V (Fin (k - 2)))) :=
  T.G.edges.image (fun e => e.map (inlEmb T.V (k - 2)) ∪ suspW k T)

/-- The root set of the `k`-uniform suspension. -/
noncomputable def suspRoots (k : ℕ) (T : RootedGraph) :
    Finset (Sum T.V (Fin (k - 2))) :=
  T.R.map (inlEmb T.V (k - 2)) ∪ suspW k T

lemma susp_edge_card (k : ℕ) (hk : 2 ≤ k) (T : RootedGraph)
    {e : Finset T.V} (he : e ∈ T.G.edges) :
    (e.map (inlEmb T.V (k - 2)) ∪
      (Finset.univ : Finset (Fin (k - 2))).map (inrEmb T.V (k - 2))).card = k := by
  have hcard : e.card = 2 := T.G.edges_card e he
  have hdisj : Disjoint (e.map (inlEmb T.V (k - 2)))
      ((Finset.univ : Finset (Fin (k - 2))).map (inrEmb T.V (k - 2))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, hb'⟩
    cases hb'
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map,
    Finset.card_univ, Fintype.card_fin, hcard]
  omega

/-- The `k`-uniform suspension of a rooted graph. -/
noncomputable abbrev suspensionRooted (k : ℕ) (hk : 2 ≤ k) (T : RootedGraph) :
    RootedKHypergraph k := by
  classical
  have hex : ∃ x : T.V, x ∉ T.R := by
    by_contra h
    apply T.proper
    ext x
    simp only [Finset.mem_univ, iff_true]
    by_contra hx
    exact h ⟨x, hx⟩
  let x := Classical.choose hex
  have hx : x ∉ T.R := Classical.choose_spec hex
  have hnot1 : Sum.inl x ∉ T.R.map (inlEmb T.V (k - 2)) := by
    intro hmem
    rcases Finset.mem_map.mp hmem with ⟨y, hy, hyx⟩
    have hyx' : y = x := Sum.inl.inj hyx
    subst hyx'
    exact hx hy
  have hnot2 : Sum.inl x ∉
      (Finset.univ : Finset (Fin (k - 2))).map (inrEmb T.V (k - 2)) := by
    intro hmem
    rcases Finset.mem_map.mp hmem with ⟨j, hj, hjx⟩
    cases hjx
  have hnot : Sum.inl x ∉ suspRoots k T := by
    simp only [suspRoots, Finset.mem_union]
    exact fun h => h.elim hnot1 hnot2
  exact {
    V := Sum T.V (Fin (k - 2))
    G := {
      edges := suspEdges k T
      edges_card := by
        intro e he
        rcases Finset.mem_image.mp he with ⟨e0, he0, rfl⟩
        exact susp_edge_card k hk T he0
    }
    R := suspRoots k T
    proper := by
      intro hEq
      have : Sum.inl x ∈ suspRoots k T := by
        rw [hEq]
        exact Finset.mem_univ _
      exact hnot this
    nonempty := by
      rcases T.nonempty with ⟨r, hr⟩
      exact ⟨Sum.inl r, by
        rw [suspRoots, Finset.mem_union]
        left
        exact Finset.mem_map.mpr ⟨r, hr, rfl⟩⟩
  }

end Erdos571_hypergraph
