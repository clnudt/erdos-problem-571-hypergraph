import Erdos571_hypergraph_L6_Transport

namespace Erdos571_hypergraph

/-- The forbidden hypergraph `F_{k,r}` as a bundled finite `k`-graph. -/
noncomputable def FkrFinite {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (p : ℕ) (hp : 0 < p) : FiniteKHypergraph k where
  V := (partitePower (suspensionPartite k hk B) p hp).V
  graph := (partitePower (suspensionPartite k hk B) p hp).G

/-- Relabelling vertices preserves the number of edges. -/
lemma card_mapKHypergraph {k : ℕ} {V W : Type*}
    (e : V ≃ W) (H : KHypergraph k V) :
    (mapKHypergraph e H).edges.card = H.edges.card := by
  classical
  unfold mapKHypergraph
  rw [Finset.card_image_of_injOn]
  intro s _ t _ h
  exact Finset.map_injective e.toEmbedding h

/-- A free host on `k q^b` vertices gives a lower bound for the Turán number. -/
theorem turanNumber_ge_host {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D p : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph) (hp : 0 < p)
    (P : HostParams F k b a D)
    (hfree : ¬ IsCopy
      (partitePower (suspensionPartite k hk B) p hp).G
      (hostPartite P).G) :
    (hostEdges P).card ≤
      turanNumber (FkrFinite hk B p hp)
        (Fintype.card (HostVertex F k b)) := by
  classical
  let e : HostVertex F k b ≃ Fin (Fintype.card (HostVertex F k b)) :=
    Fintype.equivFin _
  let H : KHypergraph k (Fin (Fintype.card (HostVertex F k b))) :=
    mapKHypergraph e (hostPartite P).G
  have hcard : H.edges.card = (hostEdges P).card :=
    card_mapKHypergraph e (hostPartite P).G
  have hnot : ¬ IsCopy (FkrFinite hk B p hp).graph H := by
    intro h
    apply hfree
    exact (isCopy_mapKHypergraph_iff e
      (partitePower (suspensionPartite k hk B) p hp).G
      (hostPartite P).G).mp (by simpa [H, FkrFinite] using h)
  rw [← hcard]
  exact le_turanNumber (FkrFinite hk B p hp) ⟨H, hnot, rfl⟩

end Erdos571_hypergraph
