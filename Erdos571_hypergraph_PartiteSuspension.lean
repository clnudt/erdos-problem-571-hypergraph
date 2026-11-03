import Erdos571_hypergraph_L1
import Erdos571_hypergraph_L3_Partite

namespace Erdos571_hypergraph

/-- A rooted graph together with a fixed bipartition. -/
structure BipartiteRootedGraph where
  T : RootedGraph
  part : T.V → Fin 2
  edge_part : ∀ e ∈ T.G.edges, ∀ i : Fin 2,
    ∃! v : T.V, v ∈ e ∧ part v = i
  connected : ∀ e1 e2 : {e : Finset T.V // e ∈ T.G.edges},
    Relation.ReflTransGen
      (fun e e' : {e : Finset T.V // e ∈ T.G.edges} =>
        (e.1 ∩ e'.1).Nonempty) e1 e2
  edge_nonempty : T.G.edges.Nonempty
  vertex_covered : ∀ v : T.V, ∃ e ∈ T.G.edges, v ∈ e

/-- The part assignment of the `k`-uniform suspension. -/
noncomputable def suspPart {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) :
    Sum B.T.V (Fin (k - 2)) → Fin k
  | Sum.inl v => if B.part v = 0 then ⟨0, by omega⟩ else ⟨1, by omega⟩
  | Sum.inr j => ⟨j.1 + 2, by omega⟩

lemma suspPart_inl {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (v : B.T.V) :
    suspPart hk B (Sum.inl v) =
      if B.part v = 0 then (⟨0, by omega⟩ : Fin k) else ⟨1, by omega⟩ := rfl

lemma suspPart_inl_zero {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    {v : B.T.V} :
    suspPart hk B (Sum.inl v) = (⟨0, by omega⟩ : Fin k) ↔
      B.part v = 0 := by
  rw [suspPart_inl]
  by_cases h : B.part v = 0 <;> simp [h]

lemma suspPart_inr {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (j : Fin (k - 2)) :
    suspPart hk B (Sum.inr j) = ⟨j.1 + 2, by omega⟩ := rfl

lemma suspPart_inr_ne_zero {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (j : Fin (k - 2)) :
    suspPart hk B (Sum.inr j) ≠ (⟨0, by omega⟩ : Fin k) := by
  rw [suspPart_inr]
  intro h
  have := congrArg Fin.val h
  simp at this

lemma suspPart_inr_ne_one {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (j : Fin (k - 2)) :
    suspPart hk B (Sum.inr j) ≠ (⟨1, by omega⟩ : Fin k) := by
  rw [suspPart_inr]
  intro h
  have := congrArg Fin.val h
  simp at this

lemma mem_suspEdge_inl {k : ℕ} (T : RootedGraph)
    {eT : Finset T.V} {v : T.V} :
    Sum.inl v ∈ eT.map (inlEmb T.V (k - 2)) ∪ suspW k T ↔
      v ∈ eT := by
  simp [suspW, inlEmb, inrEmb, Finset.mem_map]

lemma mem_suspEdge_inr {k : ℕ} (T : RootedGraph)
    {eT : Finset T.V} {j : Fin (k - 2)} :
    Sum.inr j ∈ eT.map (inlEmb T.V (k - 2)) ∪ suspW k T := by
  simp [suspW, inlEmb, inrEmb, Finset.mem_map]

lemma not_mem_suspEdge_inl_of_inr {k : ℕ} (T : RootedGraph)
    {eT : Finset T.V} {j : Fin (k - 2)} :
    Sum.inr j ∉ eT.map (inlEmb T.V (k - 2)) := by
  simp [inlEmb, Finset.mem_map]

lemma not_mem_suspEdge_inr_of_inl {k : ℕ} (T : RootedGraph)
    {eT : Finset T.V} {v : T.V} :
    Sum.inl v ∉ suspW k T := by
  simp [suspW, inrEmb, Finset.mem_map]

lemma suspPart_inl_eq_one {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    {v : B.T.V} :
    suspPart hk B (Sum.inl v) = (⟨1, by omega⟩ : Fin k) ↔
      B.part v ≠ 0 := by
  rw [suspPart_inl]
  by_cases h : B.part v = 0 <;> simp [h]

lemma suspPart_inl_val {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (v : B.T.V) :
    (suspPart hk B (Sum.inl v)).1 = 0 ∨
      (suspPart hk B (Sum.inl v)).1 = 1 := by
  rw [suspPart_inl]
  by_cases h : B.part v = 0 <;> simp [h]

lemma suspEdge_part {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    {eT : Finset B.T.V} (heT : eT ∈ B.T.G.edges) :
    ∀ i : Fin k, ∃! x : Sum B.T.V (Fin (k - 2)),
      x ∈ eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T ∧
        suspPart hk B x = i := by
  intro i
  by_cases hi0 : i = (⟨0, by omega⟩ : Fin k)
  · subst i
    obtain ⟨v0, ⟨hv0e, hv0p⟩, huniq⟩ :=
      B.edge_part eT heT (⟨0, by omega⟩ : Fin 2)
    refine ⟨Sum.inl v0, ⟨?_, ?_⟩, ?_⟩
    · exact (mem_suspEdge_inl B.T).mpr hv0e
    · exact (suspPart_inl_zero hk B).mpr hv0p
    · intro y hy
      cases y with
      | inl v =>
        have hve : v ∈ eT := (mem_suspEdge_inl B.T).mp hy.1
        have hv0 : B.part v = 0 := (suspPart_inl_zero hk B).mp hy.2
        have := huniq v ⟨hve, hv0⟩
        subst this
        rfl
      | inr j =>
        exact absurd hy.2 (suspPart_inr_ne_zero hk B j)
  · by_cases hi1 : i = (⟨1, by omega⟩ : Fin k)
    · subst i
      obtain ⟨v0, ⟨hv0e, hv0p⟩, huniq⟩ :=
        B.edge_part eT heT (⟨1, by omega⟩ : Fin 2)
      refine ⟨Sum.inl v0, ⟨?_, ?_⟩, ?_⟩
      · exact (mem_suspEdge_inl B.T).mpr hv0e
      · exact (suspPart_inl_eq_one hk B).mpr (by
          intro h
          have := B.part v0
          rw [h] at hv0p
          exact Fin.zero_ne_one hv0p)
      · intro y hy
        cases y with
        | inl v =>
          have hve : v ∈ eT := (mem_suspEdge_inl B.T).mp hy.1
          have hv1 : B.part v ≠ 0 := (suspPart_inl_eq_one hk B).mp hy.2
          have hv : B.part v = 1 := by
            have := B.edge_part eT heT
            -- bipartite: part is 0 or 1
            have hlt : (B.part v).1 < 2 := (B.part v).2
            omega
          have := huniq v ⟨hve, hv⟩
          subst this
          rfl
        | inr j =>
          exact absurd hy.2 (suspPart_inr_ne_one hk B j)
    · have hi2 : 2 ≤ i.1 := by
        have h0 : i.1 ≠ 0 := by
          intro h
          apply hi0
          exact Fin.ext h
        have h1 : i.1 ≠ 1 := by
          intro h
          apply hi1
          exact Fin.ext h
        omega
      let j : Fin (k - 2) := ⟨i.1 - 2, by omega⟩
      refine ⟨Sum.inr j, ⟨mem_suspEdge_inr B.T, ?_⟩, ?_⟩
      · rw [suspPart_inr]
        apply Fin.ext
        simp [j]
        omega
      · intro y hy
        cases y with
        | inl v =>
          have hv := suspPart_inl_val hk B v
          have hival : (suspPart hk B (Sum.inl v)).1 = i.1 :=
            congrArg Fin.val hy.2
          omega
        | inr j' =>
          have hpart : suspPart hk B (Sum.inr j') = i := hy.2
          rw [suspPart_inr] at hpart
          have hj : j' = j := by
            apply Fin.ext
            have := congrArg Fin.val hpart
            simp [j] at this ⊢
            omega
          subst hj
          rfl

/-- The `k`-uniform suspension as a partite rooted `k`-graph. -/
noncomputable abbrev suspensionPartite (k : ℕ) (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) : PartiteRootedKHypergraph k :=
{ suspensionRooted k hk B.T with
  part := suspPart hk B
  edge_part := by
    intro e he i
    rcases Finset.mem_image.mp (by
        simpa [suspensionRooted, suspEdges] using he) with ⟨eT, heT, rfl⟩
    exact suspEdge_part hk B heT i }

lemma suspPart_inr_injective {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) :
    Function.Injective (fun j : Fin (k - 2) => suspPart hk B (Sum.inr j)) := by
  intro j j' h
  simp only [suspPart_inr] at h
  have := congrArg Fin.val h
  simp at this
  exact Fin.ext (by omega)

lemma susp_vertex_covered {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph)
    (v : (suspensionPartite k hk B).V) :
    ∃ e ∈ (suspensionPartite k hk B).G.edges, v ∈ e := by
  classical
  let U := suspensionPartite k hk B
  cases v with
  | inl t =>
    obtain ⟨eT, heT, ht⟩ := B.vertex_covered t
    refine ⟨eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T, ?_, ?_⟩
    · change _ ∈ suspEdges k B.T
      exact Finset.mem_image.mpr ⟨eT, heT, rfl⟩
    · exact (mem_suspEdge_inl B.T).mpr ht
  | inr j =>
    obtain ⟨eT, heT⟩ := B.edge_nonempty
    refine ⟨eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T, ?_, ?_⟩
    · change _ ∈ suspEdges k B.T
      exact Finset.mem_image.mpr ⟨eT, heT, rfl⟩
    · exact mem_suspEdge_inr B.T

end Erdos571_hypergraph
