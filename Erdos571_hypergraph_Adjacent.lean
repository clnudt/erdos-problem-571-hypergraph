import Erdos571_hypergraph_EdgePerm
import Erdos571_hypergraph_PartiteSuspension

namespace Erdos571_hypergraph

lemma suspEdge_mem {k : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    {eT : Finset B.T.V} (heT : eT ∈ B.T.G.edges) :
    eT.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T ∈
      (suspensionPartite k hk B).G.edges := by
  change _ ∈ suspEdges k B.T
  exact Finset.mem_image.mpr ⟨eT, heT, rfl⟩

lemma edgePerm_eq_of_shared_Tvertex {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (X : PartiteKHypergraph k)
    (f : (suspensionPartite k hk B).V ↪ X.V)
    {eT1 eT2 : Finset B.T.V}
    (h1 : eT1 ∈ B.T.G.edges) (h2 : eT2 ∈ B.T.G.edges)
    (hfe1 : (eT1.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map f ∈ X.G.edges)
    (hfe2 : (eT2.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map f ∈ X.G.edges)
    {v : B.T.V} (hv1 : v ∈ eT1) (hv2 : v ∈ eT2) :
    edgePerm f (suspEdge_mem hk B h1) hfe1 =
      edgePerm f (suspEdge_mem hk B h2) hfe2 := by
  classical
  let U := suspensionPartite k hk B
  let e1 : Finset U.V := eT1.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T
  let e2 : Finset U.V := eT2.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T
  have he1 : e1 ∈ U.G.edges := by
    dsimp only [e1, U]
    exact suspEdge_mem hk B h1
  have he2 : e2 ∈ U.G.edges := by
    dsimp only [e2, U]
    exact suspEdge_mem hk B h2
  have hfe1' : e1.map f ∈ X.G.edges := hfe1
  have hfe2' : e2.map f ∈ X.G.edges := hfe2
  change edgePerm f he1 hfe1' = edgePerm f he2 hfe2'
  let Wparts : Finset (Fin k) :=
    (Finset.univ : Finset (Fin (k - 2))).image
      (fun j => suspPart hk B (Sum.inr j))
  let S : Finset (Fin k) := insert (suspPart hk B (Sum.inl v)) Wparts
  have hWcard : Wparts.card = k - 2 := by
    dsimp only [Wparts]
    rw [Finset.card_image_of_injective]
    · simp
    · exact suspPart_inr_injective hk B
  have hvnot : suspPart hk B (Sum.inl v) ∉ Wparts := by
    intro hv
    rcases Finset.mem_image.mp hv with ⟨j, -, hj⟩
    have h1 := suspPart_inl_val hk B v
    have h2 : (suspPart hk B (Sum.inr j)).1 = j.1 + 2 := by
      rw [suspPart_inr]
    have hval := congrArg Fin.val hj
    omega
  have hScard : S.card = k - 1 := by
    dsimp only [S]
    rw [Finset.card_insert_of_notMem hvnot, hWcard]
    omega
  apply perm_eq_of_agree _ _ hScard
  intro i hi
  dsimp only [S] at hi
  rw [Finset.mem_insert] at hi
  rcases hi with rfl | hiW
  · -- shared vertex `inl v`
    have hx1 : Sum.inl v ∈ eT1.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T :=
      (mem_suspEdge_inl B.T).mpr hv1
    have hx2 : Sum.inl v ∈ eT2.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T :=
      (mem_suspEdge_inl B.T).mpr hv2
    have hx1' : Sum.inl v ∈ e1 := hx1
    have hx2' : Sum.inl v ∈ e2 := hx2
    change (edgePerm f he1 hfe1') (U.part (Sum.inl v)) =
      (edgePerm f he2 hfe2') (U.part (Sum.inl v))
    rw [edgePerm_apply f he1 hfe1' hx1',
      edgePerm_apply f he2 hfe2' hx2']
  · rcases Finset.mem_image.mp hiW with ⟨j, -, hj⟩
    subst hj
    have hx1 : Sum.inr j ∈ eT1.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T :=
      mem_suspEdge_inr B.T
    have hx2 : Sum.inr j ∈ eT2.map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T :=
      mem_suspEdge_inr B.T
    have hx1' : Sum.inr j ∈ e1 := by
      dsimp only [e1]
      exact mem_suspEdge_inr B.T
    have hx2' : Sum.inr j ∈ e2 := by
      dsimp only [e2]
      exact mem_suspEdge_inr B.T
    change (edgePerm f he1 hfe1') (U.part (Sum.inr j)) =
      (edgePerm f he2 hfe2') (U.part (Sum.inr j))
    rw [edgePerm_apply f he1 hfe1' hx1',
      edgePerm_apply f he2 hfe2' hx2']

lemma edgePerm_eq_of_adj {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (X : PartiteKHypergraph k)
    (f : (suspensionPartite k hk B).V ↪ X.V)
    (hfe : ∀ e : {e : Finset B.T.V // e ∈ B.T.G.edges},
      ((e.1).map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map f ∈ X.G.edges)
    {e1 e2 : {e : Finset B.T.V // e ∈ B.T.G.edges}}
    (hshare : (e1.1 ∩ e2.1).Nonempty) :
    edgePerm f (suspEdge_mem hk B e1.2) (hfe e1) =
      edgePerm f (suspEdge_mem hk B e2.2) (hfe e2) := by
  rcases hshare with ⟨v, hv⟩
  rcases Finset.mem_inter.mp hv with ⟨hv1, hv2⟩
  exact edgePerm_eq_of_shared_Tvertex hk B X f e1.2 e2.2
    (hfe e1) (hfe e2) hv1 hv2

lemma edgePerm_eq_of_chain {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (X : PartiteKHypergraph k)
    (f : (suspensionPartite k hk B).V ↪ X.V)
    (hfe : ∀ e : {e : Finset B.T.V // e ∈ B.T.G.edges},
      ((e.1).map (inlEmb B.T.V (k - 2)) ∪ suspW k B.T).map f ∈ X.G.edges)
    (e1 e2 : {e : Finset B.T.V // e ∈ B.T.G.edges}) :
    edgePerm f (suspEdge_mem hk B e1.2) (hfe e1) =
      edgePerm f (suspEdge_mem hk B e2.2) (hfe e2) := by
  classical
  let P : {e : Finset B.T.V // e ∈ B.T.G.edges} → Prop :=
    fun a => edgePerm f (suspEdge_mem hk B a.2) (hfe a) =
      edgePerm f (suspEdge_mem hk B e2.2) (hfe e2)
  have h := (B.connected e1 e2).head_induction_on
    (motive := fun a _ => P a) (refl := rfl)
    (head := by
      intro a c hstep hchain ih
      exact (edgePerm_eq_of_adj hk B X f hfe hstep).trans ih)
  exact h

end Erdos571_hypergraph
