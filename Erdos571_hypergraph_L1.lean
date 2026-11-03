import Erdos571_hypergraph_Defs

namespace Erdos571_hypergraph

lemma disjoint_inl_suspW (k : ℕ) (T : RootedGraph) (e : Finset T.V) :
    Disjoint (e.map (inlEmb T.V (k - 2))) (suspW k T) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
  rcases Finset.mem_map.mp hy with ⟨j, hj, hjx⟩
  cases hjx

lemma mem_suspRoots_inl (k : ℕ) (T : RootedGraph) (v : T.V) :
    Sum.inl v ∈ suspRoots k T ↔ v ∈ T.R := by
  rw [suspRoots, Finset.mem_union]
  constructor
  · intro h
    rcases h with h | h
    · rcases Finset.mem_map.mp h with ⟨y, hy, hyx⟩
      have hyv : y = v := Sum.inl.inj hyx
      simpa [hyv] using hy
    · rcases Finset.mem_map.mp h with ⟨j, hj, hjx⟩
      cases hjx
  · intro hv
    exact Or.inl (Finset.mem_map.mpr ⟨v, hv, rfl⟩)

lemma mem_suspRoots_inr (k : ℕ) (T : RootedGraph) (j : Fin (k - 2)) :
    Sum.inr j ∈ suspRoots k T := by
  rw [suspRoots, Finset.mem_union]
  exact Or.inr (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)

lemma suspEdge_inj (k : ℕ) (T : RootedGraph) :
    Set.InjOn (fun e : Finset T.V => e.map (inlEmb T.V (k - 2)) ∪ suspW k T)
      ↑T.G.edges := by
  intro e1 he1 e2 he2 h
  have hsub1 : e1.map (inlEmb T.V (k - 2)) ⊆ e2.map (inlEmb T.V (k - 2)) := by
    intro x hx
    have hxU : x ∈ e1.map (inlEmb T.V (k - 2)) ∪ suspW k T :=
      Finset.mem_union.mpr (Or.inl hx)
    change x ∈ (fun e => e.map (inlEmb T.V (k - 2)) ∪ suspW k T) e1 at hxU
    rw [h] at hxU
    rcases Finset.mem_union.mp hxU with hx2 | hxW
    · exact hx2
    · exact False.elim ((Finset.disjoint_left.mp (disjoint_inl_suspW k T e1)) hx hxW)
  have hsub2 : e2.map (inlEmb T.V (k - 2)) ⊆ e1.map (inlEmb T.V (k - 2)) := by
    intro x hx
    have hxU : x ∈ e2.map (inlEmb T.V (k - 2)) ∪ suspW k T :=
      Finset.mem_union.mpr (Or.inl hx)
    change x ∈ (fun e => e.map (inlEmb T.V (k - 2)) ∪ suspW k T) e2 at hxU
    rw [← h] at hxU
    rcases Finset.mem_union.mp hxU with hx1 | hxW
    · exact hx1
    · exact False.elim ((Finset.disjoint_left.mp (disjoint_inl_suspW k T e2)) hx hxW)
  have hmap : e1.map (inlEmb T.V (k - 2)) = e2.map (inlEmb T.V (k - 2)) :=
    le_antisymm hsub1 hsub2
  exact Finset.map_inj.mp hmap

theorem U_balanced {k : ℕ} (hk : 2 ≤ k) (T : RootedGraph) {a b : ℕ}
    (hbal : Balanced T a b) :
    BalancedK (suspensionRooted k hk T) a b := by
  classical
  intro S hS hSne
  let U := suspensionRooted k hk T
  let emb := inlEmb T.V (k - 2)
  let hf : Set.InjOn emb (emb ⁻¹' (S : Set (T.V ⊕ Fin (k - 2)))) := by
    intro x _ y _ h
    exact Sum.inl.inj h
  let S0 : Finset T.V := S.preimage emb hf
  have hrange : ∀ x ∈ S, x ∈ Set.range emb := by
    intro x hx
    have hxnot : x ∉ U.R := (Finset.mem_sdiff.mp (hS hx)).2
    cases x with
    | inl v => exact ⟨v, rfl⟩
    | inr j =>
        exfalso
        apply hxnot
        change Sum.inr j ∈ suspRoots k T
        exact mem_suspRoots_inr k T j
  have hS0card : S0.card = S.card := by
    change (S.preimage emb hf).card = S.card
    rw [Finset.card_preimage]
    congr 1
    apply Finset.filter_eq_self.mpr
    exact hrange
  have hS0sub : S0 ⊆ Finset.univ \ T.R := by
    intro v hv
    rw [Finset.mem_sdiff]
    constructor
    · exact Finset.mem_univ _
    · intro hvR
      have hvS : emb v ∈ S := by
        change v ∈ S.preimage emb hf at hv
        rwa [Finset.mem_preimage] at hv
      have hnot : emb v ∉ U.R := (Finset.mem_sdiff.mp (hS hvS)).2
      apply hnot
      change Sum.inl v ∈ suspRoots k T
      exact (mem_suspRoots_inl k T v).mpr hvR
  have hS0ne : S0.Nonempty := by
    rcases hSne with ⟨x, hxS⟩
    rcases hrange x hxS with ⟨v, hvx⟩
    subst hvx
    exact ⟨v, by
      change v ∈ S.preimage emb hf
      rw [Finset.mem_preimage]
      exact hxS⟩
  have hle : eT T S0 ≤ eK U S := by
    let f : Finset T.V → Finset U.V :=
      fun e => e.map emb ∪ suspW k T
    have hmaps : Set.MapsTo f
        (T.G.edges.filter (fun e => (e ∩ S0).Nonempty) : Set (Finset T.V))
        (U.G.edges.filter (fun e => (e ∩ S).Nonempty) : Set (Finset U.V)) := by
      intro e he
      rw [Finset.mem_coe, Finset.mem_filter] at he
      rcases he with ⟨heEdges, hmeet⟩
      rw [Finset.mem_coe, Finset.mem_filter]
      constructor
      · change f e ∈ suspEdges k T
        exact Finset.mem_image.mpr ⟨e, heEdges, rfl⟩
      · rcases hmeet with ⟨v, hv⟩
        rw [Finset.mem_inter] at hv
        rcases hv with ⟨hve, hvS0⟩
        have hvS : emb v ∈ S := by
          change v ∈ S.preimage emb hf at hvS0
          rwa [Finset.mem_preimage] at hvS0
        exact ⟨emb v, by
          rw [Finset.mem_inter]
          constructor
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_map.mpr ⟨v, hve, rfl⟩))
          · exact hvS⟩
    have hinj : Set.InjOn f
        (T.G.edges.filter (fun e => (e ∩ S0).Nonempty) : Set (Finset T.V)) := by
      intro e1 he1 e2 he2 h
      have he1' : e1 ∈ T.G.edges :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp he1)).1
      have he2' : e2 ∈ T.G.edges :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp he2)).1
      exact suspEdge_inj k T he1' he2' h
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    simpa [eT, eK, U, f] using hcard
  have hbalS0 : b * S0.card ≤ a * eT T S0 := hbal S0 hS0sub hS0ne
  calc
    b * S.card = b * S0.card := by rw [hS0card]
    _ ≤ a * eT T S0 := hbalS0
    _ ≤ a * eK U S := Nat.mul_le_mul_left a hle

end Erdos571_hypergraph
