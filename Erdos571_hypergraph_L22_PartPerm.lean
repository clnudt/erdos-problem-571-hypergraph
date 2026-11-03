import Erdos571_hypergraph_L21_Equiv

open scoped BigOperators

namespace Erdos571_hypergraph

/-- Part permutations compatible with a root position. -/
abbrev PartPerm {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b) :=
  {π : Equiv.Perm (Fin k) // ∀ r : U.R, (w r).1 = π (U.part r.1)}

noncomputable instance partPermFintype {F : Type} [Field F] {k b : ℕ}
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b) :
    Fintype (PartPerm U w) :=
  Fintype.ofInjective (fun p : PartPerm U w => p.1) (by
    intro a b h
    exact Subtype.ext h)

lemma compatibleEmbedding_isEmpty_of_not_part {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b)
    (π : Equiv.Perm (Fin k))
    (h : ¬ ∀ r : U.R, (w r).1 = π (U.part r.1)) :
    IsEmpty (CompatibleEmbedding U (hostPartite P) w π) := by
  classical
  rw [not_forall] at h
  obtain ⟨r, hr⟩ := h
  refine ⟨fun φ => ?_⟩
  have h1 : (φ.toFun r.1).1 = (w r).1 := by
    have := φ.root_compat r.1 r.2
    exact congrArg Prod.fst this
  have h2 : (φ.toFun r.1).1 = π (U.part r.1) := by
    have := φ.part_compat r.1
    simpa [hostPartite] using this
  exact hr (h1.symm.trans h2)

theorem Cw_eq_sum_filter {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D : ℕ} (P : HostParams F k b a D)
    (U : PartiteRootedKHypergraph k) (w : U.R → HostVertex F k b) :
    Cw U (hostPartite P) w =
      (Finset.univ.filter (fun π : Equiv.Perm (Fin k) =>
        ∀ r : U.R, (w r).1 = π (U.part r.1))).sum
        (fun π => Fintype.card
          (CompatibleEmbedding U (hostPartite P) w π)) := by
  classical
  rw [Cw]
  rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun π : Equiv.Perm (Fin k) => ∀ r : U.R, (w r).1 = π (U.part r.1))]
  have hzero : (Finset.univ.filter
      (fun π : Equiv.Perm (Fin k) => ¬ ∀ r : U.R,
        (w r).1 = π (U.part r.1))).sum
      (fun π => Fintype.card (CompatibleEmbedding U (hostPartite P) w π)) = 0 := by
    apply Finset.sum_eq_zero
    intro π hπ
    rw [Finset.mem_filter] at hπ
    haveI := compatibleEmbedding_isEmpty_of_not_part P U w π hπ.2
    simp
  rw [hzero, add_zero]

end Erdos571_hypergraph
