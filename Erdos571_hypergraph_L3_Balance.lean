import Erdos571_hypergraph_L3_Union

namespace Erdos571_hypergraph

/-- The set of copy indices whose copy of `x` is equivalent to the `i`-th
copy of `x`. -/
noncomputable def classCopies {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (x : U.V) (hx : x ∉ U.R) (i : Fin s) : Finset (Fin s) := by
  classical
  exact Finset.univ.filter (fun j =>
    UnionRel U X w s φ
      (UnionVertex.interior x hx i)
      (UnionVertex.interior x hx j))

/-- The first copy in which the class of `(x,i)` appears. -/
noncomputable def firstCopy {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (x : U.V) (hx : x ∉ U.R) (i : Fin s) : Fin s :=
  (classCopies U X w s φ x hx i).min' (by
    refine ⟨i, ?_⟩
    simp only [classCopies, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.EqvGen.refl _)

lemma firstCopy_proof_irrel {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (x : U.V) (hx hx' : x ∉ U.R) (i : Fin s) :
    firstCopy U X w s φ x hx i = firstCopy U X w s φ x hx' i := by
  have h : hx = hx' := Subsingleton.elim _ _
  subst h
  rfl

/-- The interior vertices whose first occurrence is in copy `i`. -/
noncomputable def S {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π)
    (i : Fin s) : Finset U.V := by
  classical
  exact Finset.univ.filter (fun x =>
    ∃ hx : x ∉ U.R, firstCopy U X w s φ x hx i = i)

end Erdos571_hypergraph
