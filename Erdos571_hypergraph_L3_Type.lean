import Erdos571_hypergraph_L3_Balance

namespace Erdos571_hypergraph

/-- The interior vertices of a rooted hypergraph. -/
abbrev Interior {k : ℕ} (U : PartiteRootedKHypergraph k) :=
  {x : U.toRootedKHypergraph.V // x ∉ U.toRootedKHypergraph.R}

/-- A partition of a finite type, represented by its blocks. -/
structure Partition (α : Type) [DecidableEq α] where
  blocks : Finset (Finset α)
  nonempty : ∀ b ∈ blocks, b.Nonempty
  pairwise : ∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c
  cover : ∀ a : α, ∃! b, b ∈ blocks ∧ a ∈ b

noncomputable instance partitionFintype {α : Type} [Fintype α] [DecidableEq α] :
    Fintype (Partition α) :=
  Fintype.ofInjective (fun p : Partition α => p.blocks) (by
    intro p q h
    cases p
    cases q
    simp only at h
    subst h
    rfl)

lemma Partition.ext {α : Type} [DecidableEq α] {p q : Partition α}
    (h : p.blocks = q.blocks) : p = q := by
  cases p
  cases q
  simp only at h
  subst h
  rfl

/-- The type space of Lemma 3.3: a partition of the `s h` interior
vertices, together with `s` part permutations. -/
abbrev TypeSpace {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ) :=
  Partition (Interior U × Fin s) × (Fin s → Equiv.Perm (Fin k))

noncomputable instance typeSpaceFintype {k : ℕ}
    (U : PartiteRootedKHypergraph k) (s : ℕ) :
    Fintype (TypeSpace U s) := by
  classical
  infer_instance

/-- A tuple of `s` compatible embeddings. -/
abbrev Tuple {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ) :=
  Fin s → Σ π : Equiv.Perm (Fin k), CompatibleEmbedding U X w π

/-- The image in `X` of an interior vertex in a given copy. -/
noncomputable def tupleImage {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (p : Interior U × Fin s) : X.V :=
  (φ p.2).2.toFun p.1.1

/-- The block of `p`: all pairs with the same image as `p`. -/
noncomputable def block {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (p : Interior U × Fin s) :
    Finset (Interior U × Fin s) := by
  classical
  exact Finset.univ.filter (fun q => tupleImage U X w s φ q = tupleImage U X w s φ p)

lemma mem_block_iff {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) (p q : Interior U × Fin s) :
    q ∈ block U X w s φ p ↔
      tupleImage U X w s φ q = tupleImage U X w s φ p := by
  classical
  simp [block]

lemma block_eq_of_mem {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) {p q : Interior U × Fin s}
    (h : q ∈ block U X w s φ p) :
    block U X w s φ q = block U X w s φ p := by
  classical
  ext r
  rw [mem_block_iff, mem_block_iff]
  constructor
  · intro hr
    exact hr.trans ((mem_block_iff U X w s φ p q).mp h)
  · intro hr
    exact hr.trans ((mem_block_iff U X w s φ p q).mp h).symm

/-- The partition of the `s h` interior vertices induced by a tuple. -/
noncomputable def partitionOf {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (φ : Tuple U X w s) : Partition (Interior U × Fin s) where
  blocks := Finset.univ.image (fun p => block U X w s φ p)
  nonempty := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨p, -, rfl⟩
    exact ⟨p, by simp [mem_block_iff]⟩
  pairwise := by
    intro b hb c hc hbc
    rcases Finset.mem_image.mp hb with ⟨p, -, rfl⟩
    rcases Finset.mem_image.mp hc with ⟨q, -, rfl⟩
    rw [Finset.disjoint_left]
    intro x hx hx'
    apply hbc
    have hp : block U X w s φ x = block U X w s φ p :=
      block_eq_of_mem U X w s φ hx
    have hq : block U X w s φ x = block U X w s φ q :=
      block_eq_of_mem U X w s φ hx'
    exact hp.symm.trans hq
  cover := by
    intro p
    refine ⟨block U X w s φ p, ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩
    · exact (mem_block_iff U X w s φ p p).mpr rfl
    · intro b hb
      rcases hb with ⟨hb, hpb⟩
      rcases Finset.mem_image.mp hb with ⟨q, -, rfl⟩
      exact (block_eq_of_mem U X w s φ hpb).symm

lemma card_tuple {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ) :
    Fintype.card (Tuple U X w s) = Cw U X w ^ s := by
  rw [Fintype.card_fun]
  congr 1
  · rw [Fintype.card_sigma]
    rfl
  · simp

/-- The number of tuples of a given type `τ`. -/
noncomputable def Nτ {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ)
    (τ : TypeSpace U s) : ℕ := by
  classical
  exact (Finset.univ.filter (fun φ : Tuple U X w s =>
    partitionOf U X w s φ = τ.1 ∧
      (fun i : Fin s => (φ i).1) = τ.2)).card

/-- Type decomposition: `C_w^s` is the sum of `N_τ(w)` over all types. -/
theorem type_decomposition {k : ℕ} (U : PartiteRootedKHypergraph k)
    (X : PartiteKHypergraph k) (w : U.R → X.V) (s : ℕ) :
    Cw U X w ^ s = ∑ τ : TypeSpace U s, Nτ U X w s τ := by
  classical
  rw [← card_tuple U X w s]
  let f : Tuple U X w s → TypeSpace U s := fun φ =>
    (partitionOf U X w s φ, fun i : Fin s => (φ i).1)
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Tuple U X w s)))
    (t := (Finset.univ : Finset (TypeSpace U s)))
    (f := f) (by intro x _; exact Finset.mem_univ _)
  rw [← Finset.card_univ]
  rw [h]
  apply Finset.sum_congr rfl
  intro τ _
  simp [f, Nτ, Prod.ext_iff]

end Erdos571_hypergraph
