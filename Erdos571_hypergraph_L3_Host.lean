import Erdos571_hypergraph_Defs
import Erdos571_hypergraph_L3_Partite
import Erdos571_hypergraph_L2_PolySpace
import Erdos571_hypergraph_L3_TupleType

namespace Erdos571_hypergraph

/-- Vertices of the polynomial host: a part index and `b` coordinates. -/
abbrev HostVertex (F : Type) (k b : ℕ) :=
  Fin k × (Fin b → F)

/-- The fibre of the host part map over `i` is `F^b`. -/
def hostFiberEquiv (F : Type) (k b : ℕ) (i : Fin k) :
    {v : HostVertex F k b // v.1 = i} ≃ (Fin b → F) where
  toFun v := v.1.2
  invFun c := ⟨(i, c), rfl⟩
  left_inv v := by
    rcases v with ⟨⟨j, c⟩, hj⟩
    cases hj
    rfl
  right_inv c := rfl

lemma hostPart_fiber_card {F : Type} [Fintype F] (k b : ℕ) (i : Fin k) :
    Fintype.card {v : HostVertex F k b // v.1 = i} =
      Fintype.card F ^ b := by
  rw [Fintype.card_congr (hostFiberEquiv F k b i), Fintype.card_fun]
  simp

/-- The `k` vertices of a tuple, one in each part. -/
noncomputable def hostEdge {F : Type} [DecidableEq F] {k b : ℕ}
    (z : Fin k → (Fin b → F)) : Finset (HostVertex F k b) :=
  Finset.univ.image (fun i => (i, z i))

lemma hostEdge_card {F : Type} [DecidableEq F] {k b : ℕ}
    (z : Fin k → (Fin b → F)) :
    (hostEdge z).card = k := by
  classical
  rw [hostEdge, Finset.card_image_of_injective]
  · simp
  · intro i j h
    exact (Prod.ext_iff.mp h).1

lemma hostEdge_injective {F : Type} [DecidableEq F] {k b : ℕ}
    {z w : Fin k → (Fin b → F)} (h : hostEdge z = hostEdge w) : z = w := by
  funext j
  have hz : (j, z j) ∈ hostEdge z :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  rw [h] at hz
  rcases Finset.mem_image.mp hz with ⟨j', -, hj'⟩
  have hj1 : j' = j := (Prod.ext_iff.mp hj').1
  subst hj1
  exact (Prod.ext_iff.mp hj').2.symm

/-- Flatten a `k`-tuple of `b`-vectors into a single `(k*b)`-vector. -/
noncomputable def flattenTuple {F : Type} {k b : ℕ}
    (z : Fin k → (Fin b → F)) : Fin (k * b) → F :=
  fun q =>
    let p := finProdFinEquiv.symm q
    z p.1 p.2

lemma flattenTuple_injective {F : Type} {k b : ℕ} :
    Function.Injective (flattenTuple (F := F) (k := k) (b := b)) := by
  intro z w h
  funext i j
  have := congrFun h (finProdFinEquiv (i, j))
  simpa [flattenTuple] using this

/-- Evaluation of a bounded-degree polynomial at a `k`-tuple. -/
noncomputable def evalAtTuple {F : Type} [Field F] {k b D : ℕ}
    (f : PolyCoeff F (k * b) D) (z : Fin k → (Fin b → F)) : F :=
  evalPolyAt (D := D) (flattenTuple z) f

/-- The coefficient data of the random polynomial host. -/
structure HostParams (F : Type) [Field F] (k b a D : ℕ) where
  coeffs : Fin a → PolyCoeff F (k * b) D

noncomputable instance hostParamsFintype {F : Type} [Field F] [Fintype F]
    (k b a D : ℕ) : Fintype (HostParams F k b a D) :=
  Fintype.ofInjective (fun P : HostParams F k b a D => P.coeffs) (by
    intro P Q h
    cases P
    cases Q
    congr)

/-- The edges of the host: tuples where all `a` polynomials vanish. -/
noncomputable def hostEdges {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D) :
    Finset (Finset (HostVertex F k b)) := by
  classical
  exact (Finset.univ.filter (fun z : Fin k → (Fin b → F) =>
    ∀ j : Fin a, evalAtTuple (P.coeffs j) z = 0)).image hostEdge

/-- The polynomial host as a `k`-uniform hypergraph. -/
noncomputable def hostGraph {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D) :
    KHypergraph k (HostVertex F k b) where
  edges := hostEdges P
  edges_card := by
    intro e he
    rcases Finset.mem_image.mp he with ⟨z, -, rfl⟩
    exact hostEdge_card z

/-- The polynomial host as a partite `k`-graph. -/
noncomputable abbrev hostPartite {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (P : HostParams F k b a D) : PartiteKHypergraph k where
  V := HostVertex F k b
  part := fun v => v.1
  G := hostGraph P
  edge_part := by
    intro e he i
    rcases Finset.mem_image.mp he with ⟨z, -, rfl⟩
    refine ⟨(i, z i), ?_, ?_⟩
    · simp [hostEdge]
    · intro v hv
      rcases hv with ⟨hve, hvi⟩
      rcases Finset.mem_image.mp hve with ⟨j, -, hji⟩
      have hj : j = i := by
        have := congrArg Prod.fst hji
        simpa [hvi] using this
      subst hj
      exact hji.symm

/-- The average of `C_w^s` over all polynomial coefficient data. -/
noncomputable def momentAverage {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (U : PartiteRootedKHypergraph k)
    (w : U.R → HostVertex F k b) (s : ℕ) : ℚ :=
  (∑ P : HostParams F k b a D,
      ((Cw U (hostPartite P) w) ^ s : ℚ)) /
    (Fintype.card (HostParams F k b a D) : ℚ)

lemma NτFixed_host_le {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D : ℕ} (U : PartiteRootedKHypergraph k)
    (P : HostParams F k b a D) (w : U.R → HostVertex F k b) (s : ℕ)
    (τ : TypeSpace U s) (h : PartConsistent U s τ) :
    NτFixed U (hostPartite P) w s τ ≤
      Fintype.card F ^ (b * hτ U s τ) := by
  apply NτFixed_le U (hostPartite P) w s τ h b
  intro i
  exact hostPart_fiber_card k b i

end Erdos571_hypergraph
