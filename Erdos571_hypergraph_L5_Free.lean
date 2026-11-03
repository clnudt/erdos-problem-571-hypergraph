import Erdos571_hypergraph_L4_Good
import Erdos571_hypergraph_CopyEmbedding

namespace Erdos571_hypergraph

/-- The suspension of a balanced rooted graph is balanced. -/
lemma balanced_suspensionPartite {k : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) {a b : ℕ} (hbal : Balanced B.T a b) :
    BalancedK (suspensionPartite k hk B).toRootedKHypergraph a b := by
  simpa [suspensionPartite] using U_balanced hk B.T hbal

/-- The number of edge-types is at most `s` times the number of edges of `U`. -/
lemma eτ_le_edges {k : ℕ} (U : PartiteRootedKHypergraph k) (s : ℕ)
    (τ : TypeSpace U s) :
    eτ U s τ ≤ s * U.G.edges.card := by
  classical
  unfold eτ
  calc
    (Finset.univ.image (fun p : Fin s × {e : Finset U.V // e ∈ U.G.edges} =>
      typeEdgeSet U s τ p.1 p.2.1)).card
        ≤ Fintype.card (Fin s × {e : Finset U.V // e ∈ U.G.edges}) :=
      Finset.card_image_le
    _ = s * U.G.edges.card := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]

/-- The numerical hypothesis on `D` used in the moment estimate. -/
lemma hD_of_edges_le {k : ℕ} (U : PartiteRootedKHypergraph k) (s D : ℕ)
    (hD : s * U.G.edges.card ≤ D) :
    ∀ τ : TypeSpace U s, eτ U s τ ≤ D + 1 := by
  intro τ
  have h := eτ_le_edges U s τ
  omega

/-- If no legal root position is bad, the polynomial host contains no copy of
the `p`-th power of the suspension. -/
theorem host_free_of_no_bad_roots {F : Type} [Field F] [Fintype F]
    [DecidableEq F] {k b a D p : ℕ} (hk : 2 ≤ k)
    (B : BipartiteRootedGraph) (hp : 0 < p)
    (P : HostParams F k b a D) (Pstar : ℕ)
    (hP : p = Pstar + 1)
    (hzero : badRootCount (suspensionPartite k hk B) P Pstar = 0) :
    ¬ IsCopy
      (partitePower (suspensionPartite k hk B) p hp).G
      (hostPartite P).G := by
  classical
  rintro ⟨f, hcopy⟩
  let U := suspensionPartite k hk B
  have hlegal : IsLegalRoot U (hostPartite P) (copyW hk B p hp f) :=
    copyW_isLegal hk B p hp f hcopy
  let w : LegalRoot U F b :=
    { toFun := copyW hk B p hp f
      inj := hlegal.1
      sigma := hlegal.2.choose
      part_eq := hlegal.2.choose_spec }
  have hge : p ≤ Cw U (hostPartite P) w.toFun :=
    Cw_ge_p hk B p hp f hcopy
  have hle : Cw U (hostPartite P) w.toFun ≤ Pstar := by
    by_contra h
    have hlt : Pstar < Cw U (hostPartite P) w.toFun := Nat.lt_of_not_le h
    have hpos : 0 < badRootCount U P Pstar := by
      unfold badRootCount
      apply Finset.card_pos.mpr
      exact ⟨w, by simp [hlt]⟩
    have hzero' : badRootCount U P Pstar = 0 := by simpa [U] using hzero
    omega
  omega

/-- There is a coefficient choice whose host has many edges and contains no
copy of the forbidden power. -/
theorem exists_free_host {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k b a D p s : ℕ} (hk : 2 ≤ k) (B : BipartiteRootedGraph)
    (hp : 0 < p) (Pstar : ℕ) (hP : p = Pstar + 1)
    (hbal : Balanced B.T a b) (ha : a ≤ b * k)
    (hs : 0 < s)
    (hq : ∀ τ : TypeSpace (suspensionPartite k hk B) s,
      (eτ (suspensionPartite k hk B) s τ).choose 2 < Fintype.card F)
    (hD : ∀ τ : TypeSpace (suspensionPartite k hk B) s,
      eτ (suspensionPartite k hk B) s τ ≤ D + 1)
    (hPstar : (Pstar : ℚ) < (Fintype.card F : ℚ) / 2)
    (hdich : ∀ (P : HostParams F k b a D)
        (w : LegalRoot (suspensionPartite k hk B) F b),
      Cw (suspensionPartite k hk B) (hostPartite P) w.toFun ≤ Pstar ∨
        (Fintype.card F : ℚ) / 2 ≤
          (Cw (suspensionPartite k hk B) (hostPartite P) w.toFun : ℚ))
    (P₀ : HostParams F k b a D)
    (hgap : (Fintype.card F : ℚ) ^ (b * k) *
        ((Fintype.card (LegalRoot (suspensionPartite k hk B) F b) : ℚ) *
          ((Fintype.card (TypeSpace (suspensionPartite k hk B) s) : ℚ) /
            ((Fintype.card F : ℚ) / 2) ^ s)) <
      (Fintype.card F : ℚ) ^ (b * k - a) / 2) :
    ∃ P : HostParams F k b a D,
      badRootCount (suspensionPartite k hk B) P Pstar = 0 ∧
        (Fintype.card F : ℚ) ^ (b * k - a) / 2 ≤
          ((hostEdges P).card : ℚ) ∧
        ¬ IsCopy
          (partitePower (suspensionPartite k hk B) p hp).G
          (hostPartite P).G := by
  classical
  have hbalU := balanced_suspensionPartite hk B hbal
  obtain ⟨P, hzero, hedges⟩ :=
    exists_good_coeff (suspensionPartite k hk B) a D Pstar ha hbalU hs hq hD
      hPstar hdich P₀ hgap
  exact ⟨P, hzero, hedges,
    host_free_of_no_bad_roots hk B hp P Pstar hP hzero⟩

end Erdos571_hypergraph
