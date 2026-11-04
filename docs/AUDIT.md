# Formalization Audit

## Erdős 571 Hypergraph Problem: Lean 4 Proof of Theorem 1.2

Date: 2026-11-03

---

## 1. Verdict

The Lean 4 formalization proves Theorem 1.2 of the paper, subject to exactly two
explicit mathematical axioms:

```text
'Erdos571_hypergraph.main_all' depends on axioms:
  [propext, Classical.choice,
   Erdos571_hypergraph.rootedES_upper,
   Erdos571_hypergraph.uniformDichotomy,
   Quot.sound]
```

Proposition 2.14, the root-fibre dichotomy, is **not** an axiom. It is proved in
Lean as the theorem `rootFibreDichotomy`. Its audit is:

```text
'Erdos571_hypergraph.rootFibreDichotomy' depends on axioms:
  [propext, Classical.choice,
   Erdos571_hypergraph.uniformDichotomy,
   Quot.sound]
```

The case \(r=0\) is completely axiom-free apart from the standard Lean axioms:

```text
'Erdos571_hypergraph.main_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs in the build.

---

## 2. Item-by-Item Correspondence

| Paper | Type | Lean status |
|---|---|---|
| Theorem 1.2 | main theorem | `main`, `main_zero`, `main_all`, `main_rat` |
| Proposition 2.1(i) | literature | part of `rootedES_upper` |
| Proposition 2.1(ii) | literature | part of `rootedES_upper` |
| Lemma 2.2 | literature | part of `rootedES_upper` |
| Heintz's theorem | literature | inside `uniformDichotomy` |
| Bézout's inequality | literature | inside `uniformDichotomy` |
| Lang–Weil / Cafure–Matera | literature | inside `uniformDichotomy` |
| Corollary 2.6 (descent) | new in paper | inside `uniformDichotomy` |
| Corollary 2.11 (open Lang–Weil) | new in paper | inside `uniformDichotomy` |
| Theorem 2.12 (uniform dichotomy) | new in paper | axiom `uniformDichotomy` |
| Proposition 2.14 (root-fibre) | new in paper | **proved**: `rootFibreDichotomy_proved` |
| Lemma 3.1 (part permutation) | new in paper | `edgePerm`, `copyPhi_part` |
| Corollary 3.2 (power root) | new in paper | `copyW_isLegal`, `Cw_ge_p` |
| Lemma 3.3 (\(U\)-balanced) | new in paper | `U_balanced` |
| Lemma 3.4 (interpolation) | new in paper | `multivariate_interpolation_count_full` |
| Lemma 3.5 (moment) | new in paper | `momentAverage_le_legal` |
| F-free argument | new in paper | `host_free_of_no_bad_roots` |
| Prime selection and lower bound | new in paper | `exists_prime_pow_comparable`, `eventual_lower_bound` |
| Theorem 1.2, \(0<r\le1\) | main theorem | `main` |
| Theorem 1.2, \(r=0\) | main theorem | `main_zero` |
| Combined statement | main theorem | `main_all` |
| Literal \(r:\mathbb Q\) | main theorem | `main_rat` |

---

## 3. The Two Axioms

### 3.1 `uniformDichotomy`

File: `Erdos571_hypergraph_L12_Constructible.lean`

```lean
axiom uniformDichotomy (N m D : ℕ) :
  ∃ P q0 : ℕ, ∀ (q : ℕ) [Fact q.Prime], q0 ≤ q →
    ∀ Y : Set (Fin N → ZMod q), IsConstructible q N m D Y →
      Nat.card Y ≤ P ∨ (q : ℚ) / 2 ≤ (Nat.card Y : ℚ)
```

This is Theorem 2.12. It absorbs Heintz's elimination bound, Bézout's inequality,
the Lang–Weil / Cafure–Matera estimate, and the Frobenius descent tree.

`IsConstructible q N m D Y` means that \(Y\) is defined by at most \(m\)
polynomial equations and non-vanishing conditions of degree at most \(D\) in
\(N\) variables over \(\mathbb F_q\). This matches Definition 2.3 of the paper.

The axiom is stated for prime \(q\) (`ZMod q` is a field in this case), whereas
the paper states the dichotomy for prime powers. The proof uses only prime \(q\),
so the prime case suffices.

### 3.2 `rootedES_upper`

File: `Erdos571_hypergraph_L10_Main.lean`

```lean
axiom rootedES_upper {k a b : ℕ} (hk : 2 ≤ k) (ha0 : 0 < a) (hb : 0 < b)
    (ha : a ≤ b) :
  ∃ B : BipartiteRootedGraph, Balanced B.T a b ∧
    ∀ (p : ℕ) (hp : 0 < p), ∃ C : ℝ,
      ∀ᶠ n : ℕ in Filter.atTop,
        (turanNumber (FkrFinite hk B p hp) n : ℝ) ≤
          C * (n : ℝ) ^ ((k : ℝ) - (a : ℝ) / b)
```

This is the literature upper-bound interface. It bundles:

1. Proposition 2.1(i): existence of a balanced rooted graph;
2. Proposition 2.1(ii): \(\operatorname{ex}(n,T^{(p)})=O(n^{2-a/b})\);
3. Lemma 2.2: the suspension inequality;
4. the elementary identification
   \((\mathcal S^k T)^{(p)} \cong \mathcal S^k(T^{(p)})\).

Item 4 is not a literature result, but an elementary observation of the paper.
It is bundled for interface economy and can be split off if desired.

The density identity \(\rho(T)=b/a\) recorded in Proposition 2.1 is not part of
the axiom. It is used only in Lemma 3.3 to record that \(\rho(U)=b/a\), and the
moment estimate uses the inequality \(b|S|\le a\,e_U(S)\), which the axiom states.

---

## 4. Definitional Conventions

No theorem has been weakened to make the Lean proof pass. The following
definitional choices are explicit.

### 4.1 Legal roots

The paper defines a legal root position as an injective map
\(w : R_U \to V(X)\) for which there exists \(\pi \in S_k\) such that
\[
\kappa_X(w(r)) = \pi(\kappa_U(r))
\qquad (r \in R_U).
\]

Lean has:

- `IsLegalRoot U X w`: the literal “there exists \(\pi\)” predicate;
- `LegalRoot U F b`: a bundled structure carrying \(\pi\) as a field.

The bridge lemmas

```lean
LegalRoot.toIsLegalRoot
IsLegalRoot.exists_legalRoot
```

show that:

- every bundled legal root satisfies the paper's predicate;
- every legal root position in the paper's sense has a bundled representative.

For the suspension \(U = \mathcal S^k T\) used in Theorem 1.2, the permutation is
uniquely determined by the root position, so the two notions have the same
cardinality.

### 4.2 The count `Cw`

Lean defines

```lean
Cw U X w =
  ∑ π : Equiv.Perm (Fin k),
    Fintype.card (CompatibleEmbedding U X w π)
```

The paper defines \(C_w\) as the number of embeddings compatible with some
\(\pi \in \Pi(w)\). If \(U\) has an edge, an embedding determines \(\pi\)
uniquely; this is formalized as

```lean
CompatibleEmbedding.sigma_unique
```

Therefore the sum over all permutations does not overcount, and agrees with the
paper's union count. The application always has an edge.

Moreover:

```lean
theorem Cw_eq_sum_filter :
  Cw U X w =
    ∑ π in Finset.univ.filter (fun π => ∀ r, ...),
      Fintype.card (CompatibleEmbedding U X w π)
```

shows that non-compatible permutations contribute zero.

### 4.3 The hypothesis `0 < b`

The paper implicitly assumes \(b \ge 1\) because the host parts are
\(\mathbb F_q^b\). Lean makes this explicit as `hb : 0 < b` in
`rootFibreDichotomy` and in the unconditional lower-bound statements.
This is a strengthening of the hypotheses, not of the conclusion.

### 4.4 Literal rational parameter

The paper states the theorem for \(r \in \mathbb Q \cap [0,1]\). Lean provides:

- `main` for \(r=a/b\), \(0<a\le b\);
- `main_zero` for \(r=0\);
- `main_all` combining the two;
- `main_rat` with a literal `r : ℚ`, `0 ≤ r`, `r ≤ 1`.

All four have the same mathematical content.

---

## 5. Root-Fibre Proof: Formalization Outline

For a fixed legal root position \(w\) and part permutation \(\pi\), the
embeddings are encoded as points of an affine space over \(\mathbb F_q\).

1. **Polynomial encoding.**
   Each edge condition becomes a polynomial in the ambient variables.
   `Erdos571_hypergraph_L13_PolyEncode.lean` converts bounded-degree coefficient
   vectors to `MvPolynomial`s; `Erdos571_hypergraph_L14_Embedding.lean` selects
   the vertex tuple of an edge.

2. **Injectivity partition.**
   For every pair of vertices in the same host part, the condition \(x\ne y\) is
   split according to the first coordinate at which the two images differ.
   This gives finitely many constructible pieces.
   `Erdos571_hypergraph_L15_Pieces.lean` defines `pieceSet`;
   `Erdos571_hypergraph_L18_FirstDiff.lean` defines the first differing
   coordinate.

3. **Constructibility.**
   Each piece is shown to be constructible with complexity at most
   \[
   b\rho_0 + a|E(U)| + (b+1)|\mathrm{Pair}|.
   \]
   A uniform bound independent of \(\pi\),
   \[
   M = b\rho_0 + a|E(U)| + (b+1)|V(U)|^2,
   \]
   is provided in `Erdos571_hypergraph_L23_RootM.lean`.

4. **Bijection.**
   `Erdos571_hypergraph_L21_Equiv.lean` constructs an equivalence between
   compatible embeddings and the disjoint union of the pieces, and derives
   \[
   \#\mathrm{CompatibleEmbedding}
   =
   \sum_c \#(\mathrm{pieceSet}\,w\,\pi\,c).
   \]

5. **Dichotomy.**
   `uniformDichotomy` is applied to each piece. Summing over choices and over
   compatible permutations gives
   \[
   C_w \le k!\,b^{|V(U)|^2}\,P
   \quad\text{or}\quad
   (q:\mathbb Q)/2 \le C_w.
   \]
   This is `rootFibreDichotomy_proved` in
   `Erdos571_hypergraph_L25_RootFibreProof.lean`.

6. **Use in the main theorem.**
   `Erdos571_hypergraph_L7_Existence.lean` uses the proved dichotomy as the
   theorem `rootFibreDichotomy`; the former axiom has been removed.

---

## 6. Build and Audit Commands

From the repository root:

```bash
lake exe cache get
lake build
lake env lean CheckAxioms.lean
```

The last command prints the axiom dependencies of:

```lean
Erdos571_hypergraph.rootFibreDichotomy_proved
Erdos571_hypergraph.rootFibreDichotomy
Erdos571_hypergraph.main
Erdos571_hypergraph.main_zero
Erdos571_hypergraph.main_all
Erdos571_hypergraph.main_rat
```

---

## 7. Remaining Interfaces

The only remaining mathematical interfaces are:

1. `uniformDichotomy` — the general constructible-set dichotomy of Theorem 2.12;
2. `rootedES_upper` — Proposition 2.1 together with Lemma 2.2.

If a fully axiom-free development is desired, the next step is to formalize
Theorem 2.12 from Heintz, Bézout, and Lang–Weil. This is a substantial independent
project in effective algebraic geometry.

A smaller optional step is to split `rootedES_upper` into:

- a literature axiom for Proposition 2.1 and Lemma 2.2;
- a formal proof of the suspension–power identification.

This does not affect the main theorem's proof structure.

---

## 8. File Map

### 8.1 Main theorem

- `Erdos571_hypergraph_L10_Main.lean` — `main`
- `Erdos571_hypergraph_L11_Zero.lean` — `main_zero`, `main_all`, `main_rat`
- `Erdos571_hypergraph_L8_Upper.lean` — `Fkr_vertex_covered`
- `Erdos571_hypergraph_L9_Bridge.lean` — numerical bridge
- `Erdos571_hypergraph_L7_Existence.lean` — lower-bound existence

### 8.2 Combinatorial and probabilistic part

- `Erdos571_hypergraph_L1.lean` — \(U\)-balance
- `Erdos571_hypergraph_L2*.lean` — interpolation
- `Erdos571_hypergraph_L3_*.lean` — host, types, moments
- `Erdos571_hypergraph_L4_*.lean` — legal roots, Markov
- `Erdos571_hypergraph_L5_Free.lean` — F-free argument
- `Erdos571_hypergraph_L6_*.lean` — Turán number and lower bound

### 8.3 Root-fibre part

- `Erdos571_hypergraph_L12_Constructible.lean`
- `Erdos571_hypergraph_L13_PolyEncode.lean`
- `Erdos571_hypergraph_L14_Embedding.lean`
- `Erdos571_hypergraph_L15_Pieces.lean`
- `Erdos571_hypergraph_L16_VertexImage.lean`
- `Erdos571_hypergraph_L17_EdgeImage.lean`
- `Erdos571_hypergraph_L18_FirstDiff.lean`
- `Erdos571_hypergraph_L19_EmbeddingPoint.lean`
- `Erdos571_hypergraph_L20_EmbeddingPointMem.lean`
- `Erdos571_hypergraph_L21_Equiv.lean`
- `Erdos571_hypergraph_L22_PartPerm.lean`
- `Erdos571_hypergraph_L23_RootM.lean`
- `Erdos571_hypergraph_L24_PerPerm.lean`
- `Erdos571_hypergraph_L25_RootFibreProof.lean`
