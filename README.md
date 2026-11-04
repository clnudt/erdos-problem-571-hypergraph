# The Erdős 571 Hypergraph Problem

## A Lean 4 Formalization of Theorem 1.2

This repository contains a Lean 4 / Mathlib formalization of the main theorem of

> **Rational Turán exponents of a single \(k\)-uniform hypergraph.**

The name `Erdos571_hypergraph` is used throughout to distinguish this project from
the graph version of the Erdős 571 problem.

The formalized theorem is:

> For every integer \(k \ge 2\) and every rational number \(r \in [0,1]\), there exists a
> \(k\)-uniform hypergraph \(F_{k,r}\) such that
> \[
> \operatorname{ex}_k(n,F_{k,r}) = \Theta(n^{k-r}).
> \]

The project is self-contained up to two explicitly stated axioms, both of which are
interfaces to standard results used in the paper. There is no `sorryAx`.

The paper itself is included in this repository as
`docs/Rational Turán exponents of a single k-uniform hypergraph.pdf`.

---

## 1. Main Results

### 1.1 The case \(0 < r \le 1\)

```lean
theorem main {k a b : ℕ} (hk : 2 ≤ k) (ha0 : 0 < a) (hb : 0 < b)
    (ha : a ≤ b) :
  ∃ (B : BipartiteRootedGraph) (Pstar : ℕ),
    RealizesExponent (FkrFinite hk B (Pstar + 1) (by omega))
      ((k : ℝ) - (a : ℝ) / b)
```

This is the case \(r = a/b \in (0,1]\). The forbidden hypergraph is a rooted power
of a suspension,
\[
F_{k,r} = (\mathcal S^k T)^{(p)},
\]
for a balanced rooted bipartite graph \(T\) supplied by Proposition 2.1.

### 1.2 The case \(r = 0\)

```lean
theorem main_zero (k : ℕ) (hk : 2 ≤ k) :
    RealizesExponent (completeK k) (k : ℝ)
```

Here \(F_{k,0} = K_{k+1}^{(k)}\), the complete \(k\)-uniform hypergraph on \(k+1\)
vertices. The lower bound is given by the complete \(k\)-partite \(k\)-graph with
parts of size \(\lfloor n/k\rfloor\); the upper bound is the trivial
\(\binom{n}{k}\) bound.

### 1.3 Combined statement

```lean
theorem main_all (k : ℕ) (hk : 2 ≤ k) :
    (∃ F : FiniteKHypergraph k, RealizesExponent F (k : ℝ)) ∧
    (∀ a b : ℕ, 0 < a → 0 < b → a ≤ b →
      ∃ F : FiniteKHypergraph k,
        RealizesExponent F ((k : ℝ) - (a : ℝ) / b))
```

### 1.4 Literal rational parameter

```lean
theorem main_rat (k : ℕ) (hk : 2 ≤ k) (r : ℚ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∃ F : FiniteKHypergraph k,
      RealizesExponent F ((k : ℝ) - (r : ℝ))
```

This is the literal \(r \in \mathbb Q\) form of Theorem 1.2. Internally it reduces to
`main_zero` and `main`.

---

## 2. Axioms and Trust Boundary

The final audit of the main theorem is:

```text
'Erdos571_hypergraph.main_all' depends on axioms:
  [propext, Classical.choice,
   Erdos571_hypergraph.rootedES_upper,
   Erdos571_hypergraph.uniformDichotomy,
   Quot.sound]
```

Thus, beyond the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`,
there are exactly two mathematical axioms.

### 2.1 `uniformDichotomy`

File: `Erdos571_hypergraph_L12_Constructible.lean`

```lean
axiom uniformDichotomy (N m D : ℕ) :
  ∃ P q0 : ℕ, ∀ (q : ℕ) [Fact q.Prime], q0 ≤ q →
    ∀ Y : Set (Fin N → ZMod q), IsConstructible q N m D Y →
      Nat.card Y ≤ P ∨ (q : ℚ) / 2 ≤ (Nat.card Y : ℚ)
```

This is the uniform dichotomy of Theorem 2.12. It encapsulates:

- Heintz's elimination bound;
- Bézout's inequality;
- the Lang–Weil / Cafure–Matera point count;
- the Frobenius descent tree.

`IsConstructible q N m D Y` is the standard finite-field constructible-set
complexity notion: \(Y\) is defined by at most \(m\) polynomial equations and
non-vanishing conditions of degree at most \(D\) in \(N\) variables.

### 2.2 `rootedES_upper`

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

- Proposition 2.1(i): existence of a balanced rooted graph;
- Proposition 2.1(ii): \(\operatorname{ex}(n,T^{(p)}) = O(n^{2-a/b})\);
- Lemma 2.2: the suspension inequality;
- the elementary identification
  \((\mathcal S^k T)^{(p)} \cong \mathcal S^k(T^{(p)})\).

The last item is elementary and is bundled into the interface for economy.
It can be split off if a minimal-interface version is desired.

### 2.3 What is not an axiom

Proposition 2.14, the root-fibre dichotomy, is **not** an axiom. It is proved in
`Erdos571_hypergraph_L25_RootFibreProof.lean` as

```lean
theorem rootFibreDichotomy_proved ...
```

and then used in `Erdos571_hypergraph_L7_Existence.lean` as the theorem
`rootFibreDichotomy`.

Its audit is:

```text
'Erdos571_hypergraph.rootFibreDichotomy' depends on axioms:
  [propext, Classical.choice,
   Erdos571_hypergraph.uniformDichotomy,
   Quot.sound]
```

---

## 3. Proof Architecture

### 3.1 Lower bound: random algebraic construction

The lower bound follows the paper:

1. Choose a balanced rooted bipartite graph \(T\).
2. Suspend it to a \(k\)-partite \(k\)-graph \(U = \mathcal S^k T\).
3. Take a rooted power \(U^{(p)}\) as the forbidden hypergraph.
4. Choose \(a\) random polynomials of degree at most \(D\) on the host
   \(\mathbb F_q^b \times \cdots \times \mathbb F_q^b\).
5. Count embeddings of \(U\) extending a fixed legal root position.
6. Use the moment estimate and Markov's inequality to show that, for every
   sufficiently large prime \(q\), some coefficient choice has no bad root
   position and at least half the expected number of edges.
7. Conclude that this coefficient choice is \(F\)-free, since a copy of the
   forbidden power would yield \(p > P_*\) embeddings above one root position.
8. Transfer the finite host to \(n\) vertices by adding isolated vertices.
9. Convert the finite lower bound into \(\Omega(n^{k-r})\).

The formalized combinatorial and probabilistic part consists of:

- `Erdos571_hypergraph_L1.lean`: the \(U\)-balance lemma;
- `Erdos571_hypergraph_L2*.lean`: multivariate polynomial interpolation;
- `Erdos571_hypergraph_L3_*.lean`: host, types, moments, expectations, balance;
- `Erdos571_hypergraph_L4_*.lean`: legal roots, Markov, good roots;
- `Erdos571_hypergraph_L5_Free.lean`: absence of bad roots implies \(F\)-freeness;
- `Erdos571_hypergraph_L6_*.lean`: Turán number, isolated-vertex extension, lower bound;
- `Erdos571_hypergraph_L7_Existence.lean`: prime selection and unconditional lower bound;
- `Erdos571_hypergraph_L9_Bridge.lean`: number-theoretic bridge and `maxPowRoot`.

### 3.2 Root-fibre dichotomy

The root-fibre dichotomy is the main new formalization in this repository.

For a fixed legal root position \(w\) and part permutation \(\pi\), the interior
images form a subset of an affine space. The proof:

1. Encodes edge conditions as polynomial equations
   (`Erdos571_hypergraph_L13`, `L14`).
2. Encodes injectivity by partitioning according to the first differing
   coordinate (`Erdos571_hypergraph_L15`, `L18`).
3. Proves that each piece is constructible with a uniform complexity bound
   (`pieceSet_isConstructible`, `pieceSet_isConstructible_rootM`).
4. Applies `uniformDichotomy` to each piece (`L24`).
5. Sums over all choices of first-differing coordinates and over all compatible
   part permutations (`L22`, `L25`).

The key counting identity is:

```lean
theorem card_compatibleEmbedding_eq_sum :
  Fintype.card (CompatibleEmbedding U (hostPartite P) w π) =
    ∑ c : SamePartPair U π → Fin b,
      Fintype.card {z // z ∈ pieceSet P U w π c}
```

and the dichotomy is:

```lean
theorem rootFibreDichotomy_proved ...
```

Files:

- `Erdos571_hypergraph_L12_Constructible.lean`: constructible sets and dichotomy;
- `Erdos571_hypergraph_L13_PolyEncode.lean`: polynomial encoding;
- `Erdos571_hypergraph_L14_Embedding.lean`: variables, edge/root/pair polynomials;
- `Erdos571_hypergraph_L15_Pieces.lean`: `pieceSet` and constructibility;
- `Erdos571_hypergraph_L16_VertexImage.lean`: vertex images and injectivity;
- `Erdos571_hypergraph_L17_EdgeImage.lean`: edge images are host edges;
- `Erdos571_hypergraph_L18_FirstDiff.lean`: first differing coordinate;
- `Erdos571_hypergraph_L19_EmbeddingPoint.lean`: embeddings to points;
- `Erdos571_hypergraph_L20_EmbeddingPointMem.lean`: points lie in the correct piece;
- `Erdos571_hypergraph_L21_Equiv.lean`: bijection and counting identity;
- `Erdos571_hypergraph_L22_PartPerm.lean`: summing only over compatible permutations;
- `Erdos571_hypergraph_L23_RootM.lean`: uniform complexity bound;
- `Erdos571_hypergraph_L24_PerPerm.lean`: per-permutation dichotomy;
- `Erdos571_hypergraph_L25_RootFibreProof.lean`: the root-fibre dichotomy.

### 3.3 Upper bound

The upper bound is:

\[
\operatorname{ex}_k(n,F_{k,r})
\le \binom{n}{k-2}
  \frac{\operatorname{ex}(n-k+2,T^{(p)})}{\binom{k}{2}}
= O(n^{k-a/b}).
\]

It uses Lemma 2.2 (suspension inequality) and Proposition 2.1(ii), both contained
in `rootedES_upper`. The formalization is in
`Erdos571_hypergraph_L8_Upper.lean` and `Erdos571_hypergraph_L10_Main.lean`.

### 3.4 The case \(r=0\)

`Erdos571_hypergraph_L11_Zero.lean` formalizes the complete \(k\)-partite
construction and the trivial upper bound.

---

## 4. Repository Layout

```text
Erdos571_hypergraph/
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
├── Erdos571_hypergraph.lean              # umbrella entry point
├── CheckAxioms.lean                      # axiom audit
├── README.md
├── .gitignore
├── docs/
│   ├── AUDIT.md                          # detailed formalization audit
│   └── Rational Turán exponents of a single k-uniform hypergraph.pdf
│                                          # the paper
└── Erdos571_hypergraph_*.lean            # 68 source files
```

### 4.1 Core definitions and combinatorial layer

| File | Contents |
|---|---|
| `Erdos571_hypergraph_Defs.lean` | hypergraphs, Turán number, `RealizesExponent`, balance |
| `Erdos571_hypergraph_EdgePerm.lean` | edge vertex selection, induced part permutation |
| `Erdos571_hypergraph_Adjacent.lean` | adjacency |
| `Erdos571_hypergraph_L1.lean` | \(U\)-balance lemma |
| `Erdos571_hypergraph_L2*.lean` | multivariate polynomial interpolation |
| `Erdos571_hypergraph_L3_*.lean` | host, types, moments, expectations, balance |
| `Erdos571_hypergraph_L4_*.lean` | legal roots, Markov, good roots |
| `Erdos571_hypergraph_L5_Free.lean` | no bad roots implies \(F\)-free |
| `Erdos571_hypergraph_L6_*.lean` | Turán number, isolated vertices, lower bound |
| `Erdos571_hypergraph_L7_Existence.lean` | prime selection, unconditional lower bound |
| `Erdos571_hypergraph_L8_Asymptotic.lean` | `IsTheta` interface |
| `Erdos571_hypergraph_L8_Upper.lean` | \(F_{k,r}\) has no isolated vertices |
| `Erdos571_hypergraph_L9_Bridge.lean` | `maxPowRoot`, prime-power comparison |
| `Erdos571_hypergraph_L10_Main.lean` | main theorem for \(0<r\le1\) |
| `Erdos571_hypergraph_L11_Zero.lean` | \(r=0\), `main_all`, `main_rat` |

### 4.2 Root-fibre formalization

See the list in Section 3.2.

---

## 5. Building and Verification

### 5.1 Requirements

- Lean 4: `leanprover/lean4:v4.35.0`
- Mathlib: `v4.35.0`
- Lake (installed with Lean)
- VSCode with the Lean 4 extension (recommended)

### 5.2 Build

```bash
lake exe cache get
lake build
```

The first build downloads the Mathlib cache and dependencies. Subsequent
incremental builds are fast.

### 5.3 Axiom audit

```bash
lake env lean CheckAxioms.lean
```

Expected output includes:

```text
'Erdos571_hypergraph.main_all' depends on axioms:
  [propext, Classical.choice,
   Erdos571_hypergraph.rootedES_upper,
   Erdos571_hypergraph.uniformDichotomy,
   Quot.sound]

'Erdos571_hypergraph.main_zero' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

No `sorryAx` occurs.

---

## 6. VSCode

1. Install the **Lean 4** extension.
2. Open the repository folder (the one containing `lakefile.toml` and
   `lean-toolchain`).
3. In a terminal, run:
   ```bash
   lake exe cache get
   lake build
   ```
4. The Lean server starts automatically. Open any `.lean` file to inspect
   diagnostics.
5. If the toolchain does not match, run:
   ```bash
   lake update
   ```

---

## 7. Repository

The paper and the Lean sources are distributed as this repository. `.gitignore`
excludes `.lake/`, `.olean`, `.ilean` and other build artifacts, and
`lake-manifest.json` is included to pin dependency versions.

---

## 8. Definitional Conventions

The formalization follows the paper, with two explicit packaging conventions.

### 8.1 Legal roots

The paper defines a legal root position as an injective map
\(w : R_U \to V(X)\) for which there exists a single permutation
\(\pi \in S_k\) satisfying
\[
\kappa_X(w(r)) = \pi(\kappa_U(r))
\qquad (r \in R_U).
\]

Lean provides:

- `IsLegalRoot U X w`, the literal “there exists \(\pi\)” predicate;
- `LegalRoot U F b`, a bundled version carrying \(\pi\) as a field.

The bridge lemmas

```lean
LegalRoot.toIsLegalRoot
IsLegalRoot.exists_legalRoot
```

show that the bundled structure is a refinement of the paper's predicate and that
every legal root position has a bundled representative. For the suspension
\(U = \mathcal S^k T\) used in Theorem 1.2, the permutation is uniquely determined
by the root position.

### 8.2 The count `Cw`

Lean defines

```lean
Cw U X w =
  ∑ π : Equiv.Perm (Fin k),
    Fintype.card (CompatibleEmbedding U X w π)
```

while the paper defines \(C_w\) as the number of embeddings compatible with some
\(\pi \in \Pi(w)\). If \(U\) has an edge, an embedding determines \(\pi\)
uniquely; this is formalized as

```lean
CompatibleEmbedding.sigma_unique
```

so the sum and the union count agree. The application always has an edge.

### 8.3 The hypothesis `0 < b`

The paper implicitly assumes \(b \ge 1\) because the host parts are
\(\mathbb F_q^b\). Lean makes this explicit as `hb : 0 < b` in the unconditional
lower-bound statements and in `rootFibreDichotomy`.

---

## 9. Relation to the Paper

| Paper | Lean |
|---|---|
| Theorem 1.2 | `main`, `main_zero`, `main_all`, `main_rat` |
| Proposition 2.1 | part of `rootedES_upper` |
| Lemma 2.2 | part of `rootedES_upper` |
| Theorem 2.12 | `uniformDichotomy` |
| Proposition 2.14 | `rootFibreDichotomy_proved`, `rootFibreDichotomy` |
| Lemma 3.1 | `edgePerm`, `copyPhi_part` |
| Corollary 3.2 | `copyW_isLegal`, `Cw_ge_p` |
| Lemma 3.3 | `U_balanced` |
| Lemma 3.4 | `multivariate_interpolation_count_full` and related |
| Lemma 3.5 | `momentAverage_le_legal` |
| F-free argument | `host_free_of_no_bad_roots` |
| \(r=0\) construction | `completeK`, `completePartite`, `main_zero` |

A detailed audit, including a discussion of every interface and packaging
convention, is in [`docs/AUDIT.md`](docs/AUDIT.md).
