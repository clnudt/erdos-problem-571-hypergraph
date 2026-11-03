import Mathlib

namespace Erdos571_hypergraph

open Polynomial

/-- The counting core of Lemma 3.2.

Let `F` be a finite field, `P` a finite additive group of coefficients
(e.g. the coefficient space of polynomials of total degree at most `D`),
and `eval : P →+ (Fin m → F)` a surjective evaluation map.  Then the
number of coefficient vectors whose evaluation is zero is `|P| / |F|^m`,
equivalently the probability that a uniformly random element of `P`
vanishes at all `m` points is `|F|^(-m)`. -/
theorem interpolation_count
    {F P : Type} [Field F] [Fintype F] [DecidableEq F]
    [AddCommGroup P] [Fintype P]
    (m : ℕ) (eval : P →+ (Fin m → F))
    (hsurj : Function.Surjective eval) :
    (Finset.univ.filter (fun p => eval p = 0)).card * Fintype.card F ^ m
      = Fintype.card P := by
  classical
  let K := eval.ker
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
  have hquot : Nat.card (P ⧸ K) = Nat.card (Fin m → F) := by
    exact Nat.card_congr
      (QuotientAddGroup.quotientKerEquivOfSurjective eval hsurj).toEquiv
  have hker : Nat.card K = (Finset.univ.filter (fun p => eval p = 0)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp [K, AddMonoidHom.mem_ker]
  have hF : Nat.card (Fin m → F) = Fintype.card F ^ m := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun]
    simp
  rw [hquot, hker, hF, Nat.card_eq_fintype_card] at hcard
  rw [Nat.mul_comm] at hcard
  exact hcard.symm

/-- The coefficient space of univariate polynomials of degree `< m` is finite. -/
noncomputable instance degreeLTFintype (F : Type) [Field F] [Fintype F] (m : ℕ) :
    Fintype (Polynomial.degreeLT F m) :=
  Fintype.ofEquiv (Fin m → F) (Polynomial.degreeLTEquiv F m).symm.toEquiv

/-- Evaluation at the points `v i`, as an additive homomorphism. -/
def evalHom {F : Type} [Field F] (m : ℕ) (v : Fin m → F) :
    Polynomial.degreeLT F m →+ (Fin m → F) where
  toFun f i := f.1.eval (v i)
  map_zero' := by
    funext i
    simp
  map_add' f g := by
    funext i
    simp [Polynomial.eval_add]

/-- Univariate Lagrange interpolation: for distinct points `v : Fin m → F`,
the evaluation map from polynomials of degree `< m` to `Fin m → F` is
surjective. -/
theorem univariate_eval_surjective
    {F : Type} [Field F] (m : ℕ) (v : Fin m → F) (hv : Function.Injective v) :
    Function.Surjective (evalHom m v) := by
  classical
  intro y
  let p : Polynomial F := Lagrange.interpolate (Finset.univ : Finset (Fin m)) v y
  have hvs : Set.InjOn v (↑(Finset.univ : Finset (Fin m))) := by
    intro i _ j _ h
    exact hv h
  have hpdeg : p.degree < (m : WithBot ℕ) := by
    have h := Lagrange.degree_interpolate_lt (s := Finset.univ) (v := v) hvs
      (r := y)
    simpa [p] using h
  refine ⟨⟨p, Polynomial.mem_degreeLT.mpr hpdeg⟩, ?_⟩
  funext i
  exact Lagrange.eval_interpolate_at_node (s := Finset.univ) (v := v) hvs
    (r := y) (Finset.mem_univ i)

/-- The probability form of univariate interpolation: the number of
polynomials of degree `< m` vanishing at `m` distinct points is
`|degreeLT F m| / |F|^m`. -/
theorem univariate_interpolation_count
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (m : ℕ) (v : Fin m → F) (hv : Function.Injective v) :
    (Finset.univ.filter (fun f : Polynomial.degreeLT F m =>
        evalHom m v f = 0)).card * Fintype.card F ^ m
      = Fintype.card (Polynomial.degreeLT F m) := by
  exact interpolation_count m (evalHom m v) (univariate_eval_surjective m v hv)

end Erdos571_hypergraph
