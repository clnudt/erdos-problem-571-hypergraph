import Erdos571_hypergraph_L2
import Erdos571_hypergraph_L2_Separating

namespace Erdos571_hypergraph

/-- A separating linear functional turns multivariate evaluation at the
points `z i` into univariate evaluation at the distinct values `ℓ (z i)`. -/
theorem multivariate_eval_surjective
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F) :
    ∃ ℓ : (Fin n → F) →ₗ[F] F,
      Function.Surjective
        (fun h : Polynomial.degreeLT F m =>
          fun i : Fin m => h.1.eval (ℓ (z i))) := by
  rcases exists_separating_linear z hz hq with ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_⟩
  exact univariate_eval_surjective m (fun i => ℓ (z i)) hℓ

/-- The probability form for the univariate Lagrange subspace selected by a
separating functional: the number of degree-`< m` polynomials vanishing at
all `z i` is `|degreeLT F m| / q^m`. -/
theorem multivariate_interpolation_count
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {n m : ℕ} (z : Fin m → (Fin n → F))
    (hz : Function.Injective z)
    (hq : (m.choose 2 : ℕ) < Fintype.card F) :
    ∃ ℓ : (Fin n → F) →ₗ[F] F,
      (Finset.univ.filter (fun h : Polynomial.degreeLT F m =>
          (fun i : Fin m => h.1.eval (ℓ (z i))) = 0)).card *
        Fintype.card F ^ m =
        Fintype.card (Polynomial.degreeLT F m) := by
  rcases exists_separating_linear z hz hq with ⟨ℓ, hℓ⟩
  refine ⟨ℓ, ?_⟩
  exact univariate_interpolation_count m (fun i => ℓ (z i)) hℓ

end Erdos571_hypergraph
