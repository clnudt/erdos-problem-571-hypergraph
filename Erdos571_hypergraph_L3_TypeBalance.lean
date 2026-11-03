import Erdos571_hypergraph_L3_TypeGraph
import Erdos571_hypergraph_L3_TypeEmbeddingOf

namespace Erdos571_hypergraph

/-- The first copy in which a block of `τ` appears. -/
noncomputable def blockFirstCopy {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) : Fin s :=
  (Finset.univ.filter (fun i : Fin s =>
    ∃ p : Interior U × Fin s, p ∈ b.1 ∧ p.2 = i)).min' (by
      obtain ⟨p, hp⟩ := τ.1.nonempty b.1 b.2
      exact ⟨p.2, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨p, hp, rfl⟩⟩⟩)

lemma blockFirstCopy_mem {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    blockFirstCopy U τ b ∈ Finset.univ.filter (fun i : Fin s =>
      ∃ p : Interior U × Fin s, p ∈ b.1 ∧ p.2 = i) :=
  Finset.min'_mem _ _

lemma blockFirstCopy_le {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks})
    {p : Interior U × Fin s} (hp : p ∈ b.1) :
    blockFirstCopy U τ b ≤ p.2 :=
  Finset.min'_le _ _
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hp, rfl⟩⟩)

/-- Interior vertices whose block first appears in copy `i`. -/
noncomputable def Si {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) : Finset U.V := by
  classical
  exact Finset.univ.filter (fun x : U.V =>
    ∃ hx : x ∉ U.R,
      blockFirstCopy U τ
        ⟨blockOf U s τ ⟨x, hx⟩ i, blockOf_mem U s τ ⟨x, hx⟩ i⟩ = i)

/-- The type edges of copy `i` that meet `S_i`. -/
noncomputable def Ei {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) : Finset (Finset (TypeVertex U τ)) := by
  classical
  exact (U.G.edges.filter (fun e => (e ∩ Si U τ i).Nonempty)).image
    (typeEdgeSet U s τ i)

lemma Si_subset {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) :
    Si U τ i ⊆ Finset.univ \ U.R := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨-, hxR, -⟩
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxR⟩

lemma Ei_subset {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) (hτa : TypeAdmissible U s τ) :
    Ei U τ i ⊆ (typeGraph U s τ hτa).edges := by
  classical
  intro E hE
  rcases Finset.mem_image.mp hE with ⟨e, he, rfl⟩
  exact Finset.mem_image.mpr
    ⟨⟨i, ⟨e, (Finset.mem_filter.mp he).1⟩⟩, Finset.mem_univ _, rfl⟩

lemma Ei_card {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s)
    (hinj : Function.Injective (typeEmbed U s τ i)) :
    (Ei U τ i).card = eK U.toRootedKHypergraph (Si U τ i) := by
  classical
  unfold Ei eK
  rw [Finset.card_image_of_injOn]
  intro e _ e' _ h
  exact Finset.image_injective hinj h

lemma balanced_Si {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (a b : ℕ)
    (hbal : BalancedK U.toRootedKHypergraph a b) (i : Fin s) :
    b * (Si U τ i).card ≤
      a * eK U.toRootedKHypergraph (Si U τ i) := by
  classical
  by_cases hS : (Si U τ i).Nonempty
  · exact hbal (Si U τ i) (Si_subset U τ i) hS
  · have h0 : (Si U τ i).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    simp [h0]

lemma a_mul_Ei_ge {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (a b : ℕ)
    (hbal : BalancedK U.toRootedKHypergraph a b) (i : Fin s)
    (hinj : Function.Injective (typeEmbed U s τ i)) :
    b * (Si U τ i).card ≤ a * (Ei U τ i).card := by
  have h := balanced_Si U τ a b hbal i
  rw [Ei_card U τ i hinj]
  exact h

/-- The disjoint union `Σ i, S_i`. -/
noncomputable def siSigma {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) : Finset (Σ _i : Fin s, U.V) :=
  Finset.univ.sigma (fun i => Si U τ i)

/-- The block associated with a pair `(i,x)` in the disjoint union. -/
noncomputable def siToBlock {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (p : Σ _i : Fin s, U.V)
    (hp : p ∈ siSigma U τ) :
    {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} :=
  let hx := Classical.choose (Finset.mem_filter.mp
    (Finset.mem_sigma.mp hp).2).2
  ⟨blockOf U s τ ⟨p.2, hx⟩ p.1,
    blockOf_mem U s τ ⟨p.2, hx⟩ p.1⟩

lemma si_firstCopy {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (p : Σ _i : Fin s, U.V)
    (hp : p ∈ siSigma U τ) :
    blockFirstCopy U τ (siToBlock U τ p hp) = p.1 := by
  unfold siToBlock
  exact Classical.choose_spec
    (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2

lemma siToBlock_injective {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (hsep : ∀ i : Fin s, Function.Injective
      (fun x : Interior U => blockOf U s τ x i))
    {p q : Σ _i : Fin s, U.V}
    (hp : p ∈ siSigma U τ) (hq : q ∈ siSigma U τ)
    (h : siToBlock U τ p hp = siToBlock U τ q hq) : p = q := by
  classical
  rcases p with ⟨i, x⟩
  rcases q with ⟨j, y⟩
  have hp_first : blockFirstCopy U τ (siToBlock U τ ⟨i, x⟩ hp) = i :=
    si_firstCopy U τ ⟨i, x⟩ hp
  have hq_first : blockFirstCopy U τ (siToBlock U τ ⟨j, y⟩ hq) = j :=
    si_firstCopy U τ ⟨j, y⟩ hq
  have hij : i = j := by
    rw [← hp_first, ← hq_first, h]
  subst hij
  have hblock : blockOf U s τ
      ⟨x, Classical.choose (Finset.mem_filter.mp
        (Finset.mem_sigma.mp hp).2).2⟩ i =
      blockOf U s τ
      ⟨y, Classical.choose (Finset.mem_filter.mp
        (Finset.mem_sigma.mp hq).2).2⟩ i :=
    congrArg Subtype.val h
  have hinter : (⟨x, Classical.choose (Finset.mem_filter.mp
        (Finset.mem_sigma.mp hp).2).2⟩ : Interior U) =
      ⟨y, Classical.choose (Finset.mem_filter.mp
        (Finset.mem_sigma.mp hq).2).2⟩ :=
    hsep i hblock
  have hxy : x = y := congrArg Subtype.val hinter
  subst hxy
  rfl

lemma siToBlock_surjective {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) :
    ∃ p : Σ _i : Fin s, U.V, ∃ hp : p ∈ siSigma U τ,
      siToBlock U τ p hp = b := by
  classical
  let i := blockFirstCopy U τ b
  have hi : i ∈ Finset.univ.filter (fun i : Fin s =>
      ∃ p : Interior U × Fin s, p ∈ b.1 ∧ p.2 = i) :=
    blockFirstCopy_mem U τ b
  rcases Finset.mem_filter.mp hi with ⟨-, p, hp, hpi⟩
  let x : U.V := p.1.1
  have hx : x ∉ U.R := p.1.2
  have hb : blockOf U s τ ⟨x, hx⟩ i = b.1 := by
    have h := blockOf_eq_of_mem U s τ b hp
    rwa [hpi] at h
  have hxSi : x ∈ Si U τ i := by
    simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hx, ?_⟩
    have hb' : (⟨blockOf U s τ ⟨x, hx⟩ i,
        blockOf_mem U s τ ⟨x, hx⟩ i⟩ :
          {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks}) = b :=
      Subtype.ext hb
    rw [hb']
  let p' : Σ _i : Fin s, U.V := ⟨i, x⟩
  have hp' : p' ∈ siSigma U τ := by
    simp only [siSigma, Finset.mem_sigma, Finset.mem_univ, true_and]
    exact hxSi
  refine ⟨p', hp', ?_⟩
  apply Subtype.ext
  change blockOf U s τ
    ⟨x, Classical.choose (Finset.mem_filter.mp
      (Finset.mem_sigma.mp hp').2).2⟩ i = b.1
  simpa using hb

lemma sum_Si_card {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s)
    (hsep : ∀ i : Fin s, Function.Injective
      (fun x : Interior U => blockOf U s τ x i)) :
    (∑ i : Fin s, (Si U τ i).card) = hτ U s τ := by
  classical
  have hsigma : (siSigma U τ).card =
      ∑ i : Fin s, (Si U τ i).card := by
    rw [siSigma, Finset.card_sigma]
  have hbij : (siSigma U τ).card = τ.1.blocks.card := by
    rw [← Finset.card_attach (s := τ.1.blocks)]
    apply Finset.card_bij (s := siSigma U τ) (t := τ.1.blocks.attach)
      (fun p hp => siToBlock U τ p hp)
    · intro p hp
      simpa using (siToBlock U τ p hp).2
    · intro p hp q hq h
      exact siToBlock_injective U τ hsep hp hq h
    · intro b _
      obtain ⟨p, hp, hpb⟩ := siToBlock_surjective U τ b
      exact ⟨p, hp, hpb⟩
  rw [← hsigma, hbij]
  rfl

lemma typeEmbed_interior {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) (x : Interior U) :
    typeEmbed U s τ i x.1 =
      Sum.inr ⟨blockOf U s τ x i, blockOf_mem U s τ x i⟩ := by
  simp [typeEmbed, x.2]

lemma typeEmbed_root {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (i : Fin s) (r : U.R) :
    typeEmbed U s τ i r.1 = Sum.inl r := by
  simp [typeEmbed, r.2]

lemma le_of_Ei_Ej {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) {i j : Fin s}
    {e e' : Finset U.V} (hE : typeEdgeSet U s τ j e' = typeEdgeSet U s τ i e)
    {x : U.V} (hx_e : x ∈ e) (hx_Si : x ∈ Si U τ i) :
    i ≤ j := by
  classical
  simp only [Si, Finset.mem_filter, Finset.mem_univ, true_and] at hx_Si
  rcases hx_Si with ⟨hxR, hfirst⟩
  let b : {b : Finset (Interior U × Fin s) // b ∈ τ.1.blocks} :=
    ⟨blockOf U s τ ⟨x, hxR⟩ i, blockOf_mem U s τ ⟨x, hxR⟩ i⟩
  have hfirst_b : blockFirstCopy U τ b = i := hfirst
  have hx_vertex : typeEmbed U s τ i x ∈ typeEdgeSet U s τ i e :=
    Finset.mem_image.mpr ⟨x, hx_e, rfl⟩
  have hx_vertex' : typeEmbed U s τ i x ∈ typeEdgeSet U s τ j e' := by
    rw [hE]
    exact hx_vertex
  rcases Finset.mem_image.mp hx_vertex' with ⟨y, hy_e', hy_eq⟩
  have hx_te : typeEmbed U s τ i x =
      Sum.inr ⟨blockOf U s τ ⟨x, hxR⟩ i,
        blockOf_mem U s τ ⟨x, hxR⟩ i⟩ :=
    typeEmbed_interior U τ i ⟨x, hxR⟩
  have hy_te : typeEmbed U s τ j y =
      Sum.inr ⟨blockOf U s τ ⟨x, hxR⟩ i,
        blockOf_mem U s τ ⟨x, hxR⟩ i⟩ := by
    rw [hy_eq, hx_te]
  have hyR : y ∉ U.R := by
    intro hyR
    have : typeEmbed U s τ j y = Sum.inl ⟨y, hyR⟩ :=
      typeEmbed_root U τ j ⟨y, hyR⟩
    rw [this] at hy_te
    simp at hy_te
  have hy_te' : typeEmbed U s τ j y =
      Sum.inr ⟨blockOf U s τ ⟨y, hyR⟩ j,
        blockOf_mem U s τ ⟨y, hyR⟩ j⟩ :=
    typeEmbed_interior U τ j ⟨y, hyR⟩
  have hblock : blockOf U s τ ⟨y, hyR⟩ j =
      blockOf U s τ ⟨x, hxR⟩ i := by
    rw [hy_te'] at hy_te
    injection hy_te with h
    exact congrArg Subtype.val h
  have hy_mem_b : (⟨y, hyR⟩, j) ∈ b.1 := by
    have : (⟨y, hyR⟩, j) ∈ blockOf U s τ ⟨y, hyR⟩ j :=
      mem_blockOf U s τ ⟨y, hyR⟩ j
    rw [hblock] at this
    exact this
  have hle : blockFirstCopy U τ b ≤ j :=
    blockFirstCopy_le U τ b hy_mem_b
  rwa [hfirst_b] at hle

lemma Ei_disjoint {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) {i j : Fin s} (hij : i ≠ j) :
    Disjoint (Ei U τ i) (Ei U τ j) := by
  classical
  rw [Finset.disjoint_left]
  intro E hEi hEj
  rcases Finset.mem_image.mp hEi with ⟨e, he, rfl⟩
  rcases Finset.mem_image.mp hEj with ⟨e', he', hE'⟩
  have hxne : (e ∩ Si U τ i).Nonempty := (Finset.mem_filter.mp he).2
  rcases hxne with ⟨x, hx⟩
  rcases Finset.mem_inter.mp hx with ⟨hx_e, hx_Si⟩
  have hyne : (e' ∩ Si U τ j).Nonempty := (Finset.mem_filter.mp he').2
  rcases hyne with ⟨y, hy⟩
  rcases Finset.mem_inter.mp hy with ⟨hy_e', hy_Sj⟩
  have hij_le : i ≤ j :=
    le_of_Ei_Ej U τ hE' hx_e hx_Si
  have hji_le : j ≤ i :=
    le_of_Ei_Ej U τ hE'.symm hy_e' hy_Sj
  exact hij (le_antisymm hij_le hji_le)

lemma sum_Ei_card_le_eτ {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (hτa : TypeAdmissible U s τ) :
    (∑ i : Fin s, (Ei U τ i).card) ≤ eτ U s τ := by
  classical
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      ∀ j ∈ (Finset.univ : Finset (Fin s)), i ≠ j →
        Disjoint (Ei U τ i) (Ei U τ j) := by
    intro i _ j _ hij
    exact Ei_disjoint U τ hij
  have hcard : (Finset.univ.biUnion (fun i => Ei U τ i)).card =
      ∑ i : Fin s, (Ei U τ i).card :=
    Finset.card_biUnion hdisj
  rw [← hcard]
  apply Finset.card_le_card
  intro E hE
  rcases Finset.mem_biUnion.mp hE with ⟨i, -, hi⟩
  exact Ei_subset U τ i hτa hi

theorem type_balance {k s : ℕ} (U : PartiteRootedKHypergraph k)
    (τ : TypeSpace U s) (a b : ℕ)
    (hbal : BalancedK U.toRootedKHypergraph a b)
    (hτa : TypeAdmissible U s τ)
    (hsep : ∀ i : Fin s, Function.Injective
      (fun x : Interior U => blockOf U s τ x i))
    (hinj : ∀ i : Fin s, Function.Injective (typeEmbed U s τ i)) :
    b * hτ U s τ ≤ a * eτ U s τ := by
  classical
  have hsumS := sum_Si_card U τ hsep
  have hsumE := sum_Ei_card_le_eτ U τ hτa
  calc
    b * hτ U s τ = b * (∑ i : Fin s, (Si U τ i).card) := by
      rw [hsumS]
    _ = ∑ i : Fin s, b * (Si U τ i).card := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin s, a * (Ei U τ i).card := by
      apply Finset.sum_le_sum
      intro i _
      exact a_mul_Ei_ge U τ a b hbal i (hinj i)
    _ = a * (∑ i : Fin s, (Ei U τ i).card) := by
      rw [Finset.mul_sum]
    _ ≤ a * eτ U s τ := Nat.mul_le_mul_left _ hsumE

end Erdos571_hypergraph
