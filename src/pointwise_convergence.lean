import tactic
import data.set.finite

import topological_spaces
import neighbourhoods
import topological_spaces2

open set

open_locale classical

open topological_space

-- Convergence simple :
def pointwise_lim {X Y : Type} [topological_space Y] (f : ℕ → (X → Y)) (F : X → Y) : Prop :=
∀ (x : X), seq_lim (λ n, f n x) (F x)

-- Topologie produit sur X → Y :
instance fnct.topological_space (X Y : Type) [topological_space Y] : topological_space (X → Y) :=
topological_space.generate_from (X → Y) {U | ∃ (x : X) (Ux : set Y) (hUx : is_open Ux), U = {f : X → Y | f x ∈ Ux}}

-- Base de la topologie produit (intersections finies de générateurs) :
lemma is_open_fnct_iff {X Y : Type} [topological_space Y] {s : set (X → Y)} :
is_open s ↔ ∀ f ∈ s, ∃ (D : set X) (φ : X → set Y) (hD : finite D) (hφ : ∀ x ∉ D, φ x = univ), (∀ x, is_open (φ x)) ∧ (∀ x, f x ∈ φ x) ∧ ({f' : X → Y | ∀ x, f' x ∈ φ x} ⊆ s) :=
begin
  split,
  { intros hyp f hf,
    induction hyp with U hU A B hA1 hB1 hA2 hB2 C hC1 hC2,
    { rcases hU with ⟨ x, Ux, hUx, hU ⟩,
      use [{x}, (λ x', ite (x' = x) Ux univ)], split,
      exact finite_singleton x, repeat {split},
      intros x' hx', simp, intro H, exfalso, exact hx' H,
      intro x', split_ifs, exact hUx, exact univ_mem,
      intro x', split_ifs, rw h, rw hU at hf, exact hf, simp,
      intros f' hf', rw hU, specialize hf' x, simp at hf', exact hf', },
    { rcases hA2 hf.1 with ⟨ D1, φ1, hD1, hφ1, hoφ1, hfφ1, hA ⟩,
      rcases hB2 hf.2 with ⟨ D2, φ2, hD2, hφ2, hoφ2, hfφ2, hB ⟩,
      use [(D1 ∪ D2), (λ x, (φ1 x) ∩ (φ2 x))], split,
      exact finite.union hD1 hD2, repeat {split},
      intros x hx, rw union_def at hx, simp at hx, push_neg at hx, simp [hφ1 x hx.1, hφ2 x hx.2],
      intro x, exact inter (hoφ1 x) (hoφ2 x),
      intro x, split, exact hfφ1 x, exact hfφ2 x,
      intros f' hf', split, apply hA, intro x, exact (hf' x).1, apply hB, intro x, exact (hf' x).2, },
    { rcases hf with ⟨c, hcC, hfc⟩,
      rcases hC2 c hcC hfc with ⟨ D, φ, hD, hφ, hoφ, hfφ, hc ⟩,
      use [D, φ], split,
      exact hD, repeat {split},
      exact hφ, exact hoφ, exact hfφ,
      intros f' hf', use [c, hcC, hc hf'], },
    { use [∅, (λ x, univ)], split,
      exact finite_empty, repeat {split},
      simp,
      intro x, exact univ_mem,
      repeat {simp}, }, },
  { intro hyp,
    choose D_ φ_ H1 H2 H3 H4 H5 using hyp,
    have clef : s = ⋃₀ { ({f' : X → Y | ∀ x, f' x ∈ φ_ f H x}) | (f : X → Y) (H : f ∈ s)},
    { apply le_antisymm,
      { intros f hf,
        use {f' : X → Y | ∀ x, f' x ∈ φ_ f hf x},
        use [f, hf, H4 f hf], },
      { rintros f ⟨ V, ⟨f', hf', hV⟩, hfV⟩,
        rw ← hV at hfV,
        exact H5 f' hf' hfV, }, },
    rw clef,
    apply union,
    rintros V ⟨ f, hf, hV ⟩,
    have clef2 : V = ⋂₀ { ({f' : X → Y | f' x ∈ φ_ f hf x }) | x ∈ D_ f hf },
    { apply le_antisymm,
      { intros f' hf',
        rintros Vx ⟨ x, hx, hVx ⟩,
        rw ← hVx,
        rw ← hV at hf',
        exact hf' x, },
      { intros f' hf',
        rw ← hV,
        intro x,
        cases em (x ∈ D_ f hf) with hx1 hx2,
        apply hf' {f' : X → Y | f' x ∈ φ_ f hf x },
        use [x, hx1],
        rw H2 f hf x hx2, simp, }, },
    rw clef2,
    apply finite_inter,
    { let ψ := λ x, {f' : X → Y | f' x ∈ φ_ f hf x},
      have : {_x : set (X → Y) | ∃ (x : X) (H : x ∈ D_ f hf), {f' : X → Y | f' x ∈ φ_ f hf x} = _x} = ψ '' (D_ f hf),
      { apply le_antisymm,
        { rintros V ⟨x, hx, hV⟩, rw ← hV, clear hV V,
          use x, split, exact hx, refl, },
        { rintros V ⟨x, hx, hV⟩, rw ← hV, clear hV V,
          use x, split, exact hx, refl, }, },
      rw this,
      exact finite.image ψ (H1 f hf), },
    rintros Vx ⟨ x, hx, hVx ⟩,
    rw ← hVx,
    apply generated_open.generator,
    use [x, φ_ f hf x], split,
    exact H3 f hf x,
    refl, },
end

-- Cette topologie est la topologie de la convergence simple :
example {X Y : Type} [topological_space Y] (f : ℕ → (X → Y)) (F : X → Y) :
pointwise_lim f F ↔ seq_lim f F :=
begin
  split,
  { intro hyp,
    intros V hV,
    rcases (is_neighbourhood_iff F).1 hV with ⟨U, hU, hFU, hUV⟩,
    rw is_open_fnct_iff at hU,
    rcases hU F hFU with ⟨D, φ, hD, hφ, h1, h2, h3⟩,
    cases em (D.nonempty) with hD1 hD2,
    { have clef : ∀ x, ∃ (N : ℕ), ∀ n ≥ N, f n x ∈ φ x,
      { intros x,
        have hφx : (φ x) ∈ neighbourhoods (F x),
        { rw is_neighbourhood_iff,
          use [φ x, h1 x, h2 x], },
        exact hyp x (φ x) hφx, },
      choose ψ hψ using clef,
      cases finite.exists_maximal_wrt ψ D hD hD1 with x₀ hx₀, rw exists_prop at hx₀,
      let N := ψ x₀,
      have hN : ∀ x ∈ D, N ≥ ψ x,
      { intros x hx,
        cases le_total N (ψ x) with H1 H2,
        exact ge_of_eq (hx₀.2 x hx H1),
        exact H2, },
      use N,
      intros n hn,
      apply hUV, apply h3,
      intro x,
      cases em (x ∈ D) with hx1 hx2,
      exact hψ x n (ge_trans hn (hN x hx1)),
      rw hφ x hx2, simp, },
    { rw nonempty_def at hD2, push_neg at hD2,
      use 0,
      intros n hn,
      apply hUV, apply h3,
      intro x, rw hφ x (hD2 x), simp, }, },
  { intro hyp,
    intros x Vx hVx,
    rcases (is_neighbourhood_iff (F x)).1 hVx with ⟨Ux, hUx, hxUx, hUxVx⟩,
    let V := {g : X → Y | g x ∈ Vx},
    have hV: V ∈ neighbourhoods F,
    { rw is_neighbourhood_iff,
      use {g : X → Y | g x ∈ Ux}, repeat {split},
      apply generated_open.generator,
      use [x, Ux, hUx],
      exact hxUx,
      intros g hg,
      exact hUxVx hg, },
    cases hyp V hV with N hN,
    use N,
    intros n hn,
    exact hN n hn, },
end