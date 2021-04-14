import tactic
import data.set.finite

import topological_spaces

open set

open_locale classical

open topological_space

-- Convergence simple :
def pointwise_lim {X Y : Type} [topological_space Y] (f : ℕ → (X → Y)) (F : X → Y) : Prop :=
∀ (x : X), seq_lim (λ n, f n x) (F x)

-- Topologie produit sur X → Y :
instance (X Y : Type) [topological_space Y] : topological_space (X → Y) :=
topological_space.generate_from (X → Y) {U | ∃ (x : X) (Ux : set Y) (hUx : is_open Ux), U = {f : X → Y | f x ∈ Ux}}

lemma is_open_fnct_iff {X Y : Type} [topological_space Y] {s : set (X → Y)} :
is_open s ↔ ∀ f ∈ s, ∃ (D : set X) (φ : X → set Y) (hD : finite D) (hφ : ∀ x ∉ D, φ x = univ), (∀ x, is_open (φ x)) ∧ (∀ x, f x ∈ φ x) ∧ ({f' : X → Y | ∀ x, f' x ∈ φ x} ⊆ s) :=
begin
  split,
  { intros hyp f hf,
    induction hyp,
    { rcases hyp_H with ⟨ x, Ux, hUx, hU ⟩,
      use [{x}, (λ x', ite (x' = x) Ux univ)], split,
      exact finite_singleton x, repeat {split},
      intros x' hx', simp, intro H, exfalso, exact hx' H,
      intro x', split_ifs, exact hUx, exact univ_mem,
      intro x', split_ifs, rw h, rw hU at hf, exact hf, simp,
      intros f' hf', rw hU, specialize hf' x, simp at hf', exact hf', },
    { rcases hyp_ih_ᾰ hf.1 with ⟨ D1, φ1, hD1, hφ1, hoφ1, hfφ1, hA ⟩,
      rcases hyp_ih_ᾰ_1 hf.2 with ⟨ D2, φ2, hD2, hφ2, hoφ2, hfφ2, hB ⟩,
      use [(D1 ∪ D2), (λ x, (φ1 x) ∩ (φ2 x))], split,
      exact finite.union hD1 hD2, repeat {split},
      intros x hx, rw union_def at hx, simp at hx, push_neg at hx, simp [hφ1 x hx.1, hφ2 x hx.2],
      intro x, exact inter (φ1 x) (φ2 x) (hoφ1 x) (hoφ2 x),
      intro x, split, exact hfφ1 x, exact hfφ2 x,
      intros f' hf', split, apply hA, intro x, exact (hf' x).1, apply hB, intro x, exact (hf' x).2, },
    { rcases hf with ⟨hyp_b, hbB, hfb⟩,
      rcases hyp_ih hyp_b hbB hfb with ⟨ D, φ, hD, hφ, hoφ, hfφ, hb ⟩,
      use [D, φ], split,
      exact hD, repeat {split},
      exact hφ, exact hoφ, exact hfφ,
      intros f' hf', use hyp_b, split, exact hbB, exact hb hf', },
    { use [∅, (λ x, univ)], split,
      exact finite_empty, repeat {split},
      simp,
      intro x, exact univ_mem,
      repeat {simp}, }, },
  { intro hyp,
    choose D_ hD_ using hyp,
    choose φ_ hφ_ using hD_,
    have clef : s = ⋃₀ { ({f' : X → Y | ∀ x, f' x ∈ φ_ f H x}) | (f : X → Y) (H : f ∈ s)},
    { apply le_antisymm,
      { intros f hf,
        use {f' : X → Y | ∀ x, f' x ∈ φ_ f hf x}, split,
        use [f, hf],
        specialize hφ_ f hf, repeat {rw exists_prop at hφ_},
        exact hφ_.2.2.2.1, },
      { rintros f ⟨ V, ⟨f', hf', hV⟩, hfV⟩,
        rw ← hV at hfV,
        specialize hφ_ f' hf', repeat {rw exists_prop at hφ_},
        exact hφ_.2.2.2.2 hfV, }, },
    rw clef,
    apply union,
    rintros V ⟨ f, hf, hV ⟩,
    specialize hφ_ f hf, repeat {rw exists_prop at hφ_},
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
        rw hφ_.2.1 x hx2, simp, }, },
    rw clef2,
    apply finite_inter,
    { sorry },
    rintros Vx ⟨ x, hx, hVx ⟩,
    rw ← hVx,
    apply generated_open.generator,
    use [x, φ_ f hf x], split,
    exact hφ_.2.2.1 x,
    refl, },
end