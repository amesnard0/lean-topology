import tactic
import data.set.finite

import topological_spaces

open set
open topological_space

class filter {X : Type} (F : set (set X)) :=
  ( inter  : ∀ {a b}, F a → F b → F (a ∩ b) )
  ( upward : ∀ {a b}, F a → a ⊆ b → F b )
  ( univ   : F univ )

inductive generated_filter {X : Type} (G : set (set X)) : set (set X)
| generator : ∀ g ∈ G, generated_filter g
| inter     : ∀ a b, generated_filter a → generated_filter b → generated_filter (a ∩ b)
| upward    : ∀ a b, generated_filter a → a ⊆ b → generated_filter b
| univ      : generated_filter univ

instance generated_filter_is_filter {X : Type} (G : set (set X)) : filter (generated_filter G) :=
{ inter  := generated_filter.inter,
  upward := generated_filter.upward,
  univ   := generated_filter.univ, }

def neighbourhoods {X : Type} [topological_space X] (x : X) :=
generated_filter {u : set X | is_open u ∧ x ∈ u}

instance neighbourhoods_filter {X : Type} [topological_space X] (x : X) : filter (neighbourhoods x) :=
generated_filter_is_filter {u : set X | is_open u ∧ x ∈ u}

lemma is_neighbourhood_iff {X : Type} [topological_space X] (x : X) {v : set X} :
v ∈ (neighbourhoods x) ↔ ∃ u, is_open u ∧ x ∈ u ∧ u ⊆ v :=
begin
  split,
  { intro hyp,
    induction hyp with g hg a b ha1 hb1 ha2 hb2 a b ha1 hb ha2,
    { use [g, hg.1, hg.2], },  
    { rcases ha2 with ⟨ u1, hu1, hxu1, hu1a⟩,
      rcases hb2 with ⟨ u2, hu2, hxu2, hu2b⟩,
      use [u1 ∩ u2, inter hu1 hu2, hxu1, hxu2],
      intros x hx, exact ⟨hu1a hx.1, hu2b hx.2⟩, },
    { rcases ha2 with ⟨u, hu, hxu, hua⟩,
      use [u, hu, hxu, subset.trans hua hb], },
    { use [univ, univ_mem], simp, }, },
  { rintro ⟨u, hu, hxu, huv⟩,
    apply (neighbourhoods_filter x).upward,
    apply generated_filter.generator,
    exact ⟨hu, hxu⟩,
    exact huv, },
end

lemma is_open_iff {X : Type} [topological_space X] {u : set X} :
is_open u ↔ ∀ x ∈ u, u ∈ neighbourhoods x :=
begin
  split,
  { intro hyp,
    intros x hx,
    apply generated_filter.generator,
    exact ⟨hyp, hx⟩, },
  { intro hyp,
    have : ∀ x ∈ u, ∃ u', is_open u' ∧ x ∈ u' ∧ u' ⊆ u,
    { intros x hx,
      exact (is_neighbourhood_iff x).1 (hyp x hx), },
    choose φ hφ1 hφ2 hφ3 using this,
    have clef : u = ⋃₀ { (φ x hx) | (x : X) (hx : x ∈ u)},
    { apply subset.antisymm,
      { intros x hx,
        use [φ x hx, x, hx, hφ2 x hx], },
      { rintros x ⟨u', ⟨x', hx', hu'⟩, hx⟩,
        rw ← hu' at hx,
        exact (hφ3 x' hx') hx, }, },
    rw clef,
    apply union,
    rintros u' ⟨x, hx, hu'⟩,
    rw ← hu',
    exact hφ1 x hx, },
end