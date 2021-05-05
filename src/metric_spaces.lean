import topological_spaces
import t2_spaces

import data.real.basic

noncomputable theory
open set

-- Definition d'un espace métrique :
class metric_space_basic (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

namespace metric_space_basic
open topological_space

-- Preuve que la distance est positive à partir des autres axiomes :
lemma dist_nonneg {X : Type} [metric_space_basic X] (x y : X) : 0 ≤ dist x y :=
begin
  have :=
  calc 0 = dist x x : by rw (dist_eq_zero_iff x x).2 rfl
     ... ≤ dist x y + dist y x : triangle x y x
     ... = dist x y + dist x y : by rw dist_symm x y
     ... = 2 * dist x y : by linarith,
  linarith,
end

-- Topologie induite par la distance :
instance {X : Type} [metric_space_basic X] : topological_space X :=
generate_from X { B | ∃ (x : X) r, B = {y | dist x y < r} }

-- Caractérisation des ouverts pour la distance :
lemma is_open_metric_iff {X : Type} [metric_space_basic X] {U : set X}:
is_open U ↔ ∀ x ∈ U, ∃ r > 0, {y | dist x y < r} ⊆ U :=
begin
  split,
  { intro hyp,
    intros x hx,
    induction hyp,
    { rcases hyp_H with ⟨xA, r, hA⟩,
      rw hA at hx, simp at hx,
      use [r - dist xA x, by linarith [hx]],
      intros y hy, simp at hy,
      rw hA,
      calc dist xA y ≤ dist xA x + dist x y      : triangle xA x y
                 ... < dist xA x + r - dist xA x : by linarith [hy]
                 ... = r                         : by linarith, },
    { rcases hyp_ih_ᾰ hx.1 with ⟨r1, hr1, hA⟩,
      rcases hyp_ih_ᾰ_1 hx.2 with ⟨r2, hr2, hB⟩,
      use min r1 r2, split,
      exact lt_min hr1 hr2,
      intros y hy, split,
      apply hA,
      calc dist x y < min r1 r2 : hy
                ... ≤ r1        : min_le_left r1 r2,
      apply hB,
      calc dist x y < min r1 r2 : hy
                ... ≤ r2        : min_le_right r1 r2, },
    { rcases hx with ⟨b, hbB, hxb⟩,
      rcases hyp_ih b hbB hxb with ⟨r, hr, hb⟩,
      use [r, hr],
      intros y hy,
      use b, split,
      exact hbB, exact hb hy, },
    { use [1, by linarith], simp, }, },
  { intro hyp,
    choose φ hφ using hyp,
    have clef : U = ⋃₀ { ({y : X | dist x y < φ x H}) | (x : X) (H : x ∈ U) },
    { apply le_antisymm,
      { intros x hx,
        use {y : X | dist x y < φ x hx}, split,
        use [x, hx],
        specialize hφ x hx, rw exists_prop at hφ,
        calc dist x x = 0      : (dist_eq_zero_iff x x).2 rfl
                  ... < φ x hx : by linarith [hφ.1], },
      { apply sUnion_subset,
        rintros B ⟨x, hx, hB⟩,
        rw ← hB,
        specialize hφ x hx, rw exists_prop at hφ,
        exact hφ.2, }, },
    rw clef,
    apply union,
    rintros B ⟨x, hx, hB⟩,
    rw ← hB,
    apply generated_open.generator,
    use [x, φ x hx], },
end

end metric_space_basic

open topological_space
open metric_space_basic

-- Produit de deux espaces métriques :
instance prod.metric_space_basic (X Y : Type) [metric_space_basic X] [metric_space_basic Y] :
metric_space_basic (X × Y) :=
{ dist := λ u v, max (dist u.fst v.fst) (dist u.snd v.snd),
  dist_eq_zero_iff :=
  begin
    intros u v,
    split,
    { intro hyp,
      have := dist_nonneg u.fst v.fst,
      have := dist_nonneg u.snd v.snd,
      have := max_le_iff.1 (le_of_eq hyp),
      ext; rw ← dist_eq_zero_iff; linarith, },
    { intro hyp,
      rw [hyp, (dist_eq_zero_iff _ _).mpr, (dist_eq_zero_iff _ _).mpr, max_self]; refl },
  end,
  dist_symm :=
  begin
    intros u v,
    rw [dist_symm u.fst v.fst, dist_symm u.snd v.snd],
  end,
  triangle :=
  begin
    intros u v w,
    have := triangle u.fst v.fst w.fst,
    have := triangle u.snd v.snd w.snd,
    unfold max, split_ifs;
    linarith,
  end
  }

-- Tout espace métrique est séparé :
instance metric_t2 {X : Type} [metric_space_basic X] : t2_space X :=
{ t2 :=
begin
  intros x y hxy,
  let r := dist x y,
  have r_strict_pos : r > 0,
  { cases le_or_gt r 0 with h1 h2,
    exfalso, exact hxy ((dist_eq_zero_iff x y).1 (le_antisymm h1 (dist_nonneg x y))),
    exact h2, },
  let Ux := {z : X | dist x z < r/2},
  let Uy := {z : X | dist y z < r/2},
  use [Ux, Uy],
  repeat {split},
  apply generated_open.generator, use [x, r/2],
  apply generated_open.generator, use [y, r/2],
  calc dist x x = 0   : (dist_eq_zero_iff x x).2 rfl
            ... < r/2 : by linarith,
  calc dist y y = 0   : (dist_eq_zero_iff y y).2 rfl
            ... < r/2 : by linarith,
  apply le_antisymm,
  { rintros z ⟨ hzUx, hzUy ⟩,
    have hxz : dist x z < r/2, exact hzUx,
    have hyz : dist y z < r/2, exact hzUy,
    have :=
    calc dist x y ≤ dist x z + dist z y : triangle x z y
              ... = dist x z + dist y z : by linarith [dist_symm y z]
              ... < r/2 + r/2           : by linarith [hxz, hyz]
              ... = r                   : by linarith,
    linarith, },
  { intros x hx, exfalso, exact hx, },
end }

-- Espace métrique ℝ :
instance : metric_space_basic ℝ :=
{ dist := λ x y,  abs (x - y),
  dist_eq_zero_iff :=
  begin
    intros x y,
    split,
    intro hyp,
    linarith [abs_eq_zero.1 hyp],
    intro hyp,
    simp [hyp],
  end,
  dist_symm := abs_sub,
  triangle :=
  begin
    intros x y z,
    have clef : x - z = (x - y) + (y - z), linarith,
    calc abs (x - z) = abs ((x - y) + (y - z))   : by simp [clef]
                 ... ≤ abs (x - y) + abs (y - z) : abs_add _ _,
  end }

/- On redéfinit maintenant un espace métrique comme la donnée d'un espace topologique et d'un espace métrique
tels que la topologie soit égale à la topologie induite par la distance : -/
class metric_space (X : Type) extends topological_space X, metric_space_basic X :=
  (compatible : ∀ U, is_open U ↔ generated_open X { B | ∃ (x : X) r, B = {y | dist x y < r}} U)

namespace metric_space
open topological_space

def of_basic {X : Type} (m : metric_space_basic X) : metric_space X :=
{ compatible := begin intros, refl, end,
  ..m,
  ..@metric_space_basic.topological_space X m }

/- Sur un produit de deux espaces métriques,
la topologie produit est égale à la topologie induite par la distance produit : -/
instance {X Y : Type} [metric_space X] [metric_space Y] : metric_space (X × Y) :=
{ compatible :=
  begin
    intro U,
    split,
    { intro hyp,
      sorry, },
    { intro hyp,
      induction hyp,
      { rcases hyp_H with ⟨ x, r, hA ⟩,
        rw is_open_prod_iff,
        intros a b hab, rw hA at hab,
        have := calc dist x.fst a ≤ dist x (a, b) : le_max_left _ _
                              ... < r             : hab,
        have := calc dist x.snd b ≤ dist x (a, b) : le_max_right _ _
                              ... < r             : hab,
        use [{y : X | dist a y < r - dist x.fst a}, {y : Y | dist b y < r - dist x.snd b}],
        repeat {split},
        apply generated_open.generator, use [a, r - dist x.fst a],
        apply generated_open.generator, use [b, r - dist x.snd b],
        calc dist a a = 0                 : (dist_eq_zero_iff a a).2 rfl
                  ... < r - dist x.fst a : by linarith,
        calc dist b b = 0                : (dist_eq_zero_iff b b).2 rfl
                  ... < r - dist x.snd b : by linarith,
        intros y hy,
        rw hA,
        have : dist a y.fst < r - dist x.fst a, exact hy.1,
        have left :=
        calc dist x.fst y.fst ≤ dist x.fst a + dist a y.fst : triangle x.fst a y.fst
                       ... < dist x.fst a + (r - dist x.fst a) : by linarith
                       ... = r : by linarith,
        have : dist b y.snd < r - dist x.snd b, exact hy.2,
        have right :=
        calc dist x.snd y.snd ≤ dist x.snd b + dist b y.snd : triangle x.snd b y.snd
                       ... < dist x.snd b + (r - dist x.snd b) : by linarith
                       ... = r : by linarith,
        exact max_lt left right, },
      { exact generated_open.inter hyp_A hyp_B hyp_ih_ᾰ hyp_ih_ᾰ_1, },
      { exact generated_open.union hyp_B hyp_ih, },
      { exact generated_open.univ, }, },
  end,
  ..prod.topological_space X Y,
  ..prod.metric_space_basic X Y, }

local attribute [-instance] metric_space_basic.topological_space

end metric_space