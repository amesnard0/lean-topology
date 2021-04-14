import tactic
import data.set.finite
import data.real.basic

import topological_spaces
import t2_spaces

noncomputable theory
open set

open_locale big_operators

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
  calc dist x x = 0 : (dist_eq_zero_iff x x).2 rfl
            ... < r/2 : by linarith,
  calc dist y y = 0 : (dist_eq_zero_iff y y).2 rfl
            ... < r/2 : by linarith,
  apply le_antisymm,
  { rintros z ⟨ hzUx, hzUy ⟩,
    have hxz : dist x z < r/2, exact hzUx,
    have hyz : dist y z < r/2, exact hzUy,
    have :=
    calc dist x y ≤ dist x z + dist z y : triangle x z y
            ... = dist x z + dist y z : by linarith [dist_symm y z]
            ... < r/2 + r/2 : by linarith [hxz, hyz]
            ... = r : by linarith,
    linarith, },
  { intros x hx, exfalso, exact hx, },
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