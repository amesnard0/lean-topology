import topological_spaces
import topological_spaces2
import t2_spaces

import data.real.basic

noncomputable theory
open set

-- Definition d'un espace métrique :
class metric_space (X : Type) :=
  (dist : X → X → ℝ)
  (dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y)
  (dist_symm : ∀ x y, dist x y = dist y x)
  (triangle : ∀ x y z, dist x z ≤ dist x y + dist y z)

namespace metric_space
open topological_space

-- Preuve que la distance est positive à partir des autres axiomes :
lemma dist_nonneg {X : Type} [metric_space X] (x y : X) : 0 ≤ dist x y :=
begin
  have :=
  calc 0 = dist x x : by rw (dist_eq_zero_iff x x).2 rfl
     ... ≤ dist x y + dist y x : triangle x y x
     ... = dist x y + dist x y : by rw dist_symm x y
     ... = 2 * dist x y : by linarith,
  linarith,
end

-- Topologie induite par la distance :
instance {X : Type} [metric_space X] : topological_space X :=
generate_from X { B | ∃ (x : X) r, B = {y | dist x y < r} }

-- Caractérisation des ouverts pour la distance :
lemma is_open_metric_iff {X : Type} [metric_space X] {U : set X}:
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

end metric_space

open topological_space
open metric_space

-- Espace métrique ℝ :
instance metric_space_R : metric_space ℝ :=
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


-- Produit de deux espaces métriques :
instance prod.metric_space (X Y : Type) [metric_space X] [metric_space Y] :
metric_space (X × Y) :=
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
instance metric_t2 {X : Type} [metric_space X] : t2_space X :=
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

-- Convergence d'une suite dans un espace métrique :
lemma seq_lim_metric {X : Type} [metric_space X] (u : ℕ → X) (l : X) :
seq_lim u l ↔ ∀ ε > 0, ∃ (N : ℕ), ∀ n ≥ N, dist (u n) l < ε :=
begin
  split,
  { intro hyp,
    intros ε εpos,
    let V := { x | dist l x < ε },
    have hV : neighbourhood l V,
    { use V, repeat {split},
      apply generated_open.generator,
      use [l, ε],
      calc dist l l = 0 : (dist_eq_zero_iff l l).2 rfl
                ... < ε : by linarith [εpos],
      exact le_refl V, },
    cases hyp V hV with N hN,
    use N,
    intros n hn,
    calc dist (u n) l = dist l (u n) : dist_symm (u n) l
                  ... < ε            : hN n hn, },
  { intro hyp,
    rintros V ⟨U, hU, hlU, hUV⟩,
    rcases is_open_metric_iff.1 hU l hlU with ⟨ε, εpos, H⟩,
    cases hyp ε εpos with N hN,
    use N,
    intros n hn,
    apply hUV,
    apply H,
    calc dist l (u n) = dist (u n) l : dist_symm l (u n)
                  ... < ε            : hN n hn, },
end