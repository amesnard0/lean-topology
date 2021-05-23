import tactic
import data.set.finite
import data.real.basic

import topological_spaces
import neighbourhoods
import topological_spaces2
import metric_spaces

open set

open topological_space
open metric_space

lemma Q_dense : dense {(q : ℝ) | (q : ℚ)} :=
begin
  apply subset.antisymm,
  simp,
  intros x hx,
  have clef : ∀ (n : ℕ), ∃ (q : ℚ), x < q ∧ (q : ℝ) < x + 1/(n+1),
  intro n,
  apply exists_rat_btwn,
  sorry,
  choose u hu using clef,
  apply seq_lim_closure (λ n, (u n : ℝ)), simp,
  sorry,
end

-- Topologie quotient :
instance quot.topological_space {X : Type} [topological_space X] (s : setoid X) : topological_space (quotient s) :=
{ is_open  := λ U, is_open ((quotient.mk') ⁻¹' U),
  univ_mem := univ_mem,
  inter    := begin intros A B hA hB, apply inter, exact hA, exact hB, end,
  union    :=
  begin
    intros B hB,
    rw preimage_sUnion,
    apply union, simp,
    intro b, apply union, simp,
    exact hB b,
  end }

-- Relation d'équivalence définissant ℝ/ℚ :
def real.rel_Q : setoid ℝ :=
{ r := λ x y, ∃ (q : ℚ), x - y = q,
  iseqv :=
  begin
    repeat {split},
    intro x,
    use 0,
    simp,
    rintros x y ⟨q, hq⟩,
    use -q,
    simp, rw ← hq,
    simp,
    rintros x y z ⟨q, hq⟩ ⟨q', hq'⟩,
    use (q + q'),
    calc x - z = (x - y) + (y - z) : by linarith
           ... = ↑(q + q') : by simp [hq, hq'],
  end}

-- La topologie quotient sur ℝ/ℚ est la topologie grossière :
example (U : set (quotient real.rel_Q)) : is_open U ↔ U = ∅ ∨ U = univ :=
begin
  split,
  { intro hyp,
    cases em (U.nonempty) with h1 h2,
    { right,
      cases h1 with X hX,
      cases quotient.surjective_quotient_mk' X with x hx,
      rw ← hx at hX,
      rcases is_open_metric_iff.1 hyp x hX with ⟨r, hr, H⟩,
      apply subset.antisymm, simp,
      intros Y hY,
      cases quotient.surjective_quotient_mk' Y with y hy,
      let V := {z : ℝ | dist (x - y) z < r },
      have hV : V ∈ neighbourhoods (x - y),
      { apply generated_filter.generator, split,
        apply generated_open.generator,
        use [x - y, r],
        calc dist (x - y) (x - y) = 0 : (dist_eq_zero_iff _ _).2 rfl
                              ... < r : hr },
      have clef : closure {(q : ℝ) | (q : ℚ)} = univ, exact Q_dense,
      cases (point_of_closure {(q : ℝ) | (q : ℚ)} (x - y)).1 (by simp [clef]) V hV with z hz,
      rcases hz with ⟨hz, q, hq⟩,
      have hyz : quotient.mk' (y + z) = Y, rw ← hy, rw quotient.eq', use q, simp [hq],
      rw ← hyz,
      apply H,
      have : x - (y + z) = (x - y) - z, by linarith,
      calc dist x (y + z) = abs (x - (y + z))   : rfl
                      ... = abs ((x - y) - z)   : by simp [this]
                      ... = dist (x - y) z      : rfl
                      ... < r                   : hz, },
    { left,
      apply le_antisymm, intros x hx, apply h2, use [x, hx], simp, }, },
  { intro hyp,
    cases hyp with h1 h2,
    rw h1, exact empty_mem,
    rw h2, exact univ_mem, },
end

-- Relation d'équivalence définissant ℝ/ℤ :
def real.rel_Z : setoid ℝ :=
{ r := λ x y, ∃ (n : ℤ), x - y = n,
  iseqv :=
  begin
    repeat {split},
    intro x,
    use 0,
    simp,
    rintros x y ⟨n, hn⟩,
    use -n,
    simp, rw ← hn,
    simp,
    rintros x y z ⟨n, hn⟩ ⟨n', hn'⟩,
    use (n + n'),
    calc x - z = (x - y) + (y - z) : by linarith
           ... = ↑(n + n') : by simp [hn, hn'],
  end }
