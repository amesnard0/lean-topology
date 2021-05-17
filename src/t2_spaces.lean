import topological_spaces
import topological_spaces2

open set
open topological_space

-- Definition d'un espace séparé :
class t2_space (X : Type) [topological_space X] :=
(t2 : ∀ (x y : X) (h : x ≠ y), ∃ (Ux Uy : set X) (hUx : is_open Ux) (hUy : is_open Uy) (hx : x ∈ Ux) (hy : y ∈ Uy), Ux ∩ Uy = ∅)

-- Tout espace discret est séparé :
instance discrete_t2 {X : Type} [topological_space X] [discrete_space X] : t2_space X :=
{ t2 :=
begin
  intros x y hxy,
  use [{x}, {y}],
  repeat {split},
  exact discrete_space.all_open {x},
  exact discrete_space.all_open {y},
  apply le_antisymm,
  { intros z hz,
    apply hxy,
    have : z = x, exact hz.1,
    have : z = y, exact hz.2,
    cc, },
  { intros x hx, exfalso, exact hx, },
end }

-- Unicité de la limite dans un espace séparé :
lemma lim_unique {X : Type} [topological_space X] [t2_space X] (u : ℕ → X) (x y : X)
(h1 : seq_lim u x) (h2 : seq_lim u y) : x = y :=
begin
  by_contradiction,
  rcases (t2_space.t2 x y h) with ⟨ Ux, Uy, hUx, hUy, hx, hy, hUxUy ⟩,
  cases (h1 Ux ⟨ Ux, hUx, hx, le_refl Ux⟩) with N1 hN1,
  cases (h2 Uy ⟨ Uy, hUy, hy, le_refl Uy⟩) with N2 hN2,
  have clef : u (max N1 N2) ∈ Ux ∩ Uy,
  exact ⟨hN1 (max N1 N2) (le_max_left N1 N2), hN2 (max N1 N2) (le_max_right N1 N2)⟩,
  rwa hUxUy at clef,
end