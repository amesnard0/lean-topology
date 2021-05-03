import topological_spaces

open set

open topological_space

-- Voisinage :
def neighbourhood {X : Type} [topological_space X] (x : X) (V : set X) : Prop :=
∃ (U : set X), is_open U ∧ x ∈ U ∧ U ⊆ V

-- Convergence d'une suite :
def seq_lim {X : Type} [topological_space X] (u : ℕ → X) (l : X) : Prop :=
∀ (V : set X), neighbourhood l V → ∃ (N : ℕ), ∀ n ≥ N, u n ∈ V

-- Fonction continue :
def continuous {X Y : Type} [topological_space X] [topological_space Y] (f : X → Y) : Prop :=
∀ (U : set Y), is_open U → is_open (f ⁻¹' U)

-- Intérieur d'une partie :
def interior {X : Type} [topological_space X] (A : set X) : set X := ⋃₀ {U : set X | is_open U ∧ U ⊆ A}

-- Point intérieur :
lemma interior_point {X : Type} [topological_space X] (A : set X) :
∀ a ∈ A, a ∈ interior A ↔ ∃ U, is_open U ∧ U ⊆ A ∧ a ∈ U :=
begin
  intros a ha,
  split,
  rintro ⟨U, ⟨hU, hUA⟩, haU⟩,
  use U, repeat {split},
  exact hU, exact hUA, exact haU,
  rintro ⟨U, hU, hUA, haU⟩,
  use U, repeat {split},
  exact hU, exact hUA, exact haU,
end

-- Adhérence d'une partie :
def closure {X : Type} [topological_space X] (A : set X) : set X := ⋂₀ {F : set X | is_closed F ∧ A ⊆ F}

-- Point adhérent :
lemma point_of_closure {X : Type} [topological_space X] (A : set X) :
∀ a ∈ A, a ∈ closure A ↔ ∀ (V : set X), neighbourhood a V → (V ∩ A).nonempty :=
begin
  intros a ha,
  split,
  intro hyp,
  rintros V ⟨U, hU, haU, hUV⟩,
  use a, split,
  exact hUV haU,
  exact ha,
  intro hyp,
  rintros F ⟨hF, hAF⟩,
  by_contradiction,
  have clef : neighbourhood a (compl F),
  { use (compl F),
    repeat {split},
    exact hF, exact h, exact le_refl (compl F), },
  cases hyp (compl F) clef with x hx,
  exact hx.1 (hAF hx.2),
end

-- Partie dense :
def dense {X : Type} [topological_space X] (A : set X) : Prop := closure A = univ