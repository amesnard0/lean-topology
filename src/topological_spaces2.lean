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

-- Partie dense :
def dense {X : Type} [topological_space X] (A : set X) : Prop := closure A = univ

-- Point adhérent :
lemma point_of_closure {X : Type} [topological_space X] (A : set X) :
∀ (x : X), x ∈ closure A ↔ ∀ (V : set X), neighbourhood x V → (V ∩ A).nonempty :=
begin
  intro x,
  split,
  { intro hyp,
    rintros V ⟨U, hU, hxU, hUV⟩,
    by_contradiction hVA,
    have H1 : is_closed (compl U),
    { rw ← (compl_compl U) at hU,
      exact hU, },
    have H2 : A ⊆ compl U,
    { intros a haA,
      simp, by_contradiction haU,
      apply hVA,
      use a, split,
      exact hUV haU, exact haA, },
    specialize hyp (compl U) ⟨H1, H2⟩,
    exact hyp hxU, },
  { intro hyp,
    rintros F ⟨hF, hAF⟩,
    by_contradiction,
    have clef : neighbourhood x (compl F),
    { use (compl F),
      repeat {split},
      exact hF, exact h, exact le_refl (compl F), },
    cases hyp (compl F) clef with x hx,
    exact hx.1 (hAF hx.2), },
end

-- La limite d'une suite d'éléments de A est un point adhérent de A :
lemma seq_lim_closure {X : Type} [topological_space X] {A : set X} (u : ℕ → X) {l : X} :
(∀ n, u n ∈ A) ∧ (seq_lim u l) → l ∈ closure A :=
begin
  rintros ⟨h1, h2⟩,
  rw point_of_closure A l,
  intros V hV,
  cases h2 V hV with N hN,
  use u N, split,
  exact hN N (by linarith),
  exact h1 N,
end