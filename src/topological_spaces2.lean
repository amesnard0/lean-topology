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

-- Une fonction est continue si et seulement si l'image réciproque de tout fermé est un fermé :
lemma continuous_closed {X Y : Type} [topological_space X] [topological_space Y] (f : X → Y) :
continuous f ↔ ∀ (F : set Y), is_closed F → is_closed (f ⁻¹' F) :=
begin
  split,
  { intro hyp,
    intros F hF,
    exact hyp (compl F) hF, },
  { intro hyp,
    intros U hU,
    rw ← compl_compl U at hU,
    rw ← compl_compl (f ⁻¹' U),
    exact hyp (compl U) hU, },
end

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

-- L'adhérence d'une partie est fermée :
lemma closure_closed {X : Type} [topological_space X] (A : set X) :
is_closed (closure A) :=
begin
  unfold is_closed, unfold closure,
  rw compl_sInter,
  apply union,
  rintros U ⟨F, ⟨hF, hAF⟩, hU⟩,
  rw ← hU,
  exact hF,
end

-- Une partie est fermée si et seulement si elle est égale à son adhérence :
lemma is_closed_iff {X : Type} [topological_space X] (F : set X) :
is_closed F ↔ F = closure F :=
begin
  split,
  { intro hyp,
    apply le_antisymm,
    { apply subset_sInter, simp, },
    { apply sInter_subset_of_mem,
      split,
      exact hyp,
      exact le_refl F, }, },
  { intro hyp,
    rw hyp,
    exact closure_closed F, },
end

-- Croissance de l'adhérence :
lemma closure_subset {X : Type} [topological_space X] {A B : set X} :
A ⊆ B → closure A ⊆ closure B :=
begin
  intro hyp,
  intros x hx,
  rintros F ⟨hF, hBF⟩,
  apply hx F, split,
  exact hF,
  rw ← le_eq_subset,
  exact le_trans hyp hBF,
end

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

-- Une caractérisation de la continuité :
example {X Y : Type} [topological_space X] [topological_space Y] (f : X → Y) :
continuous f ↔ ∀ (A : set X), f '' (closure A) ⊆ closure (f '' A) :=
begin
  split,
  { intro hyp,
    intro A,
    rintros y ⟨x, hx, hy⟩,
    rw point_of_closure (f '' A) y,
    rintros V ⟨U, hU, hyU, hUV⟩,
    have clef : neighbourhood x (f ⁻¹' U),
    { use (f ⁻¹' U), repeat {split},
      exact hyp U hU,
      rw ← hy at hyU,
      exact hyU,
      exact le_refl (f ⁻¹' U), },
    cases (point_of_closure A x).1 hx (f ⁻¹' U) clef with x' hx',
    use f x',
    split,
    exact hUV hx'.1,
    use x', simp [hx'.2], },
  { intro hyp,
    rw continuous_closed,
    intros F hF,
    rw is_closed_iff,
    apply le_antisymm,
    { apply subset_sInter, simp, },
    { specialize hyp (f ⁻¹' F),
      rw ← le_eq_subset at hyp,
      have hyp' := le_trans hyp (closure_subset (image_preimage_subset f F)),
      rw ← (is_closed_iff F).1 hF at hyp',
      simp at hyp', exact hyp', }, },
end