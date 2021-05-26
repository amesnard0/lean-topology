/- Généralisation du théorème démontré dans pointwise_convergence.lean à n'importe quelle topologie engendrée.
Le cas de la topologie produit est redemontré comme un exemple à la fin du fichier. -/

import tactic
import data.set.finite

import topological_spaces
import neighbourhoods
import topological_spaces2

open set

open_locale classical

open topological_space

class open_generators (X : Type) :=
  (s : set (set X))

instance generated_topological_space {X : Type} [G : open_generators X] : topological_space X :=
  generate_from X G.s

lemma seq_lim_generated_iff {X : Type} [G : open_generators X] (u : ℕ → X) (l : X)  :
seq_lim u l ↔ ∀ g ∈ G.s, l ∈ g → ∃ (N : ℕ), ∀ n ≥ N, u n ∈ g :=
begin
  split,
  { intro hyp,
    intros g hgG hlg,
    cases hyp g (generated_filter.generator g ⟨_, hlg⟩) with N hN,
    use N,
    intros n hn,
    exact hN n hn,
    apply generated_open.generator,
    exact hgG, },
  { intro hyp,
    have clef : ∀ U, (generated_open X G.s) U → l ∈ U → ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → u n ∈ U,
    { intros U hU hlU,
      { induction hU with g hg a b ha1 hb1 ha2 hb2 C hC1 hC2,
        { cases hyp g hg hlU with N hN,
          use N, intros n hn,
          exact hN n hn, },
        { cases ha2 hlU.1 with N1 hN1,
          cases hb2 hlU.2 with N2 hN2,
          use (max N1 N2),
          intros n hn,
          have hn1 :=
          calc n ≥ max N1 N2 : hn
             ... ≥ N1        : by linarith [le_max_left N1 N2],
          have hn2 :=
          calc n ≥ max N1 N2 : hn
             ... ≥ N2        : by linarith [le_max_right N1 N2],
          exact ⟨hN1 n hn1, hN2 n hn2⟩, },
        { simp at hC2,
          rcases hlU with ⟨ c, hc, hlc⟩,
          cases hC2 c hc hlc with N hN,
          use N, intros n hn,
          use [c, hc, hN n hn], },
        { simp, }, }, },
    intros v hv,
    rcases (is_neighbourhood_iff l).1 hv with ⟨U, hU, hlU, hUv⟩,
    cases clef U hU hlU with N hN,
    use N, intros n hn,
    exact hUv (hN n hn), },
end

-- Convergence simple :
def pointwise_lim {X Y : Type} [topological_space Y] (f : ℕ → (X → Y)) (F : X → Y) : Prop :=
∀ (x : X), seq_lim (λ n, f n x) (F x)

-- Topologie produit sur X → Y :
instance fnct.open_generators (X Y : Type) [topological_space Y] : open_generators (X → Y) :=
  { s := {U | ∃ (x : X) (Ux : set Y) (hUx : is_open Ux), U = {f : X → Y | f x ∈ Ux}} }

example {X Y : Type} [topological_space Y] (f : ℕ → (X → Y)) (F : X → Y) :
pointwise_lim f F ↔ seq_lim f F :=
begin
  rw seq_lim_generated_iff,
  split,
  { intro hyp,
    intros g hg hFg,
    rcases hg with ⟨x, Ux, hUx, hg⟩,
    have hUx2 : Ux ∈ neighbourhoods (F x),
    { rw hg at hFg,
      exact generated_filter.generator Ux ⟨hUx, hFg⟩, },
    cases hyp x Ux hUx2 with N hN,
    use N, intros n hn,
    rw hg,
    exact hN n hn, },
  { intro hyp,
    intros x Vx hVx,
    rcases (is_neighbourhood_iff (F x)).1 hVx with ⟨Ux, hUx, hlUx, hUxVx⟩,
    cases hyp {g : X → Y | g x ∈ Ux} (by use [x, Ux, hUx]) hlUx with N hN,
    use N, intros n hn,
    exact hUxVx (hN n hn), },
end