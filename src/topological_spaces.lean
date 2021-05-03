import tactic
import data.set.finite

open set

-- Definition d'un espace topologique :
@[ext]
class topological_space (X : Type) :=
  (is_open  : set X → Prop)
  (univ_mem : is_open univ)
  (union    : ∀ (B : set (set X)) (h : ∀ b ∈ B, is_open b), is_open (⋃₀ B))
  (inter    : ∀ (A B : set X) (hA : is_open A) (hB : is_open B), is_open (A ∩ B))

namespace topological_space

-- Fermés :
def is_closed {X : Type} [topological_space X] : set X → Prop := λ F, is_open (compl F)

-- Preuve que l'ensemble vide est un ouvert à partir des autres axiomes :
lemma empty_mem {X : Type} [topological_space X] : is_open (∅ : set X) :=
begin
  have : (∅ : set X) = ⋃₀ ∅, simp, rw this,
  apply union,
  intros b hb, exfalso, exact hb,
end

-- Toute intersection finie d'ouverts est un ouvert :
lemma finite_inter {X : Type} [topological_space X] :
∀ (B : set (set X)) (hB : finite B) (h : ∀ b ∈ B, is_open b), is_open (⋂₀ B) :=
begin
  intros b hB,
  apply finite.induction_on hB,
  simp, exact univ_mem,
  intros a s ha hs h1 h2,
  have clef : ⋂₀insert a s = ⋂₀s ∩ a,
  { apply le_antisymm,
    { intros x hx,
      split,
      intros b hb,
      apply hx, right, exact hb,
      apply hx, left, refl, },
    { intros x hx,
      intros b hb,
      cases hb with hb1 hb2,
      rw hb1,
      exact hx.2,
      exact hx.1 b hb2, }, },
  rw clef,
  apply inter,
  { apply h1,
    intros b hb,
    apply h2 b,
    right,
    exact hb, },
  { apply h2 a,
    left,
    refl, },
end

-- Topologie discrete :
def discrete (X : Type) : topological_space X :=
{ is_open  := λ U, true,
  univ_mem := trivial,
  union    := begin intros B h, trivial, end,
  inter    := begin intros A hA B hB, trivial, end }

-- Definition d'un espace discret :
class discrete_space (X : Type) [topological_space X] := 
(all_open : ∀ U : set X, is_open U)

-- Topologie engendrée par un ensemble de parties :
inductive generated_open (X : Type) (g : set (set X)) : set X → Prop
| generator : ∀ A ∈ g, generated_open A
| inter     : ∀ A B, generated_open A → generated_open B → generated_open (A ∩ B)
| union     : ∀ (B : set (set X)), (∀ b ∈ B, generated_open b) → generated_open (⋃₀ B)
| univ      : generated_open univ

def generate_from (X : Type) (g : set (set X)) : topological_space X :=
{ is_open   := generated_open X g,
  univ_mem  := generated_open.univ,
  inter     := generated_open.inter,
  union     := generated_open.union }

-- Topologie grossière :
def indiscrete (X : Type) : topological_space X :=
  generate_from X {∅, univ}

end topological_space

open topological_space

-- Topologie produit :
instance prod.topological_space (X Y : Type) [topological_space X]
  [topological_space Y] : topological_space (X × Y) :=
topological_space.generate_from (X × Y) {U | ∃ (Ux : set X) (Uy : set Y)
  (hx : is_open Ux) (hy : is_open Uy), U = set.prod Ux Uy}

-- Les ouverts pour la topologie produit sont les réunions d'ouverts élémentaires :
lemma is_open_prod_iff (X Y : Type) [topological_space X] [topological_space Y]
  {s : set (X × Y)} :
is_open s ↔ (∀a b, (a, b) ∈ s → ∃u v, is_open u ∧ is_open v ∧
                                  a ∈ u ∧ b ∈ v ∧ set.prod u v ⊆ s) :=
begin
  split,
  { intros hyp a b hab,
    induction hyp,
    { rcases hyp_H with ⟨ Ux, Uy, hx, hy, hs ⟩,
      rw hs at hab,
      use [Ux, Uy], repeat {split},
      exact hx, exact hy, exact hab.1, exact hab.2, rw hs, },
    { rcases hyp_ih_ᾰ hab.1 with ⟨u1, v1, ⟨h1a, h1b, h1c, h1d, h1e⟩⟩,
      rcases hyp_ih_ᾰ_1 hab.2 with ⟨u2, v2, ⟨h2a, h2b, h2c, h2d, h2e⟩⟩,
      use [u1 ∩ u2, v1 ∩ v2], repeat {split},
      exact inter u1 u2 h1a h2a,
      exact inter v1 v2 h1b h2b,
      exact h1c, exact h2c,
      exact h1d, exact h2d,
      intros uv huv, split,
      apply h1e, split, exact huv.1.1, exact huv.2.1,
      apply h2e, split, exact huv.1.2, exact huv.2.2, },
    { rcases hab with ⟨hyp_b, hbB, habb ⟩,
      rcases hyp_ih hyp_b hbB habb with ⟨u, v, ⟨ha, hb, hc, hd, he⟩⟩,
      use [u, v], repeat {split},
      exact ha, exact hb, exact hc, exact hd,
      intros uv huv, use hyp_b, split, exact hbB, exact he huv, },
    { use [univ, univ],
      simp, split; exact univ_mem, }, },
  { intro hyp,
    choose f1 hf1 using hyp,
    choose f2 hf2 using hf1,
    have clef : s = ⋃₀ {(f1 a b ᾰ).prod (f2 a b ᾰ) | (a : X) (b : Y) (ᾰ : (a, b) ∈ s)},
    { apply le_antisymm,
      { rintros ⟨a, b⟩ hab,
        use ((f1 a b hab).prod (f2 a b hab)), split,
        use [a, b, hab], split,
        exact (hf2 a b hab).2.2.1,
        exact (hf2 a b hab).2.2.2.1, },
      { rintros uv ⟨ UV, ⟨ ⟨a, b, hab, h⟩, huv ⟩⟩,
        rw ← h at huv,
        exact (hf2 a b hab).2.2.2.2 huv, }, },
    rw clef,
    apply union,
    rintros UV ⟨a, b, hab, h⟩,
    rw ← h,
    apply generated_open.generator,
    use [f1 a b hab, f2 a b hab], rw exists_prop, repeat {split},
    exact (hf2 a b hab).1, exact (hf2 a b hab).2.1,
  },
end

namespace topological_space

-- Definition d'une topologie à partir de ses fermés :
def mk_closed_sets
  (X : Type)
  (σ : set (set X))
  (empty_mem : ∅ ∈ σ)
  (univ_mem : univ ∈ σ)
  (inter : ∀ B ⊆ σ, ⋂₀ B ∈ σ)
  (union : ∀ (A ∈ σ) (B ∈ σ), A ∪ B ∈ σ) :
topological_space X := {
  is_open := λ U, U ∈ compl '' σ,
  univ_mem :=
  begin
    apply (mem_compl_image _ _).2,
    rw compl_univ,
    exact empty_mem
  end,
  union :=
  begin
    intros B hB,
    apply (mem_compl_image _ _).2,
    rw compl_sUnion,
    apply inter,
    intros cb hcb,
    rw ← compl_compl cb,
    exact (mem_compl_image _ _).1 (hB (compl cb) ((mem_compl_image _ _).1 hcb)),
  end,
  inter :=
  begin
    intros A B hA hB,
    apply (mem_compl_image _ _).2,
    rw compl_inter,
    exact union (compl A) ((mem_compl_image _ _).1 hA) (compl B) ((mem_compl_image _ _).1 hB),
  end,
  }

end topological_space