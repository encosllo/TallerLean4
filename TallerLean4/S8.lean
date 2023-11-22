-- Sessió 8 - 27/11/23
-- Definim l'ordre sobre els naturals

import TallerLean4.S7

-- En aquesta sessió anem a implementar l'ordre habitual sobre els naturals

-- Recordem algunes definicions bàsiques
-- Relació irreflexiva
def irreflexiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x : X), ¬ R x x

-- Obrim els resultats de la clausura reflexivo-transitiva
open ClRT
-- Obrim els nostre naturals
open N

-- El següent resultat ens diu que si una relació és irreflexiva,
-- aleshores la seua clausura reflexivo-transitiva és un ordre
theorem TIrrOr {X : Type} (R : X → X → Prop) (h : irreflexiva R) : ordre (crt R) := by
  rw [ordre]
  apply And.intro
  -- Reflexiva
  exact TCrtRfl R
  --
  apply And.intro
  -- Antisimètrica
  rw [antisimetrica]
  intro x y
  intro ⟨h1, h2⟩
  apply Exists.elim h1
  intro n
  intro h3
  apply Exists.elim h2
  intro m
  intro h4
  -- Per inducció sobre n
  induction n
  -- Cas base
  exact h3
  rename_i n hIndn
  -- Per inducció sobre m
  induction m
  -- Cas base
  exact h4.symm
  rename_i m hIndm
  --
  cases h3
  rename_i h5
  exact hIndn h5
  rename_i h5
  cases h4
  rename_i h4
  exact hIndm h4
  rename_i h4
  sorry
