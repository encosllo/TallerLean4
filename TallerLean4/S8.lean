-- Sessió 8 - 27/11/23
-- Definim l'ordre sobre els naturals

import TallerLean4.S7

-- En aquesta sessió anem a implementar l'ordre habitual sobre els naturals

-- Recordem algunes definicions bàsiques
-- Relació irreflexiva
def irreflexiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x : X), ¬ R x x

-- Obrim la clausura reflexivo-transitiva
open ClRT
-- Obrim els nostre naturals
open N

-- Definim la següent relació de predecessor sobre N
def Dprec : N → N → Prop := by
  intro n m
  exact m = s n

-- Considerem la clausura reflexivo-transitiva de
-- la relació de predecessor
def Dleq : N → N → Prop := crt Dprec

-- Emprarem la següent notació per a estes relacions
-- ≼ (\preceq) per a la relació de predecessor
notation : 65 lhs:65 " ≼ " rhs:66 => Dprec lhs rhs
-- ≤ (\leq) per a la clausura reflexivo-transitiva
notation : 65 lhs:65 " ≤  " rhs:66 => Dleq lhs rhs

-- Comprovem que que ≤ és un ordre sobre N
-- Per a fer-ho considerarem els següents lemmes
-- Lema 1
theorem LOrd1  (n m : N) : ¬ ((n ≼ m) ∧ (m ≼ n)) := by
  by_contra h
  have h1 : n≼m := by exact h.left
  have h2 : m≼n := by exact h.right
  rw [Dprec] at h1 h2
  rw [h2] at h1
  have h3 (k : N) : ¬ k = s (s k) := by
    by_contra h3
    -- Per inducció sobre k
    induction k
    -- Cas base
    injection h3
    -- Pas inductiu
    rename_i k hInd
    injection h3 with h3
    exact hInd h3
  specialize h3 m
  exact h3 h1

-- La relació ≼ és antisimètrica
theorem DprecAnti : antisimetrica Dprec := by
  intro n m
  intro h1
  have h2 : ¬ ((n ≼ m) ∧ (m ≼ n)) := by exact LOrd1 n m
  exact False.elim (h2 h1)

-- Lema 2
theorem LOrd2 (n : N) : ¬ (n ≼ z) := by
  by_contra h1
  induction n
  injection h1
  rename_i k hInd
  rw [Dprec] at h1
  injection h1

-- Lema 3
theorem LOrd3 (n : N) (h1: n ≠ z) : ¬ (n ≤ z) := by
  by_contra h1
  induction h1
  rename_i k hInd
  induction k
  have h2 : n = z := by exact hInd
  exact h1 h2
  rename_i k hIndk
  -- Per casos sobre hInd
  cases hInd
  -- Cas inl
  rename_i hinl
  exact hIndk hinl
  -- Cas inr
  rename_i hinr
  apply Exists.elim hinr
  intro m
  intro h3
  have h4 : ¬ (m≼z) := by exact LOrd2 m
  exact h4 h3.right

-- Lema 4
theorem LOrd4 (n m : N) (h1 : n ≼ m) : s n ≼ s m := by
  rw [Dprec] at h1
  exact congrArg s h1

-- Lema 5
theorem LOrd5 (n m : N) (h1 : n ≤ m) : s n ≤ s m := by
  rw [Dleq] at h1
  apply Exists.elim h1
  intro k h2
  -- Per inducció sobre k
  induction k
  -- Cas base
  have h3 : n = m := by exact h2
  use z
  exact congrArg s h2
  -- Pas inductiu
  rename_i k hIndk
  cases h2
  -- Cas inl
  rename_i hinl
  exact hIndk hinl
  -- Cas inr
  rename_i hinr
  apply Exists.elim hinr
  intro p
  intro ⟨h3, h4⟩
  rw [Dprec] at h4
  use k
  sorry

-- Lema 6
theorem LOrd6 (n m : N) (h1 : n ≼ m) : ¬ (m ≤ n) := by
  by_contra h2
  rw [Dprec] at h1
  rw [h1] at h2
  rw [Dleq] at h2
  -- Per inducció sobre n
  induction n
  -- Cas base
  have h3 : (s z) ≤ z := by exact h2
  have h4 : s z ≠ z := by
    by_contra h4
    injection h4
  have h5 : ¬ (s z ≤ z) := by exact LOrd3 (s z) h4
  exact h5 h2
  -- Pas inductiu
  rename_i k hInd
  apply Exists.elim h2
  intro l
  intro h3
  induction l
  have h4 : s (s k) = s k := by exact h3
  injection h4 with h4
  rw [h4] at h1 h2
  exact hInd h1 h2
  rename_i l hIndl
  -- Per casos sobre h3
  cases h3
  -- Cas inl
  rename_i hinl
  exact hIndl hinl
  -- Cas inr
  rename_i hinr
  apply Exists.elim hinr
  intro p
  intro ⟨h3, h4⟩
  rw [Dprec] at h4
  injection h4 with h4
  rw [h4.symm] at h3











-- La relació ≤ és antisimètrica
theorem DleqAnti : antisimetrica Dleq := by
  rw [antisimetrica]
  intro n m
  intro ⟨h1, h2⟩
  -- Per inducció sobre h1
  induction h1
  rename_i p q h1
