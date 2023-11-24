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
  have h4 : ¬ (m ≼ z) := by exact LOrd2 m
  exact h4 h3.right

-- Lema 4
theorem LOrd4 (n m : N) (h1 : n ≼ m) : s n ≼ s m := by
  rw [Dprec] at h1
  exact congrArg s h1

-- Lema 5
theorem LOrd5 (n m k : N) : (it Dprec k n m) → (it Dprec k m n) → k = z := by
  intro h1 h2
  -- Per inducció sobre k
  induction k
  -- Cas base
  exact rfl
  -- Pas inductiu
  rename_i p hInd
  cases h1
  sorry

open Suma
#check TSumaComm

-- Lema 6
theorem LOrd6 (n m : N) : (n ≤ m) → (m ≤ n) → n = m := by
  intro h1 h2
  apply Exists.elim h1
  intro k h3
  apply Exists.elim h2
  intro l h4
  have h5 : it Dprec (k+l) n m :=  by
    apply LCrtTrans2 Dprec k l
    exact h3
  have h6 : it Dprec (l+k) m n :=  by
    apply LCrtTrans2 Dprec l k
    exact h4
  have h7 : k + l = l + k := by
    apply TSumaComm
  rw [h7] at h5
  have h8 : l+k = z := by
    exact LOrd5 n m (l+k) h5 h6
  have h9 : l = z := by
    exact TSumaz l k h8
  rw [h9] at h4
  exact h4.symm

-- La relació ≤ és antisimètrica
theorem DleqAnti : antisimetrica Dleq := by
  rw [antisimetrica]
  intro n m
  intro ⟨h1, h2⟩
  exact LOrd6 n m h1 h2
