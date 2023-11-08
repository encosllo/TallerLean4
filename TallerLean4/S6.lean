-- Sessió 6 - 13/11/23
-- Definim els naturals i les seues operacions bàsiques
-- Fem demostracions per inducció

import TallerLean4.S5
import Mathlib.Tactic.LibrarySearch

open Classical

-- Els números naturals estan implementats en Lean
-- ℕ (\nat o \N o Nat)
#check ℕ
#print Nat

-- No obstant, anem a construïr-los con un tipus inductiu
-- Per a més informació consulteu
-- https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html
inductive N : Type where
  | z
  | s : N →  N

-- Segons la nostra definició hem definit l'estructura (N,z,s),
-- On z (representant el zero), serà un element de tipus N
#check N.z
-- I s (reprentant el successor), serà una aplicació de N en N
#check N.s

-- Per a treballar amb N sense necessitat d'escriure la comanda N
-- podem obrir el tipus per a importar la notació
open N

#check z
#check s

-- Amb açò ja podem definir elements
def zero : N := z
def uno  : N := s zero
def dos  : N := s uno
-- ...

namespace RecInd
-- Anem a definir una aplicació de N en Prop
-- L'aplicació compararà un objecte de tipus N amb el zero
-- Si són iguals tornarà Vertader
-- Si són diferents tornarà Fals
-- Açò és un exemple de definició per recursió
def Eqzero : N → Bool := by
  intro n
  cases n with
  | z   => exact true
  | s n => exact false

#eval Eqzero zero
#eval Eqzero uno

-- Anem a demostrar teoremes sobre N
-- Les demostracions es faran per inducció
-- induction és un procediment que serveix per a tot tipus inductiu

-- Tots els termes de la forma s n són diferents de zero
theorem EqzeroA : ∀(n:N), Eqzero (s n) = false := by
  intro n
  induction n with
  | z => exact rfl
  | s n => exact rfl

-- L'únic valor que és igual a zero és el zero
theorem EqzeroB : ∀(n:N), (Eqzero n = true) ↔ (n = z) := by
  -----------
  -- Cas base
  have hCB : Eqzero z = true ↔ z = z := by
    apply Iff.intro
    -- Esquerra
    intro h
    exact rfl
    -- Dreta
    intro h
    exact rfl
  ---------------
  -- Pas inductiu
  have hInd (n : N) (hi : Eqzero n = true ↔ n = z) : Eqzero (s n) = true ↔ (s n) = z := by
    apply Iff.intro
    -- Esquerra
    intro h1
    rw [EqzeroA n] at h1
    exact False.elim (Bool.not_false' h1)
    -- Dreta
    intro h1
    rw [h1]
    exact rfl
  -- Demostració per inducció
  intro n
  induction n with
  | z => exact hCB
  | s n hi => exact hInd n hi

-- Notem que en el pas anterior no hem fet ús de la hipòtesi inductive
-- Això vol dir que en comptes de fer una demostració per inducció
-- Podríem simplement haver fet una demostració per casos
-- Tornem a plantejar el mateix resultat que abans i demostrem-lo per casos
theorem EqzeroC : ∀(n:N), (Eqzero n = true) ↔ (n = z) := by
  -----------
  -- Cas base
  have hCB : Eqzero z = true ↔ z = z := by
    apply Iff.intro
    -- Esquerra
    intro h
    exact rfl
    -- Dreta
    intro h
    exact rfl
  ---------------
  -- Pas inductiu
  have hInd (n : N) : Eqzero (s n) = true ↔ (s n) = z := by
    apply Iff.intro
    -- Esquerra
    intro h1
    rw [EqzeroA n] at h1
    exact False.elim (Bool.not_false' h1)
    -- Dreta
    intro h1
    rw [h1]
    exact rfl
  -- Demostració per inducció
  intro n
  cases n with
  | z => exact hCB
  | s n => exact hInd n

end RecInd

namespace Suma
-- Anem a definir la suma de naturals de forma recursiva
-- Notem que fem recursió sobre n (recursió a esquerra)
def suma : N → N → N := by
  intro n m
  cases n with
  | z   => exact m
  | s n => exact s (suma n m)

-- La suma també es pot definir per recursió sobre m (recursió a dreta)
def sumar : N → N → N := by
  intro n m
  cases m with
  | z   => exact n
  | s m => exact s (suma n m)



-- Ara podem demostrar propietats bàsiques sobre la suma
-- 0 és neutre per l'esquerra per a la suma
-- Sense inducció
theorem TSuma0NE : ∀(n:N), suma z n = n := by
  intro n
  cases n with
  | z => exact rfl
  | s n => exact rfl

-- 0 és neutre per la dreta per a la suma
-- Amb inducció
theorem TSuma0ND : ∀(n:N), suma n z = n := by
  -----------
  -- Cas base
  have hCB : suma z z = z := by exact rfl
  ---------------
  -- Pas inductiu
  have hInd (n : N) (hi : suma n z = n) : suma (s n) z = s n := by
    calc
      suma (s n) z = s (suma n z) := by exact rfl
      _            = s n          := by exact congrArg s hi
  -- Demostració per inducció
  intro n
  induction n with
  | z => exact hCB
  | s n hi => exact hInd n hi

-- La suma és commutativa
theorem TSumaComm : ∀(n m : N), suma n m = suma m n := by
  -----------
  -- Cas base
  have hCB : ∀ (m:N), suma z m = suma m z := by
    intro m
    calc
      suma z m  = m         := by exact rfl
      _         = suma m z  := by exact (TSuma0ND m).symm
  ---------------
  -- Pas inductiu
  have hInd (n m : N) (hi : suma n m = suma m n) : suma (s n) m = suma m (s n) := by
    have h1 : suma (s n) m = s (suma n m) := by exact rfl
    have h2 : s (suma n m) = suma n (s m) := by sorry
    sorry
  -- Demostració per inducció
  intro n m
  induction n with
  | z => exact hCB m
  | s n hi => exact hInd n m hi

end Suma
