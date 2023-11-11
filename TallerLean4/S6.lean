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

-- Podem emprar notació d'infixe en compte de notació polaca
-- El número 65 expressa la urgència en avaluar el símbol
notation : 65 lhs:65 " + " rhs:66 => suma lhs rhs

-- Ara podem demostrar propietats bàsiques sobre la suma
theorem TRussell : uno + uno = dos := by
  exact rfl

-- 0 és neutre per l'esquerra per a la suma
-- Sense inducció
theorem TSuma0NE : ∀(n:N), z + n = n := by
  intro n
  cases n with
  | z => exact rfl
  | s n => exact rfl

-- 0 és neutre per la dreta per a la suma
-- Amb inducció
theorem TSuma0ND : ∀(n:N), n + z = n := by
  -----------
  -- Cas base
  have hCB : z + z = z := by exact rfl
  ---------------
  -- Pas inductiu
  have hInd (n : N) (hi : n + z = n) : (s n) + z = s n := by
    calc
      (s n) + z = s (n + z) := by exact rfl
      _         = s n       := by exact congrArg s hi
  -- Demostració per inducció
  intro n
  induction n with
  | z => exact hCB
  | s n hi => exact hInd n hi

-- Ara demostrarem que la suma commuta
-- Abans, necessitem un lema previ
theorem TSumUn : ∀ (n m : N), (s n) + m = n + (s m) := by
  -----------
  -- Cas base
  have hCB : ∀ (m:N), (s z) + m = z + (s m) := by
    intro m
    calc
      (s z) + m = s (z + m) := by exact rfl
      _ = s m := by exact rfl
      _ = z + (s m) := by exact rfl
  ---------------
  -- Pas inductiu
  have hInd (n m : N) (hi : (s n) + m = n + (s m)) : (s (s n)) + m = (s n) + (s m) := by
    calc
      (s (s n)) + m = s ((s n) + m) := by exact rfl
      _ = s (n + (s m)) := by exact congrArg s hi
      _ = (s n) + (s m) := by exact rfl
  intro n m
  induction n with
  | z => exact hCB m
  | s n hi => exact hInd n m hi

-- La suma és commutativa
theorem TSumaComm : ∀(n m : N), n + m = m + n := by
  -----------
  -- Cas base
  have hCB : ∀ (m:N), z + m = m + z := by
    intro m
    calc
      z + m  = m      := by exact rfl
      _      = m + z  := by exact (TSuma0ND m).symm
  ---------------
  -- Pas inductiu
  have hInd (n m : N) (hi : n + m = m + n) : (s n) + m = m + (s n) := by
    calc
      (s n) + m  = s (n + m)  := by exact rfl
      _             = s (m + n)  := by exact congrArg s hi
      _             = (s m) + n  := by exact rfl
      _             = m + (s n)  := by exact TSumUn m n
  -- Demostració per inducció
  intro n m
  induction n with
  | z => exact hCB m
  | s n hi => exact hInd n m hi

-- La suma és associativa
theorem TSumaAss : ∀(n m p : N), (n + m) + p = n + (m + p) := by
  -----------
  -- Cas base
  have hCB : ∀ (n m : N), (n + m) + z = n + (m + z) := by
    intro n m
    calc
      (n + m) + z = n + m := by exact TSuma0ND (suma n m)
      _ = n + (m + z) := by exact congrArg (suma n) (id (TSuma0ND m).symm)
  ---------------
  -- Pas inductiu
  have hInd (n m p: N) (hi : (n + m) + p = n + (m + p)) : (n + m) + (s p) = n + (m + (s p)) := by
    calc
      (n + m) + (s p) = (s (n + m)) + p := by exact (TSumUn (suma n m) p).symm
      _ = s ((n + m) + p) := by exact rfl
      _ = s (n + (m + p)) := by exact congrArg s hi
      _ = (s n) + (m + p) := by exact rfl
      _ = n + (s (m + p)) := by exact TSumUn n (suma m p)
      _ = n + ((s m) + p) := by exact rfl
      _ = n + (m + (s p)) := by exact congrArg (suma n) (TSumUn m p)
  intro n m p
  induction p with
  | z => exact hCB n m
  | s p hi => exact hInd n m p hi

end Suma

namespace Producte
open Suma
-- Anem a definir el producte de naturals de forma recursiva
-- Notem que fem recursió sobre n (recursió a esquerra)
def prod : N → N → N := by
  intro n m
  cases n with
  | z   => exact z
  | s n => exact (prod n m) + m

-- Podem emprar notació d'infixe en compte de notació polaca
-- El número 70 expressa la urgència en avaluar el símbol
-- Com 70 és major que 65, primer s'avaluarà el producte i després la suma
notation : 70 lhs:70 " * " rhs:71 => prod lhs rhs

-- Ara podem demostrar propietats bàsiques sobre el producte
theorem TRussell : uno * uno = uno := by
  exact rfl

-- 0 és aniquilador per l'esquerra per al producte
theorem TProd0AE : ∀(n:N), z * n = z := by
  sorry

-- 1 és neutre per l'esquerra per al producte
theorem TProd1NE : ∀(n:N), uno * n = n := by
  sorry

-- El productes és communtatiu
theorem TProdComm : ∀(n m : N), n * m = m * n := by
  sorry

-- El producte és associatiu
theorem TProdAss : ∀(n m p : N), (n * m) * p = n * (m * p) := by
  sorry

-- El producte distribueix per l'esquerra
theorem TProdDis : ∀(n m p : N), n * (m + p) = n * m + n * p := by
  sorry

end Producte
