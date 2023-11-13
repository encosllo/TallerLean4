-- Sessió 7 - 20/11/23
-- Definim structures i classes

import TallerLean4.S6
import Mathlib.Tactic.LibrarySearch

-- En aquesta sessió anem a implementar classes i estructures
-- Seguirem https://lean-lang.org/theorem_proving_in_lean4/type_classes.html

-- Definim una estructura que dependrà d'un tipus α
-- i contindrà tipus amb operacions binàries
structure Bin (α : Type) where
  bin : α → α → α

-- Una vegada definida l'estructura podem considerar objectes del tipus Bin
#check Bin
-- Notem que l'estructura depen d'un paràmetre α
-- Així per exemple un objecte de tipus Bin ℕ podem pensar-lo com a una instància concreta
-- d'una operació binària sobre els naturals
#check Bin ℕ

-- Podem considerar estructures binàries sobre els naturals
variable (Est : Bin ℕ)
-- Aquestes estructures ens permeten recuperar l'operació que codifiquen
#check Est.bin

-- Podem, per exemple, definir les estructures de suma i producte
-- en els naturals que vam definir en l'anterior sessió
def NSum : Bin N := {bin := Suma.suma}
-- També podem definir una estructura com segueix
def NProd : Bin N where
  bin := Producte.prod

#check NSum
#check NProd

-- Donada una estructura del tipus Bin α, podem definir la iterada de l'operació  binària
def it {α : Type} (s : Bin α) (x : α) : α :=
  s.bin x x

-- Per al cas concret de N
open N
#check it NSum z

-- Es pot comprovar que la iterada de l'operació funciona com esperem
theorem TItSumz : it NSum z = z := by rfl
theorem TItSumu : it NSum uno = dos := by rfl
theorem TItProdz : it NProd z = z := by rfl
theorem TItProdu : it NProd uno = uno := by rfl

-- Les classes, per contra
class Opbin (α : Type) where
  bin : α → α → α

#check @Opbin.bin

variable (Estr : Opbin ℕ)
#check Estr

-- Ara ja no podem definir objectes d'una classe amb def
-- Caldrà donar instàncies

instance : Opbin N where
  bin := Suma.suma


#check NOpbinSum
