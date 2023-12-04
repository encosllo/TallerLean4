-- Sessió 9
-- Definim structures i classes

import TallerLean4.S8
import TallerLean4.S6

-- En aquesta sessió anem a implementar classes i estructures
-- Seguirem https://lean-lang.org/theorem_proving_in_lean4/type_classes.html

namespace bin
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
def doble {α : Type} (s : Bin α) (x : α) : α :=
  s.bin x x

-- Per al cas concret de N
open N
#check doble NSum z

-- Es pot comprovar que la iterada de l'operació funciona com esperem
theorem TDSumz : doble NSum z = z := by rfl
theorem TDSumu : doble NSum uno = dos := by rfl
theorem TDProdz : doble NProd z = z := by rfl
theorem TDProdu : doble NProd uno = uno := by rfl

-- La idea principal darrere de les classes de tipus
-- és permetre l'aplicació implícita de comportaments
-- (definits per les classes de tipus) a diferents tipus

-- Podem definir com aquests comportaments haurien de
-- funcionar per als seus propis tipus, i el compilador,
-- a través de la resolució de classes de tipus,
-- sintetitza automàticament les instàncies correctes
-- de la base de dades d'instàncies definides pels usuaris
class Opbin (α : Type) where
  bin : α → α → α

#check @Opbin.bin

variable (Estr : Opbin ℕ)
#check Estr
#check Estr.bin

-- Ara ja no podem definir objectes d'una classe amb def
-- Caldrà donar instàncies

instance CSum : Opbin N where
  bin := Suma.suma

  #check CSum
  #check CSum.bin

end bin

namespace monoide
-- Definim l'estructura dels monoides
structure monoide where
  univ : Type
  op : univ → univ → univ
  e : univ
  ass : ∀ (x y z : univ), op (op x y) z = op x (op y z)
  neud : ∀(x : univ), op x e = x
  neue : ∀(x : univ), op e x = x

open monoide
-- notation : 65 lhs:65 " * " rhs:66 => op lhs rhs

-- En un monoide l'element neutre és l'únic que és neutre a dreta
theorem TUniNeutred (S : monoide) (z : S.univ) :  (∀(w : S.univ), (S.op z w = w)) → z = S.e := by
  intro h
  specialize h S.e
  calc
   z = S.op z S.e := by exact (S.neud z).symm
   _ = S.e := by exact h

-- En un monoide l'element neutre és l'únic que és neutre a esquerra
theorem TUniNeutree (S : monoide) (z : S.univ) : (∀(w : S.univ), (S.op w z = w)) → z = S.e := by
  intro h
  specialize h S.e
  calc
   z = S.op S.e z := by exact (S.neue z).symm
   _ = S.e := by exact h

-- En un monoide l'element neutre és idempotent
theorem TUniId (S : monoide) : S.op S.e S.e = S.e := by
  exact neue S S.e

open N
open Suma

-- N té estructura de monoide
instance sN : monoide where
  univ := N
  op := suma
  e := z
  ass := TSumaAss
  neud := TSuma0ND
  neue := TSuma0NE
--

-- ℕ té estructura de monoide
instance sNat : monoide where
  univ := ℕ
  op := by
    intro n m
    exact n + m
  e := 0
  ass := by
    intro n m p
    exact Nat.add_assoc n m p
  neud := by
    intro n
    exact rfl
  neue := by
    intro n
    exact Nat.zero_add n
--

-- Definim els homomorfismes de monoides
structure monhom (S T : monoide) where
  f : S.univ → T.univ
  cop : ∀(x y : S.univ), f (S.op x y) = T.op (f x) (f y)
  cneu : f (S.e) = T.e

-- Inclusió de generadors
def η : N → sN.univ := by
  intro n
  exact n
----

def punivf (S : monoide) (s : S.univ) : sNat.univ → S.univ := by
  intro n
  induction n
  exact S.e
  rename_i n hInd
  exact S.op s hInd

#check Nat.sum

def puniv (S : monoide) (s : S.univ) : monhom sNat S where
  f := punivf S s
  cop := by
    intro n
    induction n
    intro m
    have h1 : op sNat Nat.zero m = m := by
      induction m
      exact rfl
      rename_i m hIndm
      have h2 : op sNat Nat.zero (Nat.succ m) = Nat.succ (op sNat Nat.zero m) := by exact rfl
      rw [h2]
      exact congrArg Nat.succ hIndm
    rw [h1]
    have h2 : punivf S s Nat.zero = S.e := by exact rfl
    rw [h2]
    rw [S.neue]
    rename_i n hInd
    intro m
    have h1 : op sNat (Nat.succ n) m = op sNat n (Nat.succ m) := by
      sorry
    rw [h1]
    rw [hInd (Nat.succ m)]
    have h2 : punivf S s (Nat.succ n) = S.op s (punivf S s n) := by exact rfl
    rw [h2]
    have h3 : punivf S s (Nat.succ m) = S.op s (punivf S s m) := by exact rfl
    rw [h3]
    rw [S.ass] at *
    sorry
  cneu := by
    exact rfl
--







end monoide
