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
  mult : univ → univ → univ
  e : univ
  ass : ∀ (x y z : univ), mult (mult x y) z = mult x (mult y z)
  neud : ∀(x : univ), mult x e = x
  neue : ∀(x : univ), mult e x = x

open monoide
-- notation : 65 lhs:65 " * " rhs:66 => mult lhs rhs

-- En un monoide l'element neutre és l'únic que és neutre a dreta
theorem TUniNeutred (S : monoide) (z : S.univ) :  (∀(w : S.univ), (S.mult z w = w)) → z = S.e := by
  intro h
  specialize h S.e
  calc
   z = S.mult z S.e := by exact (S.neud z).symm
   _ = S.e := by exact h

-- En un monoide l'element neutre és l'únic que és neutre a esquerra
theorem TUniNeutree (S : monoide) (z : S.univ) : (∀(w : S.univ), (S.mult w z = w)) → z = S.e := by
  intro h
  specialize h S.e
  calc
   z = S.mult S.e z := by exact (S.neue z).symm
   _ = S.e := by exact h

-- En un monoide l'element neutre és idempotent
theorem TUniId (S : monoide) : S.mult S.e S.e = S.e := by
  exact neue S S.e

open N
open Suma

-- N té estructura de monoide
instance sN : monoide where
  univ := N
  mult := suma
  e := z
  ass := TSumaAss
  neud := TSuma0ND
  neue := TSuma0NE
--

-- Definim els homomorfismes de monoides
structure monhom (S T : monoide) where
  f : S.univ → T.univ
  cmult : ∀(x y : S.univ), f (S.mult x y) = T.mult (f x) (f y)
  cneu : f (S.e) = T.e

-- Inclusió de generadors
def η : N → sN.univ := by
  intro n
  exact n
----

def puniv (S : monoide) (s : S.univ) : monhom sN S where
  f := by
    intro n
    induction n
    -- Cas base
    exact S.e
    -- Pas inductiu
    rename_i n hInd
    exact S.mult s hInd
  cmult := by
    intro n m
    induction n
    induction m
    simp at *
    have h1 : mult sN z z = z := by exact rfl
    rw [h1]
    have h2 : mult S S.e S.e = S.e := by exact TUniId S
    rw [h2]
    --
    rename_i m hInd
    simp at *
    have h1 : mult sN z (N.s m) = N.s m := by exact rfl
    rw [h1]
    have h2 : mult S S.e (mult S s (N.rec S.e (fun a a_ih => mult S s a_ih) m)) = (mult S s (N.rec S.e (fun a a_ih => mult S s a_ih) m)) := by
      exact neue S (mult S s (N.rec S.e (fun a a_ih => mult S s a_ih) m))
    rw [h2]
    --
    rename_i n hInd
    induction m
    have h3 : mult sN (N.s n) z = N.s n := by
      exact TSuma0ND (N.s n)
    have h4 : mult sN n z = n := by
      exact TSuma0ND n
    rw [h3, h4] at *
    simp at *
    rw [neud S] at *
    --
    rename_i m hIndm
    simp at *
    rw [ass S] at *
    have h3 : mult sN n (N.s m) = mult sN (N.s n) m := by
      exact (TSumUn n m).symm
    rw [h3] at hInd
    sorry
  cneu := by
    exact rfl
--







end monoide
