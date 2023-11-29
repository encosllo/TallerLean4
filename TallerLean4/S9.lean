-- Sessió 9
-- Definim structures i classes

import TallerLean4.S8

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


namespace semigrups

-- Definim la classes dels monoides
class monoide where
  univ : Type
  mult : univ → univ → univ
  e : univ
  ass : ∀ (x y z : univ), mult (mult x y) z = mult x (mult y z)
  neud : ∀(x : univ), mult x e = x
  neue : ∀(x : univ), mult e x = x

open monoide
notation : 65 lhs:65 " * " rhs:66 => mult lhs rhs

-- En un monoide l'element neutre és l'únic que és neutre a dreta
theorem TUniNeutred [S : monoide] (z : univ) :  (∀(w : univ), (z*w = w)) → z = e := by
  intro h
  specialize h e
  calc
   z = z * e := by exact (neud z).symm
   _ = e := by exact h

-- En un monoide l'element neutre és l'únic que és neutre a esquerra
theorem TUniNeutree [S : monoide] (z : univ) : (∀(w : univ), (w*z= w)) → z = e := by
  intro h
  specialize h e
  calc
   z = e * z := by exact (neue z).symm
   _ = e := by exact h

-- Definim els homomorfismes de monoides
class monhom where
  dom : monoide
  cod : monoide
  f : dom.univ → cod.univ
  cmult : ∀(x y : dom.univ), f (dom.mult x y) = cod.mult (f x) (f y)
  cneu : f (dom.e) = cod.e


-- N té estructura de monoide
instance sN : monoide where
  univ := N
  mult := Suma.suma
  e := z
  ass := Suma.TSumaAss
  neud := Suma.TSuma0ND
  neue := Suma.TSuma0NE

--







end semigrups
