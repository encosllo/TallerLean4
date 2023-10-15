-- Sessió 1 - 02/10/23
-- Treballem amb Proposicions

-- L'objectiu d'aquesta sessió és introduïr el tipus de les proposicions, els connectors lògics i realitzar les primeres demostracions
-- Prop és el tipus de les proposicions
#check Prop

namespace DefVar
-- Definim una variable P de tipus Prop
variable (P : Prop)
#check P

-- Les proposicions, al seu torn, poden fer de tipus
-- Més informació https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html
variable (h : P)
#check h
end DefVar

namespace DefCon 
-- En aquest espai introduïm les connectives proposicionals
-- Definim variables P, Q de tipus Prop
variable (P Q : Prop)

-- Conjunció ∧ (\and) 
-- Si P i Q són de tipus Prop, aleshores P∧Q també és de tipus Prop
#check P∧Q  

-- Disjunció ∨ (\or) 
-- Si P i Q són de tipus Prop, aleshores P∨Q també és de tipus Prop
#check P∨Q

-- Negació ¬ (\not) 
-- Si P és de tipus Prop, aleshores ¬P també és de tipus Prop
#check ¬P

-- Implicació → (\to) 
-- Si P i Q són de tipus Prop, aleshores P→Q també és de tipus Prop
#check P→Q

-- Doble implicació ↔ (\iff) 
-- Si P i Q són de tipus Prop, aleshores P↔Q també és de tipus Prop
#check P↔Q

-- La veritat (True) té tipus Prop
#check True 
-- No confondre amb true, que té tipus Bool
#check true

-- La falsedat (False) té tipus Prop
#check False
-- No confondre amb false, que té tipus Bool
#check false
end DefCon

namespace Teo
-- En aquest espai farem les nostres primeres demostracions
-- Definim variables P, Q de tipus Prop
variable (P Q : Prop)

-- A continuació presentem el nostre teorema i provem de demostrar-lo
-- Per a introduïr l'enunciat escrivim theorem, a continuació el nom del teorema (en aquest cas Teo1), després les hipòtesi que té (en aquest cas h, de tipus P) i finalment els dos punts i la conclusió (en aquest cas : P)
-- A continuació escrivim := (igual que per a les definicions)
-- Si botem de línia i indentem podrem escriure sorry, que és una comanda per a finalitzar processos
-- En posar-nos a la dreta de sorry ens apareixen les hipòtesis del teorema i el que ens cal demostrar
-- En aquest cas tenim a P i Q assumides com a variables de tipus Prop, una hipòtesis de tipus P i el símbol ⊢ (\vdash) -de conseqüència sintàctica- acompanyat de P, la conclusió a la què volem arribar
theorem Teo1 (h : P) : P := 
  sorry

-- Tornem a escriure el teorema -amb un nou nom- i el demostrem
-- Com que tenim assumida h de tipus P i volem aconseguir P, podem dir que ja el tenim, fent referència a h
theorem Teo2 (h : P) : P :=
  show P from h
-- El teorema Teo2 està demostrat i ara podem emprar-lo en la resta del fitxer
#check Teo2
#print Teo2
-- El teorema Teo 2 té tipus ∀ (P : Prop), P → P
-- Té sentit aplicar el teorema sobre una variable de tipus Prop
-- Adona't que, en aplicar-lo sobre P, el seu tipus és P→P
#check Teo2 P
-- En aplicar-lo sobre Q, el seu tipus canvia a Q→Q
#check Teo2 Q 


-- Podem emprar diferent sintaxi per a la demostració del mateix Teorema
-- Adoneu-vos de la inclusió de l'ítem by a l'inici de la demostració
theorem Teo3 (h : P) : P := by
  exact h

-- Els teoremes poden emprar-se dins de la demostració d'altres teoremes
theorem Teo4 (h : P) : P := by
  exact (Teo2 P) h

-- En els teoremes podem tindre objectius intermedis amb la comanda have
theorem Teo5 (h : P) : P := by 
  have h' : P := by exact h 
  exact h'

-- Els example funcionen com els teoremes, però no reben nom -i, per tant, no podrem cridar-los més endavant
example (h : P) : P := by
  exact h

end Teo

namespace InOut
-- En aquest espai vorem com introduïr i eliminar connectors lògics
-- Definim variables P, Q de tipus Prop
variable (P Q R: Prop)

-- ////////////////////////////////////
-- Introducció de la implicació 
-- Si tenim la variable Q, podem concloure P→Q
theorem T1 (h1 : Q) : P→Q := by
-- En aquest cas assumim la hipòtesi i de la implicació
  intro h2
-- Demostrem Q 
  exact h1

-- Eliminació de la implicació (Modus Ponens)
-- Si tenim com a hipòtesi P→Q i P, podem concloure Q
-- Simplement tractem P→Q com si fora una aplicació i la fem actuar sobre P
theorem T2 (h1 : P → Q) (h2 : P) : Q := by
  exact h1 h2 

-- ////////////////////////////////////
-- Introducció de la conjunció
-- Si tenim com a hipòtesis P i Q, podem deduïr P∧Q amb la comanda And.intro
theorem T3 (h1 : P) (h2 : Q) : P∧Q := by
  exact And.intro h1 h2

-- Eliminació de la conjunció
-- Si tenim com a hipòtesis P∧Q, podem deduïr P amb la comanda .left
theorem T4 (h : P∧Q) : P := by
  exact h.left
-- Si tenim com a hipòtesis P∧Q, podem deduïr Q amb la comanda .right
theorem T5 (h : P∧Q) : Q := by
  exact h.right

-- ////////////////////////////////////
-- Introducció de la disjunció
-- Si tenim com a hipòtesi P, podem deduïr P∨Q amb la comanda Or.inl
theorem T6 (h : P) : P∨Q := by
  exact Or.inl h
-- Si tenim com a hipòtesi Q, podem deduïr P∨Q amb la comanda Or.inr
theorem T7 (h : Q) : P∨Q := by
  exact Or.inr h

-- Eliminació de la disjunció
-- Si tenim com a hipòtesi P∨Q i que P→R i Q→R, podem concloure R 
-- En aquest cas farem una demostració per casos
theorem T8 (h1 : P∨Q) (h2: P→R) (h3: Q→R) : R := by
  cases h1 with 
  | inl hP => exact h2 hP
  | inr hQ => exact h3 hQ

-- ////////////////////////////////////
-- ¬P és una abreviatura de P→False, per tant s'introdueix i s'elimina com una implicació
-- Introducció de la negació
-- Si tenim com a hipòtesi False, aleshores podem concloure ¬P   
theorem T9 (h1 : False) : ¬P := by 
  intro h2 
  exact h1

-- Eliminació de la negació
-- Si tenim ¬P i P, aleshores podem concloure False
theorem T10 (h1 : ¬P) (h2 : P) : False := by
  exact h1 h2

-- ////////////////////////////////////
-- P↔Q és una abreviatura de (P→Q)∧(Q→P) , per tant s'introdueix i s'elimina com una conjunció
-- Introducció de la doble implicació
-- Si tenim com a hipòtesi P→Q i Q→P, podem concloure P↔Q
theorem T11 (h1 : P→Q) (h2 : Q→P) : P↔Q := by
  exact Iff.intro h1 h2 

-- Eliminació de la doble implicació
-- Si tenim com a hipòtesi P↔Q, podem concloure P→Q (.mp Modus Ponens)
theorem T12 (h : P↔Q) : P→Q := by
  exact h.mp
-- Si tenim com a hipòtesi P↔Q, podem concloure Q→P (.mpr Modus Ponens reversed)
theorem T13 (h : P↔Q) : Q→P := by
exact h.mpr 

-- ////////////////////////////////////
-- La Veritat
-- Sempre es pot introduïr, però no es pot eliminar
theorem T14 : True := by
  exact True.intro

-- ////////////////////////////////////
-- La Falsedat
-- Sempre es pot eliminar -deduïnt qualsevol proposició--, però no es pot introduïr
theorem T15 (h:False) : P := by
  exact False.elim h

end InOut

namespace Exercicis
-- Exercicis de Daniel Clemente 
-- https://www.danielclemente.com/
-- CA https://www.danielclemente.com/logica/dn.ca.pdf
-- ES https://www.danielclemente.com/logica/dn.pdf
-- EN https://www.danielclemente.com/logica/dn.en.pdf
-- EO https://www.danielclemente.com/logica/dn.eo.pdf

-- 5.1 Un molt senzill
theorem T51 (P Q : Prop) (h1: P) (h2: P → Q) : P ∧ Q := by
  sorry

-- 5.2 Una mica més complicat
theorem T52 (P Q R : Prop) (h1: P ∧ Q → R) (h2: Q → P) (h3: Q) : R := by
  sorry

-- 5.3 Començant a suposar coses
theorem T53 (P Q R : Prop) (h1: P → Q) (h2: Q → R) : P → (Q ∧ R) := by
  sorry

-- 5.4 Usant la iteració
theorem T54 (P Q : Prop) (h1 : P) : Q → P := by
  sorry

-- 5.5 Reducció a l'absurd
theorem T55 (P Q : Prop) (h1 : P → Q) (h2: ¬Q) : ¬P := by
  sorry

-- 5.6 Amb subdemostracions
theorem T56 (P Q R : Prop) (h1: P → (Q → R)) : Q → (P → R) := by
  sorry

-- 5.7 Un de prova per casos
theorem T57 (P Q R : Prop) (h1: P ∨ (Q ∧ R)) : P ∨ Q := by
  sorry

-- 5.8 Un per pensar-hi
theorem T58 (L M P I : Prop) (h1: (L ∧ M) → ¬P)  (h2: I → P) (h3: M) (h4: I) : ¬L := by
  sorry

-- 5.9 La part esquerra buida
theorem T59 (P: Prop) : P → P := by
  sorry

-- 5.10 Suposar el contrari
theorem T510 (P: Prop) : ¬ (P ∧ ¬P) := by
  sorry

-- 5.11 Aquest sembla fàcil
theorem T511 (P: Prop) : P ∨ ¬P := by
  sorry

-- 5.12 Un d'interessant
theorem T512 (P Q : Prop) (h1: P ∨ Q) (h2: ¬P) : Q := by
  sorry

-- 5.13 Aquest me'l van posar a un examen
theorem T513 (A B C D : Prop) (h1: A ∨ B) (h2: A → C) (h3: ¬D → ¬B) : C ∨ D := by
  sorry

-- 5.14 Un "curt"
theorem T514 (A B: Prop) (h1: A ↔ B) : (A ∧ B) ∨ (¬A ∧ ¬B) := by
  sorry

end Exercicis

namespace Classical
-- ////////////////////////////////////
-- Si heu intentat resoldre els anteriors exercicis amb el que sabíeu, 
-- segurament vos trobeu el problema d'intentar donar una solució per a 
-- expressions del tipus P ∨ ¬ P o P ↔ (¬ (¬ P)). Açò és perquè 
-- les regles d'introducció i eliminació anteriors són regles 
-- constructives, mentre que les que anteriors són clàssiques o booleanes
-- Per a poder-les emprar, cal importar la llibreria clàssica

open Classical

-- Terç Exclós
-- Podeu emprar la comanda em (excludded middle) per a derivar P ∨ ¬ P 
#check em

theorem TE (P : Prop) : P ∨ ¬P := by 
  exact em P

-- Doble negació
theorem DN (P : Prop) : ¬¬P → P := by 
  intro h 
  cases (em P) with 
  | inl hP => exact hP
  | inr hNP => exact False.elim (h hNP)

-- Doble negació per reducció a l'absurd
#check byContradiction 
theorem DN2 (P : Prop) : ¬¬P → P := by 
  intro h 
  have hF : ¬ P → False := by
    intro hNP 
    exact h hNP 
  apply byContradiction hF 

-- Si voleu aprendre més sobre la diferència entre lògica clàssica 
-- i lògica contructivista podeu llegir l'article 
-- Five stages of accepting constructive mathematics, d'Andrej Bauer
-- https://www.ams.org/journals/bull/2017-54-03/S0273-0979-2016-01556-4/S0273-0979-2016-01556-4.pdf
end Classical