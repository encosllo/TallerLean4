-- Sessió 2 - 16/10/23
-- Treballem amb quantificadors

-- L'objectiu d'aquesta sessió és introduïr els quantificadors
-- universal i existencial i treballar amb ells
-- Seguirem
-- https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html

import Paperproof

namespace Peratot
-- En aquest espai introduïm el quantificador universal
-- Vorem com introduïr-lo i eliminar-lo
-- Ω (\Omega) és un tipus que farà de contenidor
variable (Ω : Type)
-- P serà una proposició sobre Ω
variable (P : Ω → Prop)

-- El quantificador universal ∀ (\forall)
-- S'empra especificant el domini en el què s'estableix el quantificador
#check ∀ (x : Ω), P x

-- ////////////////////////////////////
-- Introducció del quantificador universal
-- Per a introduïr un quantificador universal introduïm una variable x del
-- tipus sobre el què quantifiquem i provem de demostrar que P x és cert
theorem T1 : ∀ (x:Ω), P x := by
  intro x
  sorry

-- ////////////////////////////////////
-- Eliminació del quantificador universal
-- Per a eliminar un quantificador universal simplement l'apliquem
-- sobre una variable del tipus sobre el què quantifiquem
theorem T2 (h : ∀(x:Ω), P x) (y : Ω) : P y := by
  exact h y

end Peratot

namespace Existeix
-- En aquest espai introduïm el quantificador existencial
-- Vorem com introduïr-lo i eliminar-lo
-- Ω (\Omega) és un tipus que farà de contenidor
variable (Ω : Type)
-- P serà una proposició sobre Ω
variable (P : Ω → Prop)
-- Q serà una proposició
variable (Q : Prop)

-- El quantificador existencial ∃ (\exists)
-- S'empra especificant el domini en el què s'estableix el quantificador
#check ∃ (x : Ω), P x

-- ////////////////////////////////////
-- Introducció del quantificador existencial
-- Per a introduïr un quantificador existencial cal demostrar que algun P x és cert
theorem T1  (y : Ω) (h: P y) : ∃ (x:Ω), P x := by
  exact Exists.intro y h

-- ////////////////////////////////////
-- Eliminació del quantificador existencial
-- Per a eliminar un quantificador existencial simplement
theorem T2 (h1 : ∃(x:Ω), P x) (h2 : ∀ (x:Ω), P x → Q) : Q := by
  apply Exists.elim h1
  exact h2

end Existeix

namespace ExS2
open Classical
-- Ω és un tipus que farà de contenidor
variable (Ω : Type)
-- x, y i z seran variables de tipus Ω
variable (x y z : Ω)
-- P i Q seran proposicions sobre Ω
variable (P Q : Ω → Prop)
-- R serà una proposició
variable (R : Prop)

-- Les següents proposicions venen de
-- https://github.com/leanprover/tutorial/blob/master/04_Quantifiers_and_Equality.org

theorem E1 : (∃ (x : Ω), R) → R :=  by
  sorry

theorem E2 (x : Ω) : R → (∃ (x : Ω), R) := by
  sorry

theorem E3 : (∃ (x : Ω), P x ∧ R) ↔ (∃ (x : Ω), P x) ∧ R := by
  sorry

theorem E4 : (∃ (x : Ω), P x ∨ Q x) ↔ (∃ (x : Ω), P x) ∨ (∃ (x : Ω), Q x) := by
  sorry

theorem E5 : (∀ (x : Ω), P x) ↔ ¬ (∃ (x : Ω), ¬ P x) := by
  sorry

theorem E6 : (∃ (x : Ω), P x) ↔ ¬ (∀ (x : Ω), ¬ P x) := by
  sorry

theorem E7 : (¬ ∃ (x : Ω), P x) ↔ (∀ (x : Ω), ¬ P x) := by
  sorry

theorem E8 : (¬ ∀ (x : Ω), P x) ↔ (∃ (x : Ω), ¬ P x) := by
  sorry

theorem E9 : (∀ (x : Ω), P x → R) ↔ (∃ (x : Ω), P x) → R := by
  sorry

theorem E10 (x : Ω) : (∃ (x : Ω), P x → R) ↔ (∀ (x : Ω), P x) → R := by
  sorry

theorem E11 (x : Ω) : (∃ (x : Ω), R  →  P x) ↔ (R → ∃ (x : Ω), P x) := by
  sorry

end ExS2
