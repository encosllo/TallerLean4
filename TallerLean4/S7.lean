-- Sessió 7 - 20/11/23
-- Definim l'ordre sobre els naturals

import TallerLean4.S6

-- Recordem que un ordre és una relació reflexiva,
-- antisimètrica i transitiva
def reflexiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x : X), R x x

def antisimetrica {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y : X), (R x y) ∧ (R y x) → x = y

def transitiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y z : X), (R x y) ∧ (R y z) → (R x z)

def ordre {X : Type} (R : X → X → Prop) : Prop :=
  reflexiva R ∧ antisimetrica R ∧ transitiva R

-- Recordem la definició de la relació diagonal
def diag (X : Type) : X → X → Prop := by
  intro x y
  exact x = y

-- La relació diagonal és una relació d'ordre
theorem TDiagOrd {X : Type} : ordre (diag X) := by
  rw [ordre]
  apply And.intro
  -- La relació diagonal és reflexiva
  rw [reflexiva]
  intro x
  rw [diag]
  --
  apply And.intro
  -- La relació diagonal és antisimètrica
  rw [antisimetrica]
  intro x y
  intro ⟨h1, h2⟩
  exact h1
  -- La relació diagonal és transitiva
  rw [transitiva]
  intro x y z
  intro ⟨h1, h2⟩
  rw [diag] at h1 h2
  rw [diag]
  exact h1.trans h2

namespace Cltrans
-- Anem a definir la clausura transitiva d'una relació
-- Definim la composició de dues relacions
def comp {X : Type} (R S : X → X → Prop) : X → X → Prop := by
  intro x z
  exact ∃(y : X), (R x y) ∧ (S y z)

-- Definim la unió de dues relacions
def unio {X : Type} (R S : X → X → Prop) : X → X → Prop := by
  intro x y
  exact (R x y) ∨ (S x y)

-- Definim la relació d'inclusió entre dues relacions
def subseteq {X : Type} (R S : X → X → Prop) : Prop := by
  exact ∀(x y : X), R x y → S x y

-- Emprarem notació per a la composició de dues aplicacions
notation : 65 lhs:65 " · " rhs:66 => comp lhs rhs
-- Emprarem notació per a la unió de dues aplicacions
notation : 65 lhs:65 " ∪ " rhs:66 => unio lhs rhs
-- Emprarem notació per a la relació d'inclusió entre dues aplicacions
notation : 65 lhs:65 " ⊆ " rhs:66 => subseteq lhs rhs

-- La relació diagonal és neutre per a la composició a esquerra
theorem TDiagNCompE {X : Type} (R : X → X → Prop) : R · (diag X) = R := by
  funext x y
  apply propext
  apply Iff.intro
  -- Esquerra a dreta
  intro h1
  rw [comp] at h1
  apply Exists.elim h1
  intro z
  intro ⟨h2, h3⟩
  rw [diag] at h3
  rw [h3] at h2
  exact h2
  -- Dreta a esquerra
  intro h1
  apply Exists.intro y
  apply And.intro
  exact h1
  rw [diag]

-- La relació diagonal és neutre per a la composició a dreta
theorem TDiagNCompD {X : Type} (R : X → X → Prop) : (diag X) · R = R := by
  sorry

-- Importem N
open N

-- Definim l'iterat d'una relació de forma recursiva
def it {X : Type} (R : X → X → Prop) : N → (X → X → Prop) := by
  intro n
  cases n with
  | z => exact diag X
  | s n => exact (it R n) ∪ (it R n)·R

-- Definim la unió de tots els iterats
def crt {X : Type} (R : X → X → Prop) : X → X → Prop := by
  intro x y
  exact ∃ (n : N), it R n x y






end Cltrans
