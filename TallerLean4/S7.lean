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
  | s n => exact (it R n) ∪ ((it R n)·R)

-- Definim la unió de tots els iterats, està serà la
-- clausura reflexivo-transitiva d'una relació
def crt {X : Type} (R : X → X → Prop) : X → X → Prop := by
  intro x y
  exact ∃ (n : N), it R n x y

-- La clausura reflexivo-transitiva d'una relació és
-- una relació reflexiva
theorem TCrtRfl {X : Type} (R : X → X → Prop) : reflexiva (crt R) := by
  rw [reflexiva]
  intro x
  rw [crt]
  use z
  exact rfl

-- Per a demostrar que la clausura reflexivo-transitiva d'una relació
-- és una relació transitiva, farem uns lemes previs
-- Lemma 1
theorem LCrtTrans1 {X : Type} (R : X → X → Prop) (n : N) (x y : X) (h1 : it R n x y) : it R (s n) x y := by
  have h2 : ((it R n) ∪ ((it R n)· R )) x y := by
    rw [unio]
    exact Or.inl h1
  exact h2

-- Importem els resultats sobre la suma
open Suma

-- Lema 2
theorem LCrtTrans2 {X : Type} (R : X → X → Prop) (n m : N) (x y : X) (h1 : it R n x y) : it R (n + m) x y := by
  --------------
   -- Cas base
  have hCB : it R (n + z) x y := by
    have h2 : n + z = n := by exact TSuma0ND n
    have h3 : it R n = it R (n + z) := by exact congrArg (it R) (id h2.symm)
    rw [h3] at h1
    exact h1
  ---------------
  -- Pas inductiu
  have hInd (k : N) (hi: it R (n + k) x y) : it R (n + s k) x y := by
    have h2 : n + (s k) = s (n + k) := by
      calc
        n + (s k) = (s n) + k := by exact (TSumUn n k).symm
        _ = s (n + k) := by exact rfl
    rw [h2]
    apply LCrtTrans1
    exact hi
  induction m with
  | z => exact hCB
  | s m hi => exact hInd m hi

-- Lema 3
theorem LCrtTrans3 {X : Type} (R : X → X → Prop) (n : N) (x1 x2 x3 : X) (h1 : it R n x1 x2) (h2 : it R n x2 x3) : it R ( (s n) ) x1 x3 := by
  sorry
  --- Per inducció sobre n

-- Lema 4
theorem LCrtTrans4 {X : Type} (R : X → X → Prop) (n m : N) (x1 x2 x3 : X) (h1 : it R n x1 x2) (h2 : it R m x2 x3) : it R ( (s n) + m) x1 x3 := by
  -- Apliquem el Lema LCrtTrans2 dues voltes
  have h3 : it R (n + m) x1 x2 := by exact LCrtTrans2 R n m x1 x2 h1
  have h4 : it R (n + m) x2 x3 := by
    have h5 : n + m = m + n := by exact TSumaComm n m
    rw [h5]
    exact LCrtTrans2 R m n x2 x3 h2
  -- Apliquem el Lema LCrtTrans3
  apply LCrtTrans3 R (n + m) x1 x2 x3 h3 h4

-- La clausura reflexivo-transitiva d'una relació és
-- una relació transitiva
theorem TCrtTrans {X : Type} (R : X → X → Prop) : transitiva (crt R) := by
  rw [transitiva]
  intro x1 x2 x3
  intro ⟨h1 ,h2⟩
  rw [crt] at h1 h2
  apply Exists.elim h1
  intro n
  apply Exists.elim h2
  intro m
  intro h3 h4
  -- Comencem la demostració per inducció sobre n
  --------------
  -- Cas base
  have hCB (h5 : it R N.z x1 x2) : crt R x1 x3 := by
    have h6 : x1 = x2 := by exact h5
    have h7 : it R m x1 x3 := by
      rw [h6.symm] at h3
      exact h3
    rw [crt]
    use m
  ---------------
  -- Pas inductiu
  have hInd (k : N) (hi : it R k x1 x2 → crt R x1 x3) : it R (s k) x1 x2 → crt R x1 x3 := by
    intro h5
    ----- Ací Lema
    sorry
  induction n with
  | z => exact hCB h4
  | s n hi => exact (hInd n) hi h4



end Cltrans
