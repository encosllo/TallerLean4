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
theorem LCrtTrans3 {X : Type} (R : X → X → Prop) (n m: N) (x1 x2 x3 : X) (h1 : it R n x1 x2) (h2 : it R m x2 x3) : it R (n + m) x1 x3 := by
  -- Per inducció sobre m
  --------------
  -- Cas base
  have hCB (h2 : it R z x2 x3) : it R (n + z) x1 x3 := by
    have h3 : n + z = n := by exact TSuma0ND n
    rw [h3]
    have h4 : x2 = x3 := by exact h2
    rw [h4] at h1
    exact h1
  ---------------
  -- Pas inductiu
  have hInd (k : N) (h2 : it R (s k) x2 x3) (hi : it R k x2 x3 → it R (n + k) x1 x3) : it R (n + s k) x1 x3 := by
    have h3 : n + s k = s (n + k) := by
      calc
        n + s k = s n + k := by exact (TSumUn n k).symm
        _ = s (n + k) := by exact rfl
    rw [h3]
    have h4 : ((it R k) ∪ ((it R k)·R)) x2 x3 := by exact h2
    rw [unio] at h4
    -- Per cassos sobre h4
    -- El primer cas, en que it R k x2 x3, és senzill
    have h5 (h4L : it R k x2 x3) : it R (s (n + k)) x1 x3 := by
      have h6 : it R (n + k) x1 x3 := by exact hi h4L
      -- Emprem el Lema1
      apply LCrtTrans1
      exact h6
    -- Importa el segon cas
    have h6 (h4R : ((it R k)·R) x2 x3) : it R (s (n + k)) x1 x3 := by
      rw [comp] at h4R
      apply Exists.elim h4R
      intro x4
      intro ⟨h4R1, h4R2⟩

      sorry
    cases h4 with
    | inl h4L => exact h5 h4L
    | inr h4R => exact h6 h4R
  induction m with
  | z => exact hCB h2
  | s m hi => exact hInd m h2 hi

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
  have h5 : it R (n + m) x1 x3 := by
    exact LCrtTrans3 R n m x1 x2 x3 h4 h3
  use n+m

-- Anem a emprar una forma més abstracta de definir
-- la clausura reflexivo-transitiva d'una relació
inductive ClRT {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base : ∀ (x y: X), R x y → ClRT R x y
  | rfl : ∀(x:X), ClRT R x x
  | trans : ∀(x y z: X), ClRT R x y →  ClRT R y z → ClRT R x z


end Cltrans
