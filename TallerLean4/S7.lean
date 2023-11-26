-- Sessió 7 - 20/11/23
-- Operadors Clausura

import TallerLean4.S6

-- Recordem algunes definicions bàsiques
-- Relació reflexiva
def reflexiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x : X), R x x

-- Relació antisimètrica
def antisimetrica {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y : X), (R x y) ∧ (R y x) → x = y

-- Relació simètrica
def simetrica {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y : X), (R x y) → (R y x)

-- Relació transitiva
def transitiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x y z : X), (R x y) ∧ (R y z) → (R x z)

-- Un ordre és una relació reflexiva, antisimètrica i transitiva
def ordre {X : Type} (R : X → X → Prop) : Prop :=
  reflexiva R ∧ antisimetrica R ∧ transitiva R

-- Una relació d'equivalència és una relació reflexiva, simètrica i transitiva
def equivalencia {X : Type} (R : X → X → Prop) : Prop :=
  reflexiva R ∧ simetrica R ∧ transitiva R

-- Recordem la definició de la relació diagonal
def diag (X : Type) : X → X → Prop := by
  intro x y
  exact x = y

-- Definim operacions bàsiques sobre les relacions
-- Definim la composició de dues relacions
def comp {X : Type} (R S : X → X → Prop) : X → X → Prop := by
  intro x z
  exact ∃(y : X), (R x y) ∧ (S y z)

-- Definim la inversa d'una relació
def inv {X : Type} (R : X → X → Prop) : X → X → Prop := by
  intro x y
  exact R y x

-- Definim la unió de dues relacions
def unio {X : Type} (R S : X → X → Prop) : X → X → Prop := by
  intro x y
  exact (R x y) ∨ (S x y)

-- Definim la intersecció de dues relacions
def interseccio {X : Type} (R S : X → X → Prop) : X → X → Prop := by
  intro x y
  exact (R x y) ∧ (S x y)

-- Definim la relació d'inclusió entre dues relacions
def subseteq {X : Type} (R S : X → X → Prop) : Prop := by
  exact ∀(x y : X), R x y → S x y

-- Emprarem notació per a la composició de dues aplicacions
notation : 65 lhs:65 " · " rhs:66 => comp lhs rhs
-- Emprarem notació per a la unió de dues aplicacions
notation : 65 lhs:65 " ∪ " rhs:66 => unio lhs rhs
-- Emprarem notació per a la intersecció de dues aplicacions
notation : 65 lhs:65 " ∩ " rhs:66 => interseccio lhs rhs
-- Emprarem notació per a la relació d'inclusió entre dues aplicacions
notation : 65 lhs:65 " ⊆ " rhs:66 => subseteq lhs rhs

namespace PropietatsRelacions
-- Comprovem algunes propietats bàsiques de les operacions sobre relacions que acabem de vore
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

-- La relació diagonal és una relació d'equivalència
theorem TDiagEqv {X : Type} : equivalencia (diag X) := by
  rw [equivalencia]
  apply And.intro
  -- La relació diagonal és reflexiva
  rw [reflexiva]
  intro x
  rw [diag]
  --
  apply And.intro
  -- La relació diagonal és simètrica
  rw [simetrica]
  intro x y
  intro h1
  exact h1.symm
  -- La relació diagonal és transitiva
  rw [transitiva]
  intro x y z
  intro ⟨h1, h2⟩
  rw [diag] at h1 h2
  rw [diag]
  exact h1.trans h2

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

-- Una relació és reflexiva si, i només si, conté a la diagonal
theorem TCRfl {X : Type} (R : X → X → Prop) : reflexiva R ↔ diag X ⊆ R := by
  sorry

-- Una relació és simètrica si, i només si, conté a la seua inversa
theorem TCSim {X : Type} (R : X → X → Prop) : simetrica R ↔ inv R ⊆ R := by
  sorry

-- Una relació és transitiva si, i només si, conté al seu quadrat
theorem TCTrans {X : Type} (R : X → X → Prop) : transitiva R ↔ R·R ⊆ R := by
  sorry

end PropietatsRelacions

namespace ClRT
-- Anem a definir la clausura reflexivo-transitiva d'una relació
-- Importem N
open N

-- Definim l'iterat a esquerra d'una relació de forma recursiva
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

-- La clausura reflexivo-transitiva d'una relació conté a la relació
theorem TCrtBase {X : Type} (R : X → X → Prop) : R ⊆ crt R := by
  intro x y
  intro h1
  use (s z)
  apply Or.inr
  use x
  apply And.intro
  exact rfl
  exact h1

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

-- Aquesta nova relació és la mínima que conté a R, és reflexiva i transitiva
theorem TCrtMin {X : Type} (R S: X → X → Prop) (h1: R ⊆ S) (h2: reflexiva S) (h3: transitiva S) : (crt R) ⊆ S := by
  intro x y
  intro h4
  have h5 : ∀ (n:N), it R n x y → S x y := by
    intro n
    intro h5
    -- Per inducció sobre n
    --------------
    -- Cas base
    have hCB (h6: it R z x y) : S x y := by
      sorry
    ---------------
    -- Pas inductiu
    have hInd (k : N) (h6: it R k x y → S x y) (h7: it R (s k) x y) : S x y := by
      sorry
    -- Ara fem l'inducció
    induction n with
    | z => exact hCB h5
    | s n hi => exact hInd n hi h5
  apply Exists.elim h4
  intro n
  exact h5 n

-- Anem a emprar una forma més abstracta de definir
-- la clausura reflexivo-transitiva d'una relació
inductive ClRT {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base : ∀ (x y: X), R x y → ClRT R x y
  | rfl : ∀(x:X), ClRT R x x
  | trans : ∀(x y z: X), ClRT R x y →  ClRT R y z → ClRT R x z

  -- Aquesta nova relació conté a R
  theorem TClRTbase {X : Type} (R : X → X → Prop) : R ⊆ ClRT R := by
    intro x y
    intro h1
    exact ClRT.base x y h1

  -- Aquesta nova relació és reflexiva
  theorem TClRTrfl {X : Type} (R : X → X → Prop) : reflexiva (ClRT R) := by
    rw [reflexiva]
    intro x
    exact ClRT.rfl x

  -- Aquesta nova relació és transitiva
  theorem TClRTtrans {X : Type} (R : X → X → Prop) : transitiva (ClRT R) := by
    rw [transitiva]
    intro x y z
    intro ⟨h1, h2⟩
    exact ClRT.trans x y z h1 h2

  -- Aquesta nova relació és la mínima que conté a R, és reflexiva i transitiva
  theorem TClRMin {X : Type} (R S: X → X → Prop) (h1: R ⊆ S) (h2: reflexiva S) (h3: transitiva S) : (ClRT R) ⊆ S := by
    intro x y
    intro h4
    induction h4 with
    | base a b h4 => exact h1 a b h4
    | rfl z => exact h2 z
    | trans a b c h4 h5 h6 h7 => exact h3 a b c (And.intro h6 h7)

-- Per tant, ClRT R ⊆ Crt R
theorem TClRTincCrt {X : Type} (R : X → X → Prop) : ClRT R ⊆ crt R := by
  apply TClRMin
  exact TCrtBase R
  exact TCrtRfl R
  exact TCrtTrans R

-- Per tant, crt R ⊆ ClRT R
theorem TCrtincClRT {X : Type} (R : X → X → Prop) : crt R ⊆ ClRT R := by
  apply TCrtMin
  exact TClRTbase R
  exact TClRTrfl R
  exact TClRTtrans R

-- Aleshores les dues definicions coincideixen
theorem TClRT {X : Type} (R : X → X → Prop) : ClRT R = crt R := by
  funext x y
  apply propext
  apply Iff.intro
  exact TClRTincCrt R x y
  exact TCrtincClRT R x y

end ClRT

namespace Eqvgen
-- Anem a definir la mínima relació d'equivalència que conté una relació donada
-- Farem com abans, donarem dues formes equivalents de construïr aquest operador

-- Importem N
open N

-- Definim l'iterat d'una relació de forma recursiva
def it {X : Type} (R : X → X → Prop) : N → (X → X → Prop) := by
  intro n
  cases n with
  | z => exact diag X
  | s n => exact (it R n) ∪ (inv (it R n)) ∪ ((it R n)·R)

-- Definim la unió de tots els iterats, està serà la
-- mínima relació d'equivalència que conté una relació donada
def eqvgen {X : Type} (R : X → X → Prop) : X → X → Prop := by
  intro x y
  exact ∃ (n : N), it R n x y

-- eqvgen R conté a R
theorem TEqvgenBase {X : Type} (R : X → X → Prop) : R ⊆ eqvgen R := by
  sorry

-- eqvgen R és reflexiva
theorem TEqvgenRfl {X : Type} (R : X → X → Prop) : reflexiva (eqvgen R) := by
  sorry

-- eqvgen R és simètrica
theorem TEqvgenSim {X : Type} (R : X → X → Prop) : simetrica (eqvgen R) := by
  sorry

-- eqvgen R és transitiva
theorem TEqvgenTrans {X : Type} (R : X → X → Prop) : transitiva (eqvgen R) := by
  sorry

-- Per tant, eqvgen R és una relació d'equivalència
theorem TEqvgenEqv {X : Type} (R : X → X → Prop) : equivalencia (eqvgen R) := by
  sorry

-- evgen R és la mínima relació d'equivalència que conté a R
theorem TEqvgenmin {X : Type} (R S: X → X → Prop) (h1: R ⊆ S) (h2: equivalencia S) : (eqvgen R) ⊆ S := by
  sorry

-- Anem a emprar una forma més abstracta de definir
-- La mínima relació d'equivalència que conté una relació donadad
inductive Eqvgen {X : Type} (R : X → X → Prop) : X → X → Prop where
  | base : ∀ (x y: X), R x y → Eqvgen R x y
  | rfl : ∀(x:X), Eqvgen R x x
  | sim : ∀(x y:X), Eqvgen R x y → Eqvgen R y x
  | trans : ∀(x y z: X), Eqvgen R x y →  Eqvgen R y z → Eqvgen R x z

-- Aleshores les dues definicions coincideixen
theorem TEqvgen {X : Type} (R : X → X → Prop) : Eqvgen R = eqvgen R := by
  sorry

end Eqvgen


namespace OpCl
-- Operadors clausura
-- Un operador és una endoaplicació de relacions sobre un tipus X
-- És a dir, un objecte del tipus (X → X → Prop) → (X → X → Prop)

-- Direm que un operador és extensiu si
def extensiu {X : Type} (Op : (X → X → Prop) → (X → X → Prop)) : Prop :=
  ∀(R : X → X → Prop), R ⊆ Op R

-- Direm que un operador és monòton si
def monoton {X : Type} (Op : (X → X → Prop) → (X → X → Prop)) : Prop :=
  ∀(R S: X → X → Prop), R ⊆ S → Op R ⊆ Op S

-- Direm que un operador és idempotent si
def idempotent {X : Type} (Op : (X → X → Prop) → (X → X → Prop)) : Prop :=
  ∀(R : X → X → Prop), Op (Op R) ⊆ Op R

-- Finalment, direm que un operador és de clausura si
def Operadorclausura {X : Type} (Op : (X → X → Prop) → (X → X → Prop)) : Prop :=
  extensiu Op ∧ monoton Op ∧ idempotent Op

-- Els operadors que hem definit abans són de clausura
------------------------------
-- Obrim ClRT
open ClRT

-- Definim l'operador associat a la clausura reflexivo-transitiva
def ClRTOp (X : Type) : (X → X → Prop) → X → X → Prop := by
  intro R
  exact ClRT R

-- L'operador clausura reflexivo-transitiva és un operador de clausura
theorem TClRTCl {X : Type} : Operadorclausura (ClRTOp X) := by
  sorry

------------------------------
-- Obrim Eqvgen
open Eqvgen

-- Definim l'operador associat a la relació d'equivalència generada
def EqvgenOp (X : Type) : (X → X → Prop) → X → X → Prop := by
  intro R
  exact Eqvgen R

-- L'operador equivalència generada és un operador de clausura
theorem TEqvgenCl {X : Type} : Operadorclausura (EqvgenOp X) := by
  sorry

end OpCl
