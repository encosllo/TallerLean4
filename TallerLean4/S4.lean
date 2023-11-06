-- Sessió 4 - 30/10/23
-- Treballem amb subtipus i tipus quocients
-- L'objectiu d'aquesta sessió és introduïr els subtipus i els tipus quocients

import Paperproof
import Mathlib.data.setoid.basic
import TallerLean4.S3

namespace Subtipus
-- Ω (\Omega) és un tipus que farà de contenidor
variable (Ω : Type)
-- P serà una proposició sobre Ω
variable (P : Ω → Prop)
-- Amb aquesta informació som capaços d'obtindre el subtipus P
#check Subtype P
#print Subtype

-- Una notació alternativa per a este concepte és
def ΩP : Type := { ω : Ω // P ω }

-- Donar un element del Subtipus P és equivalent a donar un element ω de tipus Ω i una demostració de P ω
theorem TSub.mk {Ω : Type} {P : Ω → Prop} (ω : Ω) (h : P ω) : Subtype P := by
  exact Subtype.mk ω h

theorem TSub.val {Ω : Type} {P : Ω → Prop} (ω : Subtype P) : Ω := by
  exact ω.val

theorem TSub.prop {Ω : Type} {P : Ω → Prop} (ω : Subtype P) : P ω := by
  exact ω.property

theorem TSubEqEl {Ω : Type} {P : Ω → Prop} (ω_1 ω_2 : Subtype P) (h : ω_1.val = ω_2.val) : ω_1 = ω_2 := by
  exact Subtype.eq h

-- Si dues proposicions són equivalents, aleshores els subtipus associats són iguals
theorem TSubEq {Ω : Type} (P Q : Ω → Prop) (h1 : ∀(ω : Ω), P ω ↔ Q ω) : Subtype P = Subtype Q := by
  have h2 : P = Q := by
    funext ω
    specialize h1 ω
    rewrite [h1]
    rfl
  rw [h2]

-- Si la propietat que defineix un subtipus implica una altra, podem moure'ns de subtipus
def incl {Ω : Type} (P Q: Ω → Prop) (h1 : ∀(ω : Ω), P ω → Q ω) : Subtype P → Subtype Q := by
  intro ω
  specialize h1 ω.val
  have h2: Q ω.val := by exact h1 ω.property
  exact Subtype.mk ω.val h2

-- Per a cada subtipus podem considerar l'aplicació inclusió
def inc {Ω : Type} (P : Ω → Prop) : Subtype P → Ω := by
  intro ω
  exact ω.val

-- Podem restringir aplicacions a subtipus
def rest {Ω Γ : Type} {P : Ω → Prop} : (Ω → Γ) → (Subtype P → Γ) := by
  intro f
  intro ω
  exact f ω.val

-- Podem definir el subtipus imatge
def Im {Ω Γ : Type} (f : Ω → Γ) : Type := { γ : Γ // ∃ (ω : Ω), f ω = γ}

-- Propietat Universal dels Subtipus
-- Im (inc) = Subtype
theorem PUSub {Ω : Type} {P : Ω → Prop} : Im (inc P) = Subtype P := by
  apply TSubEq
  intro ω
  apply Iff.intro
  -- Cas 1
  intro h1
  apply Exists.elim h1
  intro x
  intro h2
  rw [h2.symm]
  rw [inc]
  exact x.property
  -- Cas 2
  intro h2
  apply Exists.intro (Subtype.mk ω h2)
  rw [inc]

-- Existència de la correstricció
def corest {Δ Ω : Type} {P : Ω → Prop} (f : Δ → Ω) (h : ∀(δ:Δ), P (f δ)) : Δ → Subtype P := by
  intro δ
  specialize h δ
  exact Subtype.mk (f δ) h

-- Propietat universal de la correstricció
-- Existència
theorem TUSub {Δ Ω : Type} {P : Ω → Prop} (f : Δ → Ω) (h : ∀(δ:Δ), P (f δ)) : f = inc P ∘ (corest f h) := by
  rfl

-- Unicitat
theorem TUSubUni {Δ Ω : Type} {P : Ω → Prop} (f : Δ → Ω) (g : Δ → Subtype P) (h : ∀(δ:Δ), P (f δ)) (h1 : f = inc P ∘ g) : (corest f h) = g := by
  funext δ
  exact Subtype.eq (congrFun h1 δ)

end Subtipus

namespace Quocient
-- https://leanprover-community.github.io/mathlib_docs/data/setoid/basic.html

-- Ω (\Omega) és un tipus que farà de contenidor
variable (Ω : Type)
-- R serà una relació sobre Ω
variable (R : Ω → Ω → Prop)
-- Donats dos elements de tipus Ω
variable (ω1 ω2 : Ω)
-- Direm que estan R-relacionats si tenim R ω1 ω2
#check R ω1 ω2

-- Una relació R s'anomena reflexiva si ∀(ω : Ω), R ω ω
def reflexiva {Ω : Type} (R: Ω → Ω → Prop) : Prop :=  ∀(ω : Ω), R ω ω
-- Una relació R s'anomena simètrica si ∀(ω1 ω2 : Ω), R ω1 ω2 → R ω2 ω1
def simetrica {Ω : Type} (R: Ω → Ω → Prop) : Prop :=  ∀{ω1 ω2 : Ω}, R ω1 ω2 → R ω2 ω1
-- Una relació R s'anomena transitiva si ∀(ω1 ω2 ω3 : Ω), R ω1 ω2 ∧ R ω2 ω3 → R ω1 ω3
def transitiva {Ω : Type} (R: Ω → Ω → Prop) : Prop :=  ∀{ω1 ω2 ω3 : Ω}, R ω1 ω2 → R ω2 ω3 → R ω1 ω3
-- Una relació R s'anomena d'equivalència si R és reflexiva simètrica i transitiva
def equivalencia {Ω : Type} (R: Ω → Ω → Prop) : Prop := reflexiva R ∧ simetrica R ∧ transitiva R

-- La implementació en Lean de les relacions d'equivalència es fa amb la comanda Equivalence
#check Equivalence

theorem TEq {Ω : Type} (R: Ω → Ω → Prop) : equivalencia R ↔ Equivalence R := by
  apply Iff.intro
  -- Cas 1
  intro h
  rw [equivalencia] at h
  have h1 : reflexiva R := by
    exact h.left
  have h2 : simetrica R := by
    exact h.right.left
  have h3 : transitiva R := by
    exact h.right.right
  apply Equivalence.mk
  --
  rw [reflexiva] at h1
  exact h1
  --
  rw [simetrica] at h2
  exact h2
  --
  rw [transitiva] at h3
  exact h3
  -- Cas 2
  intro h
  rw [equivalencia]
  apply And.intro
  rw [reflexiva]
  exact Equivalence.refl h
  apply And.intro
  rw [simetrica]
  exact Equivalence.symm h
  rw [transitiva]
  exact Equivalence.trans h

-- Un setoid és un parell (Ω,R) on Ω és un tipus i R una relació d'equivalència sobre Ω
#check Setoid Ω
#print Setoid

-- D'un setoid podem obtindre la relació subjacent
def ps {Ω : Type} : Setoid Ω → (Ω → Ω → Prop) := by
  intro s
  exact Setoid.r

-- La relació subjacent d'un setoid és d'equivalència
theorem ts {Ω : Type} (s : Setoid Ω) : Equivalence s.r := by
  exact Setoid.iseqv

-- Per a donar un objecte de tipus Setoid Ω cal donar una relació d'equivalència en Ω
theorem tis {Ω : Type} {R : Ω → Ω → Prop} (h : Equivalence R) : Setoid Ω := by
  apply Setoid.mk R h

-- Considerem un setoid de tipus Ω
variable (s : Setoid Ω)
-- Aleshores podem considerar el tipus quocient associat
#check Quotient s

-- Dos setoids són iguals sii les relacions associades són iguals
theorem TEqSetoid {Ω : Type} {s t : Setoid Ω} : s=t ↔ s.r=t.r := by
  apply Iff.intro
  --
  intro h
  rw [h]
  --
  intro h
  have h1 : ∀ (ω1 ω2 : Ω), s.r ω1 ω2 ↔ t.r ω1 ω2 := by
    intro ω1 ω2
    rw [h]
  exact Setoid.ext h1

#print Setoid

-- Donat un objecte d'Ω podem considerar la seua classe
def pr {Ω : Type} (s : Setoid Ω) : Ω → Quotient s := by
  intro ω
  exact Quotient.mk s ω

-- Donada una classe podem considerar un representant
#check Quotient.out
#check Quotient.exists_rep
#check Exists.choose
noncomputable def rep {Ω : Type} {s : Setoid Ω} : Quotient s → Ω := by
  intro cω
  have h2 : ∃ (ω : Ω), Quotient.mk s ω = cω := by
    exact Quotient.exists_rep cω
  apply Exists.choose h2

-- La classe del representant és la classe original
#check Quotient.mk_out
theorem TRep {Ω : Type} {s : Setoid Ω} (cω : Quotient s) : pr s (rep cω) = cω := by
  apply Iff.mp Quotient.out_equiv_out
  rw [pr]
  exact Quotient.mk_out (rep cω)

-- Donat dos objectes d'Ω les seues classes són iguals si, i només si,
-- els objectes estan relacionats
theorem TQuotEq {Ω : Type} {s : Setoid Ω} (ω1 ω2 : Ω) : pr s ω1 = pr s ω2 ↔ s.r ω1 ω2 := by
  apply Iff.intro
  -- Cas 1
  intro h1
  rw [pr, pr] at h1
  apply Quotient.exact h1
  -- Cas 2
  intro h1
  rw [pr, pr]
  exact Quotient.sound h1

-- Podem astringir aplicacions a quocients
def ast {Ω Γ : Type} {s : Setoid Ω} : (Γ → Ω) → (Γ → Quotient s) := by
  intro f
  intro γ
  exact pr s (f γ)

-- Podem definir el nucli d'una aplicació
def Ker {Ω Γ : Type} (f : Ω → Γ) : Ω → Ω → Prop := by
  intro ω1 ω2
  exact f ω1 = f ω2

-- El nucli d'una aplicació és relació d'equivalència
theorem TKerEq {Ω Γ : Type} (f : Ω → Γ) : Equivalence (Ker f) := by
  apply Equivalence.mk
  -- Reflexiva
  intro ω
  exact rfl
  -- Simètrica
  intro ω1 ω2
  intro h
  exact h.symm
  -- Transitiva
  intro ω1 ω2 ω3
  intro h1 h2
  exact h1.trans h2

-- Definició del setoid (Ω, Ker f)
def SKer {Ω Γ : Type} (f : Ω → Γ) : Setoid Ω := by
  apply Setoid.mk
  exact TKerEq f

-- Definició del quocient Ω/Ker f
def QKer {Ω Γ : Type} (f : Ω → Γ) : Type := Quotient (SKer f)

-- Propietat Universal dels Quocients
-- Ker (pr θ) = θ
theorem TUKer {Ω : Type} {s : Setoid Ω} : SKer (pr s) = s := by
  have h1 : Ker (pr s) = s.r := by
    funext ω1 ω2
    calc
      Ker (pr s) ω1 ω2 = (pr s ω1 = pr s ω2)  := by exact rfl
      _                = s.r ω1 ω2            := by rw [TQuotEq ω1 ω2]
  rw [TEqSetoid]
  exact h1

-- Existència de la coastricció
#check Quotient.lift
def coast {Ω Γ : Type} {s : Setoid Ω} (f : Ω → Γ) (h : ∀(ω1 ω2 : Ω), s.r ω1 ω2 → Ker f ω1 ω2) : Quotient s → Γ := by
  intro cω
  apply Quotient.lift
  exact h
  exact cω

-- Propietat universal de la coastricció
-- Existència
theorem TUQuot {Ω Γ : Type} {s : Setoid Ω} (f : Ω → Γ) (h : ∀(ω1 ω2 : Ω), s.r ω1 ω2 → Ker f ω1 ω2) : f = (coast f h) ∘ (pr s) := by
  apply funext
  intro ω
  exact rfl

-- Unicitat
theorem TUQuotUni {Ω Γ : Type} {s : Setoid Ω} (f : Ω → Γ) (g : Quotient s → Γ) (h : ∀(ω1 ω2 : Ω), s.r ω1 ω2 → Ker f ω1 ω2) (h1 : f = g ∘ (pr s)) : coast f h = g := by
  funext cω
  calc
    coast f h cω    =   coast f h (pr s (rep cω))   := by exact congrArg (coast f h) (Eq.symm (TRep cω))
    _               =   (coast f h ∘ pr s) (rep cω) := by exact rfl
    _               =   f (rep cω)                  := by exact rfl
    _               =   (g ∘ pr s) (rep cω)         := by rw [h1.symm]
    _               =   g (pr s (rep cω))           := by exact rfl
    _               =   g cω                        := by exact congrArg g (TRep cω)

end Quocient

namespace ExS4
-- Recordem les següents definicions
-- Definició de l'aplicació identitat

-- Definició d'aplicació identiat
#check PropApl.idt
#print PropApl.idt

-- Definició d'aplicació injectiva
#check PropApl.Inj.injectiva
#print PropApl.Inj.injectiva
-- Definició d'aplicació sobrejectiva
#check PropApl.Sobre.sobrejectiva
#print PropApl.Sobre.sobrejectiva

-- Definició d'aplicació bijectiva
def bijectiva {X Y : Type} (f : X → Y) : Prop := PropApl.Inj.injectiva f ∧ PropApl.Sobre.sobrejectiva f

-- Definició de bijecció entre tipus
def Bijectius : Type → Type →  Prop := by
  intros X Y
  exact ∃ f : X → Y, bijectiva f

-- Ser bijectius és una relació d'equivalència sobre els tipus
-- Afegeiu tots els lemes previs que necessiteu
theorem TEqBij : Equivalence Bijectius := by
  sorry

-- Exercicis de Subtipus
-- L'aplicació inclusió és injectiva
#check Subtipus.inc
theorem TincInj {Ω : Type} (P : Ω → Prop) : PropApl.Inj.injectiva  (Subtipus.inc P) := by
  sorry

-- Defineix la imatge epimorfica d'una aplicació
def Depi {Δ Ω : Type} (f: Δ → Ω) : Δ → Subtipus.Im f := by
  sorry

-- La imatge epimorfica d'una aplicació a la seua imatge és sobrejectiva
theorem TDEpiSobre {Δ Ω : Type} (f: Δ → Ω) : PropApl.Sobre.sobrejectiva (Depi f) := by
  sorry

-- Exercicis de Tipus Quocients
-- L'aplicació projecció és sobrejectiva
#check Quocient.pr
theorem TprSobre {Ω : Type} (s : Setoid Ω) : PropApl.Sobre.sobrejectiva (Quocient.pr s) := by
  sorry

-- Defineix la imatge monomorfica d'una aplicació
def Dmono {Γ Ω : Type} (f: Ω → Γ) : Quocient.QKer f → Γ := by
  sorry

-- La imatge monomorfica d'una aplicació és injectiva
theorem TDmonoInj {Δ Ω : Type} (f: Δ → Ω) : PropApl.Inj.injectiva (Dmono f) := by
  sorry

-- Primer teorema d'isomorfisme
-- Defineix la bijectivitzada d'una aplicació
def DBij {A B : Type} (f : A → B) : Quocient.QKer f → Subtipus.Im f := by
  sorry

-- Comprova que la bijectivitzada d'una aplicació és bijectiva
theorem TDBij {A B : Type} (f : A → B) : bijectiva (DBij f) := by
  sorry

end ExS4
