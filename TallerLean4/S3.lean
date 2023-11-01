-- Sessió 3 - 23/10/23
-- Treballem amb igualtats i aplicacions

-- L'objectiu d'aquesta sessió és introduïr les igualtats i les aplicacions entre tipus i treballarem amb algunes de les seues propietats bàsiques
-- Seguirem https://lean-lang.org/theorem_proving_in_lean4/quantifiers_and_equality.html

namespace Igualtat
-- En aquest espai treballarem amb la igualtat
-- Ω (\Omega) és un tipus que farà de contenidor
variable (Ω : Type)
-- P serà una proposició sobre Ω
variable (P : Ω → Prop)
-- Considerem dues variables x i y de tipus Ω
variable (x y : Ω)
-- Comprovem el tipus de l'igualtat x=y
#check x=y

#check rfl
-- La igualtat és reflexiva
theorem TEqRfl (a : Ω) : a=a := by
  exact rfl

-- La igualtat és simètrica
theorem TEqSymm (a b : Ω) (h : a=b) : (b=a) := by
  exact Eq.symm h

-- La igualtat és transitiva
theorem TEqTrans (a b c : Ω) (h1 : a=b) (h2 : b=c) : a=c := by
  exact Eq.trans h1 h2

-- La igualtat serveix per a reescriure els objectius
theorem TEqRw (a b : Ω) (h1 : a=b) (h2 : P b) : P a := by
  rewrite [h1]
  exact h2

-- La reescritura funciona d'esquerra a dreta
theorem TEqRw2 (a b : Ω) (h1 : a=b) (h2 : P a) : P b := by
  rewrite [h1.symm]
  exact h2

-- Es poden reescriure hipòtesis
theorem TEqRw3 (a b : Ω) (h1 : a=b) (h2 : P b) : P a := by
  rewrite [h1.symm] at h2
  exact h2

-- Demostracions calculístiques
theorem TCalc (a b c d : Ω) (h1 : a=b) (h2 : b=c) (h3: c=d) : (a=d) := by
  calc
    a = b := by rw [h1]
    _ = c := by rw [h2]
    _ = d := by rw [h3]

end Igualtat

namespace Aplicacions
-- En aquest espai treballarem amb les aplicacions
-- X Y seran tipus que faran de contenidor
variable (X Y Z: Type)
-- Les aplicacions d'X en Y són elements del tipus X→Y
variable (f g : X→Y)
variable (h : Y→Z)

-- Considerem un element x : X
variable (x: X)
-- Aleshores f x : Y
#check f x

-- Les aplicacions es poden composar amb ∘ (\circ)
#check h∘f

-- Dues aplicacions f g : X→Y  són iguals si, i només si, per a tots els elements x : X es té que f x = g x
theorem TEqApl : f = g ↔ ∀ (x : X), f x = g x := by
  apply Iff.intro
  -- Primera implicació
  intro h
  intro z
  exact congrFun h z
  -- Segona implicació
  intro h
  exact funext h

end Aplicacions

namespace PropApl
-- Introduïm l'aplicació identitat
def idt (X : Type) : X→X := by
  intro x
  exact x

-- El següent teorema diu com funciona l'aplicació identitat
theorem idteq {X : Type} (x : X) : idt X x = x := by exact rfl

namespace Inj
-- En aquest espai definim  tres conceptes sobre una aplicació, el d'injectivitat, el de ser monomorfisme i el de tindre invers per l'esquerra

-- Definició d'aplicació injectiva
def injectiva {X Y : Type} (f : X→Y) : Prop := ∀(x y: X), f x = f y → x = y

-- Definició de monomorfisme
def monomorfisme {X Y : Type} (f : X→Y) : Prop := ∀(Z : Type), ∀(g h : Z→X), f∘g=f∘h  → g=h

-- Definició d'inversa a esquerra
def invesq {X Y : Type} (f : X→Y) : Prop := ∃(g : Y→X), g∘f = idt X

-- Teoremes
-- La identitat és injectiva
theorem TIdInj {X:Type} : injectiva (idt X) := by
  rw [injectiva]
  intros x y h
  rw [idteq x, idteq y] at h
  exact h

-- Negació de la injectivitat
theorem TNegInj {X Y : Type} (f: X→Y) : ¬ (injectiva f) ↔ ∃(x y : X), f x = f y ∧ x ≠ y := by
  sorry

-- La composició d'injectives és injectiva
theorem TCompInj {X Y Z: Type} (f: X→Y) (g: Y→Z) (h1: injectiva f) (h2: injectiva g) : injectiva (g∘f) := by
  sorry

-- Si la composició (g∘f) és injectiva, aleshores f és injectiva
theorem TCompDInj {X Y Z: Type} (f: X→Y) (g: Y→Z) (h1: injectiva (g∘f)) : (injectiva f) := by
  sorry

-- Ser injectiva és equivalent a ser monomorfisme
theorem TCarMonoInj {X Y : Type} (f: X→Y) : injectiva f ↔ monomorfisme f := by
  sorry

-- Ser injectiva és equivalent a tindre inversa per l'esquerra
theorem TCarInvesqInj {X Y : Type} (f: X→Y) : injectiva f ↔ invesq f := by
  sorry

end Inj

--------

namespace Sobre
-- En aquest espai definim  tres conceptes sobre una aplicació, el de sobrejectivitat, el de ser epimorfisme i el de tindre invers per la dreta

-- Definició d'aplicació sobrejectiva
def sobrejectiva {X Y : Type} (f : X→Y) : Prop := ∀(y : Y), ∃(x : X), f x = y

-- Definició d'epimorfisme
def epimorfisme {X Y : Type} (f : X→Y) : Prop := ∀(Z : Type), ∀(g h : Y→Z), g∘f=h∘f  → g=h

-- Definició d'inversa a dreta
def invdret {X Y : Type} (f : X→Y) : Prop := ∃(g : Y→X), f∘g = idt Y

-- Teoremes
-- La identitat és sobrejectiva
theorem TIdInj {X:Type} : sobrejectiva (idt X) := by
  rw [sobrejectiva]
  intros x
  apply Exists.intro x
  exact idteq x

-- Negació de la sobrejectivitat
theorem TNegSobre {X Y : Type} (f: X→Y) : ¬ (sobrejectiva f) ↔ ∃(y : Y), ∀ (x : X), f x ≠ y := by
  sorry

-- La composició de sobrejectives és sobrejectiva
theorem TCompSobre {X Y Z: Type} (f: X→Y) (g: Y→Z) (h1: sobrejectiva f) (h2: sobrejectiva g) : sobrejectiva (g∘f) := by
  sorry

-- Si la composició (g∘f) és sobrejectiva, aleshores g és sobrejectiva
theorem TCompDSobre {X Y Z: Type} (f: X→Y) (g: Y→Z) (h1: sobrejectiva (g∘f)) : (sobrejectiva g) := by
  sorry

-- Ser sobrejectiva és equivalent a ser epimorfisme
theorem TCarEpiSobre {X Y : Type} (f: X→Y) : sobrejectiva f ↔ epimorfisme f := by
  sorry

-- Si es té inversa per la dreta, aleshores és equivalent sobrejectiva
theorem TImplInvDretSobre {X Y : Type} (f: X→Y) : invdret f → sobrejectiva f := by
  sorry

end Sobre
end PropApl
