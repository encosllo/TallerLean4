-- Sessió 5 - 6/11/23
-- Treballem amb tipus producte i suma
-- L'objectiu d'aquesta sessió és introduïr els productes i els coproductes en Lean

import Paperproof
import TallerLean4.S4

namespace producte
-- Comencem amb el producte
-- X Y seran tipus que faran de contenidor
variable (X Y : Type)
-- Amb aquesta informació som capaços d'obtindre el tipus producte, X × Y (\times)
#check X×Y

-- Una construcció alternativa fa ús del constructor Prod
#check Prod
#print Prod
#check Prod X Y

-- Donar un element del producte és equivalent a
-- donar un element de la primera component
-- i un element de la segona component
#check Prod.mk
theorem TProdMk {X Y : Type} (x : X) (y : Y) : X×Y := by
  exact Prod.mk x y

-- Donat un element del producte podem considerar
-- la projecció (π \pi) a la primera component
def π1 {X Y : Type} : X×Y → X := by
  intro p
  exact p.1

-- Donat un element del producte podem considerar
-- la projecció (π \pi) a la segona component
def π2 {X Y : Type} : X×Y → Y := by
  intro p
  exact p.2

-- Dos elements del producte són iguals si, i només si,
-- tenen les mateixes components
#check Prod.ext
theorem PProdEq {X Y : Type} (p1 p2 : X×Y) : p1=p2 ↔ π1 p1 = π1 p2 ∧ π2 p1 = π2 p2 := by
  apply Iff.intro
  -- Cas 1
  intro h
  apply And.intro
  -- Cas π1
  exact congrArg π1 h
  -- Cas π2
  exact congrArg π2 h
  -- Cas 2
  intro ⟨h1,h2⟩
  exact Prod.ext h1 h2

-- Propietat Universal del producte
-- Donat qualsevol altre tipus Z i aplicacions f : Z → X i g : Z → Y
-- podem definir l'aplicació ⟨f,g⟩ : Z → X×Y
def PUProd {X Y Z : Type} (f : Z → X) (g : Z → Y) : Z → X×Y := by
  intro z
  apply Prod.mk
  exact f z
  exact g z

-- L'aplicació ⟨f,g⟩ satisfà que π1⟨f,g⟩=f
theorem TUProd1 {X Y Z : Type} (f : Z → X) (g : Z → Y) : π1∘(PUProd f g) = f := by
  apply funext
  intro z
  exact rfl

-- L'aplicació ⟨f,g⟩ satisfà que π2⟨f,g⟩=g
theorem TUProd2 {X Y Z : Type} (f : Z → X) (g : Z → Y) : π2∘(PUProd f g) = g := by
  apply funext
  intro z
  exact rfl

-- L'aplicació ⟨f,g⟩ és l'única que satisfà les dues condicions anteriors
theorem TUProdUniq {X Y Z : Type} (f : Z → X) (g : Z → Y) (h : Z → X×Y) (h1 : π1∘h = f) (h2 : π2∘h = g) : h = PUProd f g := by
  apply funext
  intro z
  have h3 : π1 (h z) = π1 (PUProd f g z) := by
    calc
      π1 (h z)  = (π1 ∘ h) z        := by exact rfl
      _         = f z               := by exact congrFun h1 z
      _         = π1 (PUProd f g z) := by exact rfl
  have h4 : π2 (h z) = π2 (PUProd f g z) := by
    calc
      π2 (h z)  = (π2 ∘ h) z        := by exact rfl
      _         = g z               := by exact congrFun h2 z
      _         = π2 (PUProd f g z) := by exact rfl
  have h5 : h z = PUProd f g z ↔ π1 (h z) = π1 (PUProd f g z) ∧ π2 (h z) = π2 (PUProd f g z) := by
    exact PProdEq (h z) (PUProd f g z)
  rw [h5]
  exact And.intro h3 h4
end producte

namespace coproducte
-- Continuem amb el coproducte
-- X Y seran tipus que faran de contenidor
variable (X Y : Type)
-- Amb aquesta informació som capaços d'obtindre el tipus producte, X ⊕ Y (\oplus)
#check X⊕Y

-- Una construcció alternativa fa ús del constructor Sum
#check Sum
#print Sum
#check Sum X Y

-- Donat un element d'x, podem considerar
-- la inclusió (ι \iota) a la primera component
#check Sum.inl
def ι1 {X Y : Type} (x : X) : X⊕Y := by
  exact Sum.inl x

-- Donat un element d'y, podem considerar
-- la inclusió (ι \iota) a la segona component
#check Sum.inr
def ι2 {X Y : Type} (y : Y) : X⊕Y := by
  exact Sum.inr y

-- Propietat Universal del coproducte
-- Donat qualsevol altre tipus Z i aplicacions f : X → Z i g : Y → Z
-- podem definir l'aplicació [f,g] : X⊕Y → Z
def PUCoProd {X Y Z : Type} (f : X → Z) (g : Y → Z) : X⊕Y → Z := by
  intro q
  cases q with
  | inl x => exact (f x)
  | inr y => exact (g y)

-- L'aplicació [f,g] satisfà que [f,g]∘ι1 = f
theorem TUCoProd1 {X Y Z : Type} (f : X → Z) (g : Y → Z) : (PUCoProd f g)∘ι1 = f := by
  apply funext
  intro x
  exact rfl

-- L'aplicació [f,g] satisfà que [f,g]∘ι2 = g
theorem TUCoProd2 {X Y Z : Type} (f : X → Z) (g : Y → Z) : (PUCoProd f g)∘ι2 = g := by
  apply funext
  intro y
  exact rfl

-- L'aplicació [f,g] és l'única que satisfà les dues condicions anteriors
theorem TUCoProdUniq {X Y Z : Type} (f : X → Z) (g : Y → Z) (h : X⊕Y → Z) (h1 : h∘ι1 = f) (h2 : h∘ι2 = g) : h = PUCoProd f g := by
  apply funext
  have h3 : ∀(x:X), h (ι1 x) = PUCoProd f g (ι1 x) := by
    intro x
    calc
       h (ι1 x) = (h ∘ ι1) x              := by exact rfl
       _        = f x                     := by exact congrFun h1 x
       _        = PUCoProd f g (ι1 x)     := by exact rfl
  have h4 : ∀(y:Y), h (ι2 y) = PUCoProd f g (ι2 y) := by
    intro y
    calc
       h (ι2 y) = (h ∘ ι2) y            := by exact rfl
       _        = g y                   := by exact congrFun h2 y
       _        = PUCoProd f g (ι2 y)   := by exact rfl
  intro q
  cases q with
  | inl x => exact h3 x
  | inr y => exact h4 y

end coproducte

namespace ExS5
-- En aquesta secció generalitzarem les anteriors construccions
-- a una família de tipus
-- Definim un tipus que farà d'índex
variable (I : Type)
-- Llavors una família de tipus indexada per I és una variable
-- del següent tipus (𝕏 \bbX)
variable (𝕏 : I → Type)

namespace producte
-- El producte de la família 𝕏 es denota com ∀(i:I), 𝕏 i
#check ∀(i:I), 𝕏 i

-- Donat un element del producte podem considerar
-- la projecció a la component i-èssima
def π {I : Type} {𝕏 : I → Type} (i : I) : (∀(i:I), 𝕏 i) → 𝕏 i := by
  sorry

-- Dos elements del producte són iguals si, i només si,
-- tenen les mateixes components
theorem PProdEqG {I : Type} {𝕏 : I → Type} (p1 p2 : ∀(i:I), 𝕏 i) : p1=p2 ↔ ∀(i:I), (π i p1 = π i p2) := by
  sorry

-- Propietat Universal del producte
-- Donat qualsevol altre tipus Z i famílies d'aplicacions
-- (fi : Z → 𝕏 i) (𝕗 \bbf) podem definir l'aplicació
-- ⟨fi⟩ : Z → ∀(i:I), 𝕏 i
def PUProdG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) : Z → (∀(i:I), 𝕏 i) := by
  sorry

-- L'aplicació ⟨fi⟩ satisfà que (πi)∘⟨fi⟩ = fi, per a tot i : I
theorem TUProdG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) (i : I) : (π i)∘(PUProdG 𝕗) = 𝕗 i := by
  sorry

-- L'aplicació ⟨fi⟩ és l'única que satisfà les condicions anteriors per a tot i : I
theorem TUProdUniqG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), Z → 𝕏 i ) (h : Z → (∀(i:I), 𝕏 i)) (hi : ∀(i:I) , (π i)∘h = 𝕗 i) : h = PUProdG 𝕗 := by
  sorry

end producte

namespace coproducte
-- El coproducte de la família 𝕏 es denota com Σ(i:I), 𝕏 i (Σ \Sigma)
#check Σ(i:I), 𝕏 i

-- Donat un element de 𝕏 i podem considerar
-- la inclusió a la component i-èssima
def ι {I : Type} {𝕏 : I → Type} (i : I) : 𝕏 i → (Σ(i:I), 𝕏 i) := by
  sorry

-- Propietat Universal del coproducte
-- Donat qualsevol altre tipus Z i famílies d'aplicacions
-- (fi : 𝕏 i → Z) (𝕗 \bbf) podem definir l'aplicació
-- [fi] : (Σ(i:I), 𝕏 i) → Z
def PUCoProdG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z) : (Σ(i:I), 𝕏 i) → Z := by
  sorry

-- L'aplicació [fi] satisfà que [fi]∘(ιi) = fi, per a tot i : I
theorem TUProdG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z) (i : I) : (PUCoProdG 𝕗)∘(ι i) = 𝕗 i := by
  sorry

-- L'aplicació [fi] és l'única que satisfà les condicions anteriors per a tot i : I
theorem TUCoProdUniqG {I Z : Type} {𝕏 : I → Type} (𝕗 : ∀(i:I), 𝕏 i → Z) (h : (Σ(i:I), 𝕏 i) → Z) (hi : ∀(i:I), h∘(ι i) = 𝕗 i) : h = PUCoProdG 𝕗 := by
  sorry
end coproducte

namespace lleis
-- Les següents lleis que comprovarem no ens donen estrictament
-- igualtats entre tipus, però sí tipus bijectius
-- Recordem la definició de la relació de ser bijectius
#check ExS4.Bijectius
#print ExS4.Bijectius

-- El producte commuta
theorem TProdAb {X Y : Type} : ExS4.Bijectius (X×Y) (Y×X) := by
  sorry

-- El producte és associatiu
theorem TProdAss {X Y Z : Type} : ExS4.Bijectius (X×(Y×Z)) ((X×Y)×Z) := by
  sorry

-- El producte té al tipus Unit com a unitat per l'esquerra
theorem TProdUnitL {X : Type} : ExS4.Bijectius (X×Unit) (X) := by
  sorry

-- El producte té al tipus Unit com a unitat per la dreta
theorem TProdUnitR {X : Type} : ExS4.Bijectius (Unit×X) (X) := by
  sorry

-- El coproducte commuta
theorem TCoProdAb {X Y : Type} : ExS4.Bijectius (X⊕Y) (Y⊕X) := by
  sorry

-- El coproducte és associatiu
theorem TCoProdAss {X Y Z : Type} : ExS4.Bijectius (X⊕(Y⊕Z)) ((X⊕Y)⊕Z) := by
  sorry

-- El coproducte té al tipus Empty com a unitat per l'esquerra
theorem TCoProdEmptyL {X : Type} : ExS4.Bijectius (X⊕Empty) (X) := by
  sorry

-- El producte té al tipus Unit com a unitat per la dreta
theorem TCoProdEmptyR {X : Type} : ExS4.Bijectius (Empty⊕X) (X) := by
  sorry

-- El producte distribueix per l'esquerra sobre el coproducte
theorem TDisL {X Y Z : Type} : ExS4.Bijectius (X×(Y⊕Z)) ((X×Y)⊕(X×Z)) := by
  sorry

-- El producte distribueix per la dreta sobre el coproducte
theorem TDisR {X Y Z : Type} : ExS4.Bijectius ((X⊕Y)×Z) ((X×Z)⊕(Y×Z)) := by
  sorry

end lleis
end ExS5
