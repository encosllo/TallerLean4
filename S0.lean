-- Sessió 0 - 25/09/23
-- Primeres definicions i sintaxi de Lean4

-- Observem que en el nostre espai de treball tenim dues finestres
-- Una finestra farà d'editor de text i una altra farà d'intèrpret
-- Els fitxers .Lean s'obriran en l'editor i l'intèrpret executarà les línies de codi en situar el cursor a la dreta de les expressions que apareixen a l'editor

-- En Lean tots els objectes amb els què treballem estaran tipificats
-- L'expressió a:A es llig com a té tipus A
-- Lean ja compta amb l'implementació d'alguns tipus, com els Naturals denotats per ℕ (\nat) o Nat, els Booleans denotats per Bool, els Enters denotats per Int, les Cadenes denotades per String, etc
-- Amb la comanda #check podem comprovar el tipus d'un objecte donat
-- Per a que l'intèrpret execute l'ordre fer-ho escriurem el text i situarem el cursor a la dreta de l'expressió que 
#check Nat  
#check Bool 
#check Int 
#check String

-- Si volem conèixer com estan implementats els tipus internament emprarem la comanda #print
#print Nat
#print Bool
#print Int
#print String

-- Existeix el tipus tipus denotat per Type
-- Podem treballar amb ell com amb qualsevol altre tipus
-- La diferència és que en comprovar el seu tipus ens diu que té Tipus 1, és a dir, un tipus d'ordre superior
#check Type 
-- I així de forma indefinida
#check Type 1

-- Si volem definir un objecte concret d'un tipus utilitzarem expressions com 
def x : Nat := 5
-- En aquest cas estem definint a l'objecte que s'anomena x, estem dient que té tipus Nat i que té el valor concret de 5
-- Si comprovem el seu tipus, ens diu que és un natural
#check x  
-- Si l'avaluem ens torna el valor que té assignat
#eval x
-- Si volem saber com està implementat
#print x

-- Podem crear variables d'un tipus concret que estaran definides globalment per a tot el document
variable (m n: Nat)
#check m

-- També podem crear espais de treball i dins d'aquests espais definir variables 
-- Adona't que els espais de treball es poden col·lapsar per a millorar la presentació de l'editor
-- Les variables que hi definim només tindran interpretació dins de l'espai de treball
-- Creem un Espai de Treball anomenat EspaiTreball i dins creem una variable de tipus natural
namespace EspaiTreball
def r : Nat := 27
-- Notem que la variable r està perfectament definida dins l'espai de treball
#check r
#eval r 
#print r
end EspaiTreball

-- Però en eixir de l'espai de treball, el sistema deixa de reconèixer la variable r
#check r 
#eval r
#print r
-- Per a recuperar la variable r haurem d'escriure prèviament l'espai de Treball on està definida
#check EspaiTreball.r
#eval EspaiTreball.r
#print EspaiTreball.r

-- Podem construïr nous tipus a partir de tipus donats
-- Per exemple el producte de dos tipus emprant el constructor × (\times)
#check Nat × Nat
-- Els elements d'aquest nou tipus seran parells ordenats
-- Per als guionets ⟨ (⟨) i ⟩ (⟩)  
def p : Nat × Nat := ⟨2,3⟩  
-- Comprovem tipus, significat i construcció
#check p
#eval p
#print p

-- El tipus de les aplicacions d'un tipus en un altre emprant el constructor → (\to) 
#check Nat → Nat
-- Els elements d'aquest nou tipus seran aplicacions
def f: Nat → Nat := by 
  intro x
  exact x + 5
-- Hem definit l'aplicació f:Nat → Nat, que a cada x:Nat li assigna x + 5 
-- Comprovem tipus
#check f
-- En avaluar aquests nou objectes rebem un missatge d'error
#eval f
-- Les aplicacions s'avaluen sobre elements del domini
#eval f 2
-- Podem vore com estan construïdes
#print f

-- Vegem que ens ha tornat notació alternativa per a definir aplicacions
def f' : Nat → Nat :=
  fun x => x + 5
-- O també podríem escriure-ho amb notació λ (\lambda) com
def f'' : Nat → Nat :=
  λ x => x+ 5

-- Encara que funcionen igual, les aplicacions f, f' i f'' són diferents per a Lean perquè tenen noms diferents

-- Les aplicacions es poden composar amb ∘ (\circ)
#check f∘f
#eval (f∘f) (2)
-- O també 
#eval f (f 2) 