-- Sessió 8 - 27/11/23
-- Definim l'ordre sobre els naturals

import TallerLean4.S7

-- En aquesta sessió anem a implementar l'ordre habitual sobre els naturals

-- Recordem algunes definicions bàsiques
-- Relació irreflexiva
def irreflexiva {X : Type} (R : X → X → Prop) : Prop :=
  ∀ (x : X), ¬ R x x

-- Obrim la clausura reflexivo-transitiva
open ClRT
-- Obrim els nostre naturals
open N

-- Definim la següent relació de predecessor sobre N
def Dprec : N → N → Prop := by
  intro n m
  exact m = s n

-- Considerem la clausura reflexivo-transitiva de
-- la relació de predecessor
def Dleq : N → N → Prop := crt Dprec

-- Emprarem la següent notació per a estes relacions
-- ≼ (\preceq) per a la relació de predecessor
notation : 65 lhs:65 " ≼ " rhs:66 => Dprec lhs rhs
-- ≤ (\leq) per a la clausura reflexivo-transitiva
notation : 65 lhs:65 " ≤  " rhs:66 => Dleq lhs rhs

-- Comprovem que que ≤ és un ordre sobre N
-- Per a fer-ho considerarem els següents lemmes
-- Lema 1
theorem LOrd1  (n m : N) : ¬ ((n ≼ m) ∧ (m ≼ n)) := by
  by_contra h
  have h1 : n≼m := by exact h.left
  have h2 : m≼n := by exact h.right
  rw [Dprec] at h1 h2
  rw [h2] at h1
  have h3 (k : N) : ¬ k = s (s k) := by
    by_contra h3
    -- Per inducció sobre k
    induction k
    -- Cas base
    injection h3
    -- Pas inductiu
    rename_i k hInd
    injection h3 with h3
    exact hInd h3
  specialize h3 m
  exact h3 h1

-- La relació ≼ és antisimètrica
theorem DprecAnti : antisimetrica Dprec := by
  intro n m
  intro h1
  have h2 : ¬ ((n ≼ m) ∧ (m ≼ n)) := by exact LOrd1 n m
  exact False.elim (h2 h1)

-- Lema 2
theorem LOrd2 (n : N) : ¬ (n ≼ z) := by
  by_contra h1
  induction n
  injection h1
  rename_i k hInd
  rw [Dprec] at h1
  injection h1

-- Lema 3
theorem LOrd3 (n : N) (h1: n ≠ z) : ¬ (n ≤ z) := by
  by_contra h1
  induction h1
  rename_i k hInd
  induction k
  have h2 : n = z := by exact hInd
  exact h1 h2
  rename_i k hIndk
  -- Per casos sobre hInd
  cases hInd
  -- Cas inl
  rename_i hinl
  exact hIndk hinl
  -- Cas inr
  rename_i hinr
  apply Exists.elim hinr
  intro m
  intro h3
  have h4 : ¬ (m ≼ z) := by exact LOrd2 m
  exact h4 h3.right

-- Lema 4
theorem LOrd4 (n m : N) (h1 : n ≼ m) : s n ≼ s m := by
  rw [Dprec] at h1
  exact congrArg s h1

-- Lema 5
theorem LOrd5 (n : N) : z ≤ n := by
  use n
  induction n
  exact rfl
  rename_i n hInd
  apply Or.inr
  use n
  apply And.intro
  exact hInd
  exact rfl

-- Lema 6
theorem LOrd6 (n k : N) : (it Dprec k n z) → n = z := by
  intro h1
  induction k
  exact h1
  rename_i k hInd
  cases h1
  --
  rename_i h1inl
  exact hInd h1inl
  --
  rename_i h1inr
  apply Exists.elim h1inr
  intro p
  intro ⟨h1,h2⟩
  rw [Dprec] at h2
  injection h2
--

-- Lema 7
theorem LOrd7 (n k : N) : (it Dprec k n n) := by
  induction k
  exact rfl
  rename_i k hInd
  exact Or.inl hInd

-- Lema8
theorem LOrd8 (n k : N) : ∀ (m:N), it Dprec k (s n) m → it Dprec (s k) n m := by
  induction k
  -- Cas base
  intro m
  intro h
  apply Or.inr
  use n
  apply And.intro
  exact rfl
  exact h.symm
  -- Pas inductiu
  intro m
  intro h
  rename_i k hInd
  cases h
  rename_i hinl
  exact Or.inl ((hInd m) hinl)
  rename_i hinr
  apply Exists.elim hinr
  intro p
  intro ⟨h1, h2⟩
  apply Or.inr
  use p
  apply And.intro
  exact (hInd p) h1
  exact h2

-- Lema 9
theorem LOrd9 (n k: N) : ∀(m:N), it Dprec k n m ↔ it Dprec k (s n) (s m) := by
  induction k
  intro m
  apply Iff.intro
  --
  intro h1
  exact congrArg s h1
  intro h1
  injection h1
  --
  rename_i k hInd
  intro m
  apply Iff.intro
  intro h1
  cases h1
  rename_i h1inl
  apply Or.inl
  specialize hInd m
  exact hInd.mp (h1inl)
  rename_i h1inr
  apply Exists.elim h1inr
  intro p
  intro ⟨h2,h3⟩
  apply Or.inr
  use (s p)
  apply And.intro
  specialize hInd p
  exact hInd.mp h2
  exact congrArg s h3
  intro h1
  cases h1
  rename_i h1inl
  specialize hInd m
  apply Or.inl
  exact hInd.mpr h1inl
  rename_i h1inr
  apply Exists.elim h1inr
  intro p
  intro ⟨h2,h3⟩
  rw [Dprec] at h3
  injection h3 with h3
  rw [h3.symm] at h2
  exact LOrd8 n k m h2
--

-- Lema 10
theorem LOrd10 (n k : N) : ¬(it Dprec k (s n) n) := by
  by_contra h1
  induction n
  induction k
  injection h1
  rename_i n hInd
  have h2 : s z = z := by exact LOrd6 (s z) (s n) h1
  injection h2
  rename_i n hInd
  have h2: it Dprec k (s n) n := by
    exact (LOrd9 (s n) k n).mpr h1
  exact hInd h2

-- Obrim la suma
open Suma

-- Lema 11
theorem LOrd11 (n k : N) : ∀(m:N), it Dprec (s k) n m → (it Dprec k n m) ∨ m = s (n + k) := by
  induction k
  -- Cas base
  intro m
  intro h1
  cases h1
  --
  rename_i h1l
  exact Or.inl h1l
  --
  rename_i h1r
  apply Exists.elim h1r
  intro p
  intro ⟨h1, h2⟩
  have h3 : n = p := by exact h1
  rw [h3.symm] at h2
  rw [Dprec] at h2
  apply Or.inr
  have h4 : n = n+z := by exact (TSuma0ND n).symm
  rw [h4.symm]
  exact h2
  --
  -- Pas inductiu
  rename_i k hInd
  intro m
  intro h1
  cases h1
  --
  rename_i h1l
  exact Or.inl h1l
  --
  rename_i h1r
  apply Exists.elim h1r
  intro p
  intro ⟨h1,h2⟩
  have h3 : it Dprec k n p ∨ p = s (n + k) := by exact hInd p h1
  cases h3
  --
  rename_i h3l
  apply Or.inl
  apply Or.inr
  use p
  --
  rename_i h3r
  apply Or.inr
  have h4 : s (n + k) = n + (s k) := by
    calc
      s (n + k) = (s n) + k := by exact rfl
      _ = n + (s k) := by exact TSumUn n k
  calc
    m = s p := by exact h2
    _ = s (s (n + k)) := by exact congrArg s h3r
    _ = s (n + (s k)) := by exact congrArg s h4
--

-- Lema 12
theorem LOrd12 (k : N) : ∀(m:N), it Dprec k (s (m + k)) m → False := by
  induction k
  -- Cas base
  intro m h1
  have h2 : m + z = m := by exact TSuma0ND m
  rw [h2] at h1
  have h3 : ¬ it Dprec z (s m) m := by exact LOrd10 m z
  exact h3 h1
  -- Pas inductiu
  rename_i k hInd
  intro m h1
  have h2 : (it Dprec k (s (m + s k)) m) ∨ m = s ((s (m + s k)) + k) := by exact LOrd11 (s (m + s k)) k m h1
  cases h2
  --
  rename_i h2l
  have h3 : it Dprec (s k) (m + s k) m := by exact LOrd8 (m + s k) k m h2l
  have h4 : (it Dprec k (m + s k) m) ∨ m = s ((m + s k) + k) := by exact LOrd11 (m + s k) k m h3
  cases h4
  rename_i h4l
  have h5 : m + s k = s (m + k) := by
    calc
      m + s k = s m + k := by exact (TSumUn m k).symm
      _ = s (m +k) := by exact rfl
  rw [h5] at h4l
  exact hInd m h4l
  --
  rename_i h4r
  have h5 : s (m + s k + k) = m + s (k + s k) := by
    have h6 : m + s k + k = m + (s k + k) := by exact TSumaAss m (s k) k
    rw [h6]
    have h7 : s (m + (s k + k)) = (s m) + (s k + k) := by exact rfl
    rw [h7]
    have h8 : (s m) + (s k + k) = m + (s (s k + k)) := by
      apply TSumUn
    rw [h8]
    apply TCongd
    apply congrArg s
    exact TSumUn k k
  rw [h5] at h4r
  exact TIncSuc m (k + s k) h4r
  --
  rename_i h2r
  have h5 : s (s (m + s k) + k) = m + s (s (s k) + k) := by
    have h6 : m + s (s (s k) + k) = (s m) + (s (s k) + k) := by
      exact (TSumUn m (s (s k) + k)).symm
    rw [h6]
    have h7 : s m + (s (s k) + k) = s (m + ((s (s k) + k))) := by exact rfl
    rw [h7]
    apply congrArg s
    have h8 : m + (s (s k) + k) = (m + s (s k)) + k := by
      exact (TSumaAss m (s (s k)) k).symm
    rw [h8]
    apply TConge
    have h9 : s (m + s k) = (s m) + s k := by exact rfl
    rw [h9]
    have h10 : m + s (s k) = (s m) + (s k) := by
      exact (TSumUn m (s k)).symm
    rw [h10]
  rw [h5] at h2r
  exact TIncSuc m (s (s k) + k) h2r

-- Lema 13
theorem LOrd13  (k : N) : ∀(n m : N), it Dprec k n m → n = s (m + k) → False := by
  intro n m
  intro h1 h2
  rw [h2] at h1
  exact LOrd12 k m h1

-- Lema 14
theorem LOrd14 (k : N) : ∀(n m: N), (it Dprec k n m) → (it Dprec k m n) → n = m := by
  induction k
  -- Cas base
  intro n m
  intro h1 h2
  exact h1
  -- Pas inductiu
  rename_i k hInd
  intro n m
  intro h1 h2
  have h3 : (it Dprec k n m) ∨ m = s (n + k) := by exact LOrd11 n k m h1
  have h4 : (it Dprec k m n) ∨ n = s (m + k) := by exact LOrd11 m k n h2
  cases h3
  -- Cas 3 left
  rename_i h3l
  cases h4
  -- Cas 4 left
  rename_i h4l
  exact (hInd n m) h3l h4l
  -- Cas 4 right
  rename_i h4r
  apply False.elim
  apply LOrd13
  exact h3l
  exact h4r
  -- Cas 3 right
  rename_i h3r
  cases h4
  -- Cas 4 left
  rename_i h4l
  apply False.elim
  apply LOrd13
  exact h4l
  exact h3r
  -- Cas 4 right
  rename_i h4r
  apply False.elim
  apply TIncSuma n m k
  calc
    m = s (n + k) := by exact h3r
    _ = s n + k := by exact rfl
    _ = n + s k := by exact TSumUn n k
  calc
    n = s (m + k) := by exact h4r
    _ = s m + k := by exact rfl
    _ = m + s k := by exact TSumUn m k
--

-- Lema 15
theorem LOrd15 (n m : N) : (n ≤ m) → (m ≤ n) → n = m := by
  intro h1 h2
  apply Exists.elim h1
  intro k h3
  apply Exists.elim h2
  intro l h4
  have h5 : it Dprec (k+l) n m :=  by
    apply LCrtTrans2 Dprec k l
    exact h3
  have h6 : it Dprec (l+k) m n :=  by
    apply LCrtTrans2 Dprec l k
    exact h4
  have h7 : k + l = l + k := by
    apply TSumaComm
  rw [h7] at h5
  exact LOrd14 (l + k) n m h5 h6

-- La relació ≤ és antisimètrica
theorem DleqAnti : antisimetrica Dleq := by
  rw [antisimetrica]
  intro n m
  intro ⟨h1, h2⟩
  exact LOrd15 n m h1 h2

-- La relació ≤ és transitiva
theorem DleqTrans : transitiva Dleq := by
  exact TCrtTrans Dprec

-- La relació ≤ és reflexiva
theorem DleqRfl : reflexiva Dleq := by
  exact TCrtRfl Dprec

-- La relació ≤ és un ordre
theorem DleqOrd : ordre Dleq := by
  rw [ordre]
  apply And.intro
  exact DleqRfl
  apply And.intro
  exact DleqAnti
  exact DleqTrans
