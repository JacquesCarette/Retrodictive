module Shor where

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat

infixr 10 _↔_
infixr 12 _×ᵤ_
infixr 50 _⨾_

-----------------------------------------------------------------------------
-- Goal is to define reversible version of a^x mod N
-- Follow the book by Rieffel and Polak (Ch. 6)

data 𝕌 : Set where
  𝟙     : 𝕌
  𝟚     : 𝕌
  _×ᵤ_  : 𝕌 → 𝕌 → 𝕌

⟦_⟧ : (A : 𝕌) → Set
⟦ 𝟙 ⟧ = ⊤
⟦ 𝟚 ⟧ = Bool
⟦ t₁ ×ᵤ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

data _↔_ : 𝕌 → 𝕌 → Set where
  unite⋆   : {t : 𝕌} → t ×ᵤ 𝟙 ↔ t
  uniti⋆   : {t : 𝕌} → t ↔ t ×ᵤ 𝟙
  swap⋆    : {t₁ t₂ : 𝕌} → t₁ ×ᵤ t₂ ↔ t₂ ×ᵤ t₁
  assocl⋆  : {t₁ t₂ t₃ : 𝕌} → t₁ ×ᵤ (t₂ ×ᵤ t₃) ↔ (t₁ ×ᵤ t₂) ×ᵤ t₃
  assocr⋆  : {t₁ t₂ t₃ : 𝕌} → (t₁ ×ᵤ t₂) ×ᵤ t₃ ↔ t₁ ×ᵤ (t₂ ×ᵤ t₃)
  id↔      : {t : 𝕌} → t ↔ t
  _⨾_      : {t₁ t₂ t₃ : 𝕌} → (t₁ ↔ t₂) → (t₂ ↔ t₃) → (t₁ ↔ t₃)
  _⊗_      : {t₁ t₂ t₃ t₄ : 𝕌} → (t₁ ↔ t₃) → (t₂ ↔ t₄) → (t₁ ×ᵤ t₂ ↔ t₃ ×ᵤ t₄)
  X        : 𝟚 ↔ 𝟚
  CX       : 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚
  CCX      : 𝟚 ×ᵤ (𝟚 ×ᵤ 𝟚) ↔ 𝟚 ×ᵤ (𝟚 ×ᵤ 𝟚)

! : {A B : 𝕌} → (A ↔ B) → (B ↔ A)
! unite⋆ = uniti⋆ 
! uniti⋆ = unite⋆ 
! swap⋆ = swap⋆
! assocl⋆ = assocr⋆
! assocr⋆ = assocl⋆
! id↔ = id↔
! (c₁ ⨾ c₂) = ! c₂ ⨾ ! c₁
! (c₁ ⊗ c₂) = ! c₁ ⊗ ! c₂
! X = X
! CX = CX
! CCX = CCX

interp : {A B : 𝕌} → (A ↔ B) → ⟦ A ⟧ → ⟦ B ⟧
interp unite⋆ (v , tt) = v
interp uniti⋆ v = (v , tt)
interp swap⋆   (v₁ , v₂)        = (v₂ , v₁)
interp assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
interp assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
interp id↔ v = v
interp (c₁ ⨾ c₂) v = interp c₂ (interp c₁ v)
interp (c₁ ⊗ c₂) (v₁ , v₂) = (interp c₁ v₁ , interp c₂ v₂)
interp X b = not b
interp CX (true , b) = (true , not b)
interp CX bs = bs
interp CCX (true , (true , b)) = (true , (true , not b))
interp CCX bs = bs

-----------------------------------------------------------------------------
-- Helpers 

𝔹^ : ℕ → 𝕌
𝔹^ 0 = 𝟙
𝔹^ (suc n) = 𝟚 ×ᵤ 𝔹^ n

[AB]C=[AC]B : {A B C : 𝕌} → (A ×ᵤ B) ×ᵤ C ↔ (A ×ᵤ C) ×ᵤ B
[AB]C=[AC]B = assocr⋆ ⨾ (id↔ ⊗ swap⋆) ⨾ assocl⋆

CCX* : {A : 𝕌} → 𝟚 ×ᵤ (𝟚 ×ᵤ (𝟚 ×ᵤ A)) ↔ 𝟚 ×ᵤ (𝟚 ×ᵤ (𝟚 ×ᵤ A))
CCX* = (id↔ ⊗ assocl⋆) ⨾ assocl⋆ ⨾ (CCX ⊗ id↔) ⨾ assocr⋆ ⨾ (id↔ ⊗ assocr⋆)

-----------------------------------------------------------------------------
-- Building blocks

FLIP : {m : ℕ} → 𝔹^ (suc m) ×ᵤ 𝔹^ m ↔ 𝔹^ (suc m) ×ᵤ 𝔹^ m
FLIP {0} = id↔
FLIP {suc 0} =
  ((id↔ ⊗ unite⋆) ⊗ unite⋆) ⨾
  assocr⋆ ⨾ CCX ⨾ assocl⋆ ⨾
  ((id↔ ⊗ uniti⋆) ⊗ uniti⋆)
FLIP {suc (suc m)} =
  [AB]C=[AC]B ⨾
  ((id↔ ⊗ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆)) ⊗ id↔) ⨾
  (CCX* ⊗ id↔) ⨾
  ((id↔ ⊗ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆)) ⊗ id↔) ⨾
  (assocl⋆ ⊗ id↔) ⨾ assocr⋆ ⨾ (id↔ ⊗ swap⋆) ⨾
  (id↔ ⊗ FLIP) ⨾
  (id↔ ⊗ swap⋆) ⨾ assocl⋆ ⨾ (assocr⋆ ⊗ id↔) ⨾
  ((id↔ ⊗ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆)) ⊗ id↔) ⨾
  (CCX* ⊗ id↔) ⨾
  ((id↔ ⊗ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆)) ⊗ id↔) ⨾
  ! [AB]C=[AC]B 

-- TEST AND SIMPLIFY AS MUCH AS POSSIBLE

-----------------------------------------------------------------------------
-- Tests



-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

{--

-----------------------------------------------------------------------------
-- Patterns and data definitions

pattern 𝔹 = 𝟙 +ᵤ 𝟙
pattern 𝔽 = inj₁ tt
pattern 𝕋 = inj₂ tt

X : 𝔹^ 1 ↔ 𝔹^ 1
X = swap₊

CX : 𝔹^ 2 ↔ 𝔹^ 2
CX = dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor

CCX : 𝔹^ 3 ↔ 𝔹^ 3
CCX = dist ⨾ (id↔ ⊕ (id↔ ⊗ CX)) ⨾ factor

AND : {m : ℕ} → 𝔹^ m ↔ 𝔹^ m
AND = {!!} 

-- NOT(b) = ¬b
NOT : 𝔹 ↔ 𝔹
NOT = swap₊

-- CNOT(b₁,b₂) = (b₁,b₁ xor b₂)
CNOT : 𝔹 ×ᵤ 𝔹 ↔ 𝔹 ×ᵤ 𝔹
CNOT = dist ⨾ (id↔ ⊕ (id↔ ⊗ swap₊)) ⨾ factor

-- CIF(c₁,c₂)(𝔽,a) = (𝔽,c₁ a)
-- CIF(c₁,c₂)(𝕋,a) = (𝕋,c₂ a)
CIF : {A : 𝕌} → (c₁ c₂ : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF c₁ c₂ = dist ⨾ ((id↔ ⊗ c₁) ⊕ (id↔ ⊗ c₂)) ⨾ factor

CIF₁ CIF₂ : {A : 𝕌} → (c : A ↔ A) → 𝔹 ×ᵤ A ↔ 𝔹 ×ᵤ A
CIF₁ c = CIF c id↔
CIF₂ c = CIF id↔ c

-- TOFFOLI(b₁,…,bₙ,b) = (b₁,…,bₙ,b xor (b₁ ∧ … ∧ bₙ))
TOFFOLI : {n : ℕ} → 𝔹^ n ↔ 𝔹^ n
TOFFOLI {0} = id↔
TOFFOLI {1} = swap₊
TOFFOLI {suc (suc n)} = CIF₂ TOFFOLI

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--}
