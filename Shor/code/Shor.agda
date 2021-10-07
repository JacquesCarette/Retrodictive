module Shor where

open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat

infixr 10 _↔_
infixr 12 _×ᵤ_
infixr 12 _⊗_
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

-- Given that we will not the sizes, partial evaluation will be
-- exact on every operation except X, CX, and CCX when their
-- inputs are only partially known

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

-----------------------------------------------------------------------------
-- Building blocks

-- SUM (c , a , b)
SUM : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
SUM = (id↔ ⊗ CX) ⨾ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆) ⨾
      (id↔ ⊗ CX) ⨾ (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆)

-- CARRY (c , a , b , c')
CARRY : 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ↔ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚 ×ᵤ 𝟚
CARRY =
  (id↔ ⊗ CCX) ⨾
  (id↔ ⊗ (assocl⋆ ⨾ (CX ⊗ id↔) ⨾ assocr⋆)) ⨾ 
  (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆) ⨾
  (id↔ ⊗ CCX) ⨾
  (assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆) ⨾
  (id↔ ⊗ (assocl⋆ ⨾ (CX ⊗ id↔) ⨾ assocr⋆))

-- ROTATER (a , b , ... , x , y) = (y , a , b , ... , x)
ROTATER : {n : ℕ} → 𝔹^ n ↔ 𝔹^ n
ROTATER {0} = id↔ 
ROTATER {1} = id↔ 
ROTATER {suc (suc n)} = (id↔ ⊗ ROTATER) ⨾ assocl⋆ ⨾ (swap⋆ ⊗ id↔) ⨾ assocr⋆ 

-- ADD (carry[n] , first[n] , second[n+1])
ADD : {n : ℕ} → 𝔹^ n ×ᵤ 𝔹^ n ×ᵤ 𝔹^ (suc n) ↔ 𝔹^ n ×ᵤ 𝔹^ n ×ᵤ 𝔹^ (suc n)
ADD {0} = id↔ 
ADD {1} = 
  (unite⋆ ⊗ unite⋆ ⊗ (id↔ ⊗ unite⋆)) ⨾
  (id↔ ⊗ id↔ ⊗ swap⋆) ⨾ CARRY ⨾
  assocl⋆ ⨾ assocl⋆ ⨾ ((assocr⋆ ⨾ SUM ⨾ assocl⋆) ⊗ id↔) ⨾ assocr⋆ ⨾ assocr⋆ ⨾
  (id↔ ⊗ (id↔ ⊗ swap⋆)) ⨾
  (uniti⋆ ⊗ uniti⋆ ⊗ (id↔ ⊗ uniti⋆))
ADD {suc (suc n)} =
  (ROTATER ⊗ ROTATER ⊗ ROTATER) ⨾
  ((id↔ ⊗ ROTATER) ⊗ id↔ ⊗ id↔) ⨾
  {!!} 

{--
c a b

--}

-----------------------------------------------------------------------------
-- Tests

t1 = interp CARRY (false , false , false , false)
t2 = interp CARRY (false , false , true , false)
t3 = interp CARRY (false , true , true , false)
t4 = interp CARRY (true , false , true , false)
t5 = interp CARRY (true , true , true , false)
t6 = interp CARRY (false , true , true , true)

t7 = interp SUM (false , false , true)
t8 = interp SUM (true , false , true)
t9 = interp SUM (true , true , true)

t10 = interp ROTATER (false , tt)
t11 = interp ROTATER (false , true , tt)
t12 = interp ROTATER (false , false , true , tt)
t13 = interp ROTATER (false , false , false , true , tt)
t14 = interp ROTATER (false , false , true , false , true , tt)

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

