{-# OPTIONS --without-K #-}

module PartialEval where

open import Data.Nat using (ℕ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_)

open import PiU
open import PiLevel0
open import PiEval

data U′ : Set where
  Pure  : U → U′
  Var   : ℕ → U → U′
  PLUSˡ  : U′ → U → U′
  PLUSʳ  : U → U′ → U′
  PLUS²  : U′ → U′ → U′
  TIMESˡ  : U′ → U → U′
  TIMESʳ  : U → U′ → U′
  TIMES²  : U′ → U′ → U′

------------------------------------------------------------------------------

-- probably need to 'mark' the virtual ones?
⟦_⟧′ : U′ → Set
⟦ Pure x ⟧′ = ⟦ x ⟧
⟦ Var i u ⟧′ = ⟦ u ⟧
⟦ PLUSˡ x y ⟧′ = ⟦ x ⟧′ ⊎ ⟦ y ⟧
⟦ PLUSʳ x y ⟧′ = ⟦ x ⟧ ⊎ ⟦ y ⟧′
⟦ PLUS² x y ⟧′ = ⟦ x ⟧′ ⊎ ⟦ y ⟧′
⟦ TIMESˡ x y ⟧′ = ⟦ x ⟧′ × ⟦ y ⟧
⟦ TIMESʳ x y ⟧′ = ⟦ x ⟧ × ⟦ y ⟧′
⟦ TIMES² x y ⟧′ = ⟦ x ⟧′ × ⟦ y ⟧′

data _⟷′_ : U′ → U′ → Set where
  lift    : {t₁ t₂ : U} → t₁ ⟷ t₂ → Pure t₁ ⟷′ Pure t₂
  unite₊l : {t : U′} → PLUSʳ ZERO t ⟷′ t
  {-
  uniti₊l : {t : U} → t ⟷ PLUS ZERO t
  unite₊r : {t : U} → PLUS t ZERO ⟷ t
  uniti₊r : {t : U} → t ⟷ PLUS t ZERO
  swap₊   : {t₁ t₂ : U} → PLUS t₁ t₂ ⟷ PLUS t₂ t₁
  assocl₊ : {t₁ t₂ t₃ : U} → PLUS t₁ (PLUS t₂ t₃) ⟷ PLUS (PLUS t₁ t₂) t₃
  assocr₊ : {t₁ t₂ t₃ : U} → PLUS (PLUS t₁ t₂) t₃ ⟷ PLUS t₁ (PLUS t₂ t₃)
  unite⋆l  : {t : U} → TIMES ONE t ⟷ t
  uniti⋆l  : {t : U} → t ⟷ TIMES ONE t
  unite⋆r : {t : U} → TIMES t ONE ⟷ t
  uniti⋆r : {t : U} → t ⟷ TIMES t ONE
  swap⋆   : {t₁ t₂ : U} → TIMES t₁ t₂ ⟷ TIMES t₂ t₁
  assocl⋆ : {t₁ t₂ t₃ : U} → TIMES t₁ (TIMES t₂ t₃) ⟷ TIMES (TIMES t₁ t₂) t₃
  assocr⋆ : {t₁ t₂ t₃ : U} → TIMES (TIMES t₁ t₂) t₃ ⟷ TIMES t₁ (TIMES t₂ t₃)
  absorbr : {t : U} → TIMES ZERO t ⟷ ZERO
  absorbl : {t : U} → TIMES t ZERO ⟷ ZERO
  factorzr : {t : U} → ZERO ⟷ TIMES t ZERO
  factorzl : {t : U} → ZERO ⟷ TIMES ZERO t
  dist    : {t₁ t₂ t₃ : U} →
            TIMES (PLUS t₁ t₂) t₃ ⟷ PLUS (TIMES t₁ t₃) (TIMES t₂ t₃)
  factor  : {t₁ t₂ t₃ : U} →
            PLUS (TIMES t₁ t₃) (TIMES t₂ t₃) ⟷ TIMES (PLUS t₁ t₂) t₃
  distl   : {t₁ t₂ t₃ : U } →
            TIMES t₁ (PLUS t₂ t₃) ⟷ PLUS (TIMES t₁ t₂) (TIMES t₁ t₃)
  factorl : {t₁ t₂ t₃ : U } →
            PLUS (TIMES t₁ t₂) (TIMES t₁ t₃) ⟷ TIMES t₁ (PLUS t₂ t₃)
  id⟷    : {t : U} → t ⟷ t
  _◎_     : {t₁ t₂ t₃ : U} → (t₁ ⟷ t₂) → (t₂ ⟷ t₃) → (t₁ ⟷ t₃)
  _⊕_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (PLUS t₁ t₂ ⟷ PLUS t₃ t₄)
  _⊗_     : {t₁ t₂ t₃ t₄ : U} →
            (t₁ ⟷ t₃) → (t₂ ⟷ t₄) → (TIMES t₁ t₂ ⟷ TIMES t₃ t₄)

  -}
peval : {t₁ t₂ : U′} → (t₁ ⟷′ t₂) → ⟦ t₁ ⟧′ → ⟦ t₂ ⟧′
peval (lift c) v = eval c v
peval unite₊l (inj₂ y) = y
