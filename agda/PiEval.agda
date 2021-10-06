{-# OPTIONS --without-K #-}

module PiEval where

open import Data.Empty
open import Data.Unit
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)

open import PiU
open import PiLevel0

------------------------------------------------------------------------------
-- A combinator t₁ ⟷ t₂ denotes an equivalence to types
-- note how we don't have to look at the types at all.

⟦_⟧ : U → Set
⟦ ZERO ⟧        = ⊥
⟦ ONE ⟧         = ⊤
⟦ PLUS t₁ t₂ ⟧  = ⟦ t₁ ⟧ ⊎ ⟦ t₂ ⟧
⟦ TIMES t₁ t₂ ⟧ = ⟦ t₁ ⟧ × ⟦ t₂ ⟧

eval : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₁ ⟧ → ⟦ t₂ ⟧
eval unite₊l (inj₁ ())
eval unite₊l (inj₂ v) = v
eval uniti₊l v = inj₂ v
eval unite₊r (inj₁ x) = x
eval unite₊r (inj₂ ())
eval uniti₊r v = inj₁ v
eval swap₊ (inj₁ v) = inj₂ v
eval swap₊ (inj₂ v) = inj₁ v
eval assocl₊ (inj₁ v) = inj₁ (inj₁ v)
eval assocl₊ (inj₂ (inj₁ v)) = inj₁ (inj₂ v)
eval assocl₊ (inj₂ (inj₂ v)) = inj₂ v
eval assocr₊ (inj₁ (inj₁ v)) = inj₁ v
eval assocr₊ (inj₁ (inj₂ v)) = inj₂ (inj₁ v)
eval assocr₊ (inj₂ v) = inj₂ (inj₂ v)
eval unite⋆l (tt , v) = v
eval uniti⋆l v = (tt , v)
eval unite⋆r (v , tt) = v
eval uniti⋆r v = v , tt
eval swap⋆ (v₁ , v₂) = (v₂ , v₁)
eval assocl⋆ (v₁ , (v₂ , v₃)) = ((v₁ , v₂) , v₃)
eval assocr⋆ ((v₁ , v₂) , v₃) = (v₁ , (v₂ , v₃))
eval absorbr (x , _) = x
eval absorbl (_ , y) = y
eval factorzl ()
eval factorzr ()
eval dist (inj₁ v₁ , v₃) = inj₁ (v₁ , v₃)
eval dist (inj₂ v₂ , v₃) = inj₂ (v₂ , v₃)
eval factor (inj₁ (v₁ , v₃)) = (inj₁ v₁ , v₃)
eval factor (inj₂ (v₂ , v₃)) = (inj₂ v₂ , v₃)
eval distl (v , inj₁ x) = inj₁ (v , x)
eval distl (v , inj₂ y) = inj₂ (v , y)
eval factorl (inj₁ (x , y)) = x , inj₁ y
eval factorl (inj₂ (x , y)) = x , inj₂ y
eval id⟷ v = v
eval (c₁ ◎ c₂) v = eval c₂ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₁ v) = inj₁ (eval c₁ v)
eval (c₁ ⊕ c₂) (inj₂ v) = inj₂ (eval c₂ v)
eval (c₁ ⊗ c₂) (v₁ , v₂) = (eval c₁ v₁ , eval c₂ v₂)

-- useful to have the backwards eval too

evalB : {t₁ t₂ : U} → (t₁ ⟷ t₂) → ⟦ t₂ ⟧ → ⟦ t₁ ⟧
evalB unite₊l x = inj₂ x
evalB uniti₊l (inj₁ ())
evalB uniti₊l (inj₂ y) = y
evalB unite₊r v = inj₁ v
evalB uniti₊r (inj₁ x) = x
evalB uniti₊r (inj₂ ())
evalB swap₊ (inj₁ x) = inj₂ x
evalB swap₊ (inj₂ y) = inj₁ y
evalB assocl₊ (inj₁ (inj₁ x)) = inj₁ x
evalB assocl₊ (inj₁ (inj₂ y)) = inj₂ (inj₁ y)
evalB assocl₊ (inj₂ y) = inj₂ (inj₂ y)
evalB assocr₊ (inj₁ x) = inj₁ (inj₁ x)
evalB assocr₊ (inj₂ (inj₁ x)) = inj₁ (inj₂ x)
evalB assocr₊ (inj₂ (inj₂ y)) = inj₂ y
evalB unite⋆l x = tt , x
evalB uniti⋆l (tt , x) = x
evalB unite⋆r v = v , tt
evalB uniti⋆r (v , tt) = v
evalB swap⋆ (x , y) = y , x
evalB assocl⋆ ((x , y) , z) = x , y , z
evalB assocr⋆ (x , y , z) = (x , y) , z
evalB absorbr ()
evalB absorbl ()
evalB factorzr (_ , x) = x
evalB factorzl (x , _) = x
evalB dist (inj₁ (x , y)) = inj₁ x , y
evalB dist (inj₂ (x , y)) = inj₂ x , y
evalB factor (inj₁ x , z) = inj₁ (x , z)
evalB factor (inj₂ y , z) = inj₂ (y , z)
evalB distl (inj₁ (x , y)) = x , inj₁ y
evalB distl (inj₂ (x , y)) = x , inj₂ y
evalB factorl (v , inj₁ x) = inj₁ (v , x)
evalB factorl (v , inj₂ y) = inj₂ (v , y)
evalB id⟷ x = x
evalB (c₀ ◎ c₁) x = evalB c₀ (evalB c₁ x)
evalB (c₀ ⊕ c₁) (inj₁ x) = inj₁ (evalB c₀ x)
evalB (c₀ ⊕ c₁) (inj₂ y) = inj₂ (evalB c₁ y)
evalB (c₀ ⊗ c₁) (x , y) = evalB c₀ x , evalB c₁ y
