------------------------------------------------------------------------
-- The Agda standard library
--
-- Strongly Finite definition 
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible  #-}

module Relation.Nullary.StronglyFinite where

  open import Data.Fin.Base using (Fin; zero; suc; toℕ)
  open import Data.Nat.Base using (ℕ; zero; suc; _≤_)
  open import Level using (Level)
  open import Function.Bundles using (_↔_; Inverse)
  -- open import Function.Inverse using (_↔_; inverse; Inverse)
  open import Data.List.Base as List
  open import Function.Base using (_∘_; id)
  open import Data.Vec.Base as Vec using (Vec; tabulate)
  open import Data.Vec.Functional as Vector using (Vector; fromVec; []; _∷_)
  open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym)
  open import Data.Product.Base using (Σ; _×_; _,_)
  open import Data.Empty using (⊥)
  open import Data.Bool

  -- open import Function.Inverse as FuncInv using (inverse; ↔_)

  open Relation.Binary.PropositionalEquality.Core.≡-Reasoning
 

  record IsStronglyFinite {a : Level} (A : Set a) (n : ℕ) : Set a where 
      field
        enum : Fin n ↔ A


  record StronglyFinite  {a : Level} (A : Set a) (n : ℕ) : Set a  where
       field         
         isFinite : IsStronglyFinite A n

  open IsStronglyFinite
  open StronglyFinite 


------List----------------------------------------------------------------------

  toList : {A : Set} {n : ℕ} -> IsStronglyFinite A n -> List A
  toList  fin = List.tabulate (Inverse.to (enum fin))

  thm₁ : {A : Set} {n : ℕ} → (fin : IsStronglyFinite A n)
       → ∀ (a : A) →
       let l = toList fin ; len = List.length l in
       n ≡ len  × Σ (Fin len)  (λ i → (a ≡ List.lookup (l) i))
  thm₁ {n = zero} f0 a with Inverse.from (enum f0) a
  ... | ()
  thm₁ {n = suc n} = {!!}


------Vec--from Data.Vec.Base---------------------------------------------------------------------

  toVec :  {A : Set} {n : ℕ} -> IsStronglyFinite A n -> Vec.Vec A n
  toVec fin = Vec.tabulate  (Inverse.to (enum fin))





  thm : {A : Set} {n : ℕ} → (fin : IsStronglyFinite A n)
        → ∀ (a : A)
        → Σ (Fin n) (λ i → (a ≡ Vec.lookup (toVec fin) i))
  thm {_} {n=n} fin a =
    let  i = (Inverse.from (enum fin) a); j = toℕ i;  es = toVec fin ; k = Vec.lookup es i
    in i , sym ( ({!!}) )


-----Vector-----from Data.Vexc.Functional--------------------------------------------------------

  toVector : {A : Set} {n : ℕ} -> IsStronglyFinite A n -> Vector A n
  toVector fin = Inverse.to (enum fin)


  thm₃ : {A : Set} {n : ℕ} → (fin : IsStronglyFinite A n)
        → ∀ (a : A) → Σ (Fin n) (λ i → (a ≡ (toVector fin) i))
  thm₃ {n = n} fin a =
    let i = Inverse.from (enum fin) a; vi = (toVector fin) i; w = toℕ i
    -- in i , {sym (Inverse.to°from fin .a))!}  --pr a (enum fin)
    in  i , sym (Inverse.inverseˡ (enum fin) a )


{-  sym (begin
                 (toVector fin) i
                ≡⟨⟩
                 (Inverse.to (enum fin)) i
                ≡⟨⟩
                 (Inverse.to (enum fin)) (Inverse.from (enum fin) a)
                ≡⟨ Inverse.inverseˡ (enum fin) a ⟩
                  a
                ∎)
-}

