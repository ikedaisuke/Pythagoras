module Corollary where

open import Algebra
open import Function
import Algebra.FunctionProperties as FunctionProperties
open FunctionProperties
open import Algebra.Structures
open import Level
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq.≡-Reasoning

data NatStar : Set where
  one  : NatStar
  succ : NatStar -> NatStar

-- copy oparators from the Agda standard library
-- Data.Nat
infixl 6 _+_

_+_ : NatStar -> NatStar -> NatStar
one + n = succ n
succ m + n = succ (m + n)

_*_ : NatStar -> NatStar -> NatStar
one * n = n
succ m * n = n + m * n

-- copy properties from the Agda standard library
-- Data.Nat.Properties

+-assoc : Associative _≡_ _+_
+-assoc one _ _ = refl
+-assoc (succ m) n o = begin
  succ m + n + o ≡⟨ cong succ (+-assoc m n o) ⟩
  succ m + (n + o)
  ∎

*-distrib-right-+ :  ∀ x y z → ((y + z) * x) ≡ ((y * x) + (z * x))
*-distrib-right-+ m one o = refl
*-distrib-right-+ m (succ n) o = begin
  (succ n + o) * m    ≡⟨ refl ⟩
  m + (n + o) * m     ≡⟨ cong (_+_ m) $ *-distrib-right-+ m n o ⟩
  m + (n * m + o * m) ≡⟨ sym $ +-assoc m (n * m) (o * m) ⟩
  m + n * m + o * m   ≡⟨ refl ⟩
  succ n * m + o * m
  ∎

*-assoc : Associative _≡_ _*_
*-assoc one n o = refl
*-assoc (succ m) n o = begin
    (succ m * n) * o    ≡⟨ refl ⟩
    (n + m * n) * o     ≡⟨ *-distrib-right-+ o n (m * n) ⟩
    n * o + (m * n) * o ≡⟨ cong (λ x → n * o + x) $ *-assoc m n o ⟩
    n * o + m * (n * o) ≡⟨ refl ⟩
    succ m * (n * o)
  ∎

postulate *-comm  : Commutative _≡_ _*_
postulate *-leftIdentity : LeftIdentity _≡_ one _*_

*-isCommutativeMonoid : IsCommutativeMonoid _≡_ _*_ one
*-isCommutativeMonoid = record 
  { isSemigroup = record
      { isEquivalence = PropEq.isEquivalence
      ; assoc         = *-assoc
      ; ∙-cong        = cong₂ _*_
      }
  ; identityˡ = *-leftIdentity
  ; comm      = *-comm
  }

import Cancel
open Cancel {_} {_} {NatStar} (_≡_)
open import CancelativeAbelianMonoid

-- cancel : Cancel _*_
-- cancel = {!!}
-- can prove by induction, commutative, distributive, etc.
postulate cancel : Cancel _*_

isCancelativeAbelianMonoid : 
  IsCancelativeAbelianMonoid _≡_ _*_ one
isCancelativeAbelianMonoid
  = record {
      isCommutativeMonoid = *-isCommutativeMonoid
    ; cancel = cancel 
    }

m : CancelativeAbelianMonoid Level.zero Level.zero
m = record {
      Carrier = NatStar
    ; _≈_ = _≡_
    ; _∙_ = _*_
    ; ε   = one
    ; isCancelativeAbelianMonoid = isCancelativeAbelianMonoid
    }

open import Noether
import Property
open Property Level.zero Level.zero m
import Theorem 
open Theorem Level.zero m

-- lemma1 : 2 isPrime
-- lemma1 = {!!}
postulate lemma1 : (succ one) isPrime

-- lemma2 : Noether Carrier (multiple 2)
-- lemma2 = {!!}
postulate lemma2 : Noether Carrier (multiple (succ one))

corollary : (succ one) isNotSquare
corollary = theorem (succ one) lemma1 lemma2

