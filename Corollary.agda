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

+-comm : Commutative _≡_ _+_
+-comm one n = {!!} -- succ n ≡ n + one
+-comm (succ m) n = {!!}

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

*-one : ∀ n -> n * one ≡ n
*-one one = refl
*-one (succ m) = cong succ (*-one m)

m*1+n≡m+mn : ∀ m n → m * succ n ≡ m + m * n
m*1+n≡m+mn one n = refl
m*1+n≡m+mn (succ m) n = begin
  succ (n + m * succ n)  ≡⟨ refl ⟩
  succ n + m * succ n    ≡⟨ cong (λ x → succ n + x) (m*1+n≡m+mn m n) ⟩
  succ n + (m + m * n)   ≡⟨ refl ⟩
  succ (n + (m + m * n)) ≡⟨ cong succ (sym $ +-assoc n m (m * n)) ⟩
  succ (n + m + m * n)   ≡⟨ cong (λ x → succ (x + m * n)) (+-comm n m) ⟩
  succ (m + n + m * n)   ≡⟨ cong succ (+-assoc m n (m * n)) ⟩
  succ (m + (n + m * n)) ≡⟨ refl ⟩
  succ (m + (n + m * n))
  ∎

*-comm  : Commutative _≡_ _*_
*-comm one n = sym (*-one n)
*-comm (succ m) n = begin
  n + m * n ≡⟨ cong (λ x → n + x) (*-comm m n) ⟩
  n + n * m ≡⟨ sym (m*1+n≡m+mn n m) ⟩
  n * succ m
  ∎

-- postulate *-comm  : Commutative _≡_ _*_
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
-- can be proved by induction, commutative, distributive, etc.
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

