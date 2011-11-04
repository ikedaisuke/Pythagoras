module NatStarProperties where

open import Function
open import Algebra.FunctionProperties
open import Algebra.Structures
open import Relation.Binary.Core
open import Relation.Binary.PropositionalEquality
  as PropEq
open PropEq.≡-Reasoning

open import NatStar

-- copy properties from the Agda standard library
-- Data.Nat.Properties

+-assoc : Associative _≡_ _+_
+-assoc one _ _ = refl
+-assoc (succ m) n o = begin
  succ m + n + o ≡⟨ cong succ (+-assoc m n o) ⟩
  succ m + (n + o)
  ∎

m+1+n≡1+m+n : ∀ m n → m + succ n ≡ succ (m + n)
m+1+n≡1+m+n one n = refl
m+1+n≡1+m+n (succ m) n = cong succ (m+1+n≡1+m+n m n)

+-comm : Commutative _≡_ _+_
+-comm one one = refl
+-comm one (succ n) = sym (cong succ (+-comm n one))
+-comm (succ m) n = begin
  succ (m + n) ≡⟨ cong succ (+-comm m n) ⟩
  succ (n + m) ≡⟨ sym (m+1+n≡1+m+n n m) ⟩
  n + succ m
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

*-leftIdentity : LeftIdentity _≡_ one _*_
*-leftIdentity x = refl

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
