module CancelativeAbelianMonoid where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.Structures
open FunctionProperties
open import Level
open import Relation.Binary
open import Cancel

record IsCancelativeAbelianMonoid 
         {a l} {A : Set a} (≈ : Rel A l) (_∙_ : Op₂ A)
         (ε : A) : Set (a ⊔ l) where
  open FunctionProperties ≈
  field
    isCommutativeMonoid : IsCommutativeMonoid ≈ _∙_ ε
    cancel : Cancel ≈ _∙_

  open IsCommutativeMonoid isCommutativeMonoid public

record CancelativeAbelianMonoid c l : Set (suc (c ⊔ l)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier l
    _∙_     : Op₂ Carrier
    ε       : Carrier
    isCancelativeAbelianMonoid : IsCancelativeAbelianMonoid _≈_ _∙_ ε

  open IsCancelativeAbelianMonoid isCancelativeAbelianMonoid public

  commutativeMonoid : CommutativeMonoid c l
  commutativeMonoid 
    = record { isCommutativeMonoid = isCommutativeMonoid }

  open CommutativeMonoid commutativeMonoid public 
    using (setoid; semigroup; rawMonoid; monoid)

