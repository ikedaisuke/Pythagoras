module Corollary where

open import Algebra
import Algebra.FunctionProperties as FunctionProperties
open import Algebra.Structures
open FunctionProperties
open import Data.Nat
open import Data.Nat.Properties
open import Level
open import Relation.Binary.Core

import Cancel
open Cancel {_} {_} {ℕ} (_≡_)
open import CancelativeAbelianMonoid

open IsCommutativeSemiring

-- cancel : Cancel _*_
-- cancel = {!!}
-- can prove by induction, commutative, distributive, etc.
postulate cancel : Cancel _*_

isCancelativeAbelianMonoid : 
  IsCancelativeAbelianMonoid _≡_ _*_ 1
isCancelativeAbelianMonoid
  = record {
      isCommutativeMonoid = *-isCommutativeMonoid isCommutativeSemiring
    ; cancel = cancel 
    }

m : CancelativeAbelianMonoid Level.zero Level.zero
m = record {
      Carrier = ℕ
    ; _≈_ = _≡_
    ; _∙_ = _*_
    ; ε   = 1
    ; isCancelativeAbelianMonoid = isCancelativeAbelianMonoid
    }

open import Noether
import Property
open Property Level.zero Level.zero m
import Theorem 
open Theorem Level.zero m

-- lemma1 : 2 isPrime
-- lemma1 = {!!}
postulate lemma1 : 2 isPrime

-- lemma2 : Noether Carrier (multiple 2)
-- lemma2 = {!!}
postulate lemma2 : Noether Carrier (multiple 2)

corollary : 2 isNotSquare
corollary = theorem 2 lemma1 lemma2

