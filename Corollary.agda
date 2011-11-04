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

open import NatStar
open import NatStarProperties

import Cancel
open Cancel {_} {_} {NatStar} (_≡_)
open import CancellativeAbelianMonoid

-- z * x ≡ z * y → x ≡ y
{-
cancel : Cancel _*_
cancel x y one p = p
cancel one one (succ z) p = refl
cancel one (succ y) (succ z) p = {!!}
cancel (succ x) one (succ z) p = {!!}
cancel (succ x) (succ y) (succ z) p = {!!}
-}
-- can be proved by induction, commutative, distributive, etc.
postulate cancel : Cancel _*_

isCancellativeAbelianMonoid : 
  IsCancellativeAbelianMonoid _≡_ _*_ one
isCancellativeAbelianMonoid
  = record {
      isCommutativeMonoid = *-isCommutativeMonoid
    ; cancel = cancel 
    }

m : CancellativeAbelianMonoid Level.zero Level.zero
m = record {
      Carrier = NatStar
    ; _≈_ = _≡_
    ; _∙_ = _*_
    ; ε   = one
    ; isCancellativeAbelianMonoid = isCancellativeAbelianMonoid
    }

open import Noether
import Property
open Property Level.zero Level.zero m
import Theorem 
open Theorem Level.zero m

-- the original proof of 'two is prime' is written
-- by Nils Anders Danielsson
-- https://lists.chalmers.se/pipermail/agda/2011/003464.html

-- lemma1 : 2 isPrime
-- lemma1 = {!!}
postulate lemma1 : (succ one) isPrime

-- lemma2 : Noether Carrier (multiple 2)
-- lemma2 = {!!}
postulate lemma2 : Noether Carrier (multiple (succ one))

corollary : (succ one) isNotSquare
corollary = theorem (succ one) lemma1 lemma2

