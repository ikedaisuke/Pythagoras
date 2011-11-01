module Noether where

{-
The original proof is written by Thierry Coquand.
http://www.cs.ru.nl/~freek/comparison/comparison.pdf
-}

open import Level
open import Relation.Binary.Core
open import Relation.Unary

Noether : ∀ {a l} -> (A : Set a) -> (R : Rel A l) -> Set (a ⊔ suc l)
Noether {_} {l} A R 
  = (P : Pred A l) -> (x : A) -> 
    ((y : A) -> (R y x -> P y) -> P x) -> (z : A) -> (P z)
