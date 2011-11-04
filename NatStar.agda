module NatStar where

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

