module RoutingLib.lmv34.Playground.EvenOrOdd where

open import Data.Nat

data Even : ℕ → Set where
  evenZero : Even 0
  evenSuc  : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  oddOne : Odd 1
  oddSuc : {n : ℕ} → Odd n → Odd (suc (suc n))

_o+o_ : {n m : ℕ} → Odd n → Odd m → Even (n + m)
oddOne o+o oddOne = evenSuc evenZero
oddOne o+o oddSuc b = evenSuc (oddOne o+o b)
oddSuc a o+o b = evenSuc (a o+o b)

data EvenOrOdd : ℕ → Set where
  EvenNum : {n : ℕ} → Even n → EvenOrOdd n
  OddNum  : {n : ℕ} → Odd n  → EvenOrOdd n

toEvenOrOdd : (n : ℕ) → EvenOrOdd n
toEvenOrOdd zero = EvenNum evenZero
toEvenOrOdd (suc zero) = OddNum oddOne
toEvenOrOdd (suc (suc n)) with (toEvenOrOdd n)
... | EvenNum e = EvenNum (evenSuc e)
... | OddNum o  = OddNum (oddSuc o)
