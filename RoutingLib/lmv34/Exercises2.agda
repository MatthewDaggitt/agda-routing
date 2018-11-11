module Exercises2 where
  import AgdaBasics
  open AgdaBasics

  -- Exercise 2.1
  data Fin : Nat -> Set where
    fzero : {n : Nat} -> Fin (suc n)
    fsuc  : {n : Nat} -> Fin n -> Fin (suc n)

  _!_ : {n : Nat}{A : Set} -> Vec A n -> Fin n -> A
  []        ! ()
  (x :: xs) ! fzero    = x
  (x :: xs) ! (fsuc i) = xs ! i

  Matrix : Set -> Nat -> Nat -> Set
  Matrix A m n = Vec (Vec A m) n

  vec : {n : Nat}{A : Set} -> A -> Vec A n
  vec {zero} x = []
  vec {suc m} x = x :: (vec {m} x)

  head : {n : Nat}{A : Set} -> Vec A (suc n) -> A
  head (x :: xs) = x

  tail : {n : Nat}{A : Set} -> Vec A (suc n) -> Vec A n
  tail (x :: xs) = xs

  infixl 90 _$_
  _$_ : {n : Nat}{A B : Set} -> Vec (A -> B) n -> Vec A n -> Vec B n
  [] $ [] = []
  (f :: fs) $ (x :: xs) = f x :: fs $ xs

  transpose : forall {A m n} -> Matrix A m n -> Matrix A n m
  transpose {A} {zero} {n} xss = [] 
  transpose {A} {suc m} {n} xss = ((vec {n} head) $ xss) :: (transpose ((vec {n} tail) $ xss))

  M : Matrix Nat (suc (suc zero)) (suc (suc zero))
  M = ((suc zero) :: (suc (suc zero)) :: []) :: ((suc (suc (suc zero))) :: (suc (suc (suc (suc zero)))) :: []) :: []

  -- Exercise 2.2

  _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> (A -> C)
  (f ∘ g) x = f (g x)

  tabulate : {n : Nat}{A : Set} -> (Fin n -> A) -> Vec A n
  tabulate {zero}  f = []
  tabulate {suc n} f = f fzero :: tabulate (f ∘ fsuc)

  lem-!-tab : forall {A n} (f : Fin n -> A)(i : Fin n) ->
              ((tabulate f) ! i) == f i
  lem-!-tab {A} {n} f fzero = refl
  lem-!-tab {A} {n} f (fsuc j) = lem-!-tab {A} {n} f j

  
