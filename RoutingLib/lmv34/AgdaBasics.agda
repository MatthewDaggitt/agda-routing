module RoutingLib.lmv34.AgdaBasics where

  data Bool : Set where
    true  : Bool
    false : Bool

  not : Bool -> Bool
  not true  = false
  not false = true

  data Nat : Set where
    zero : Nat
    suc  : Nat -> Nat

  _+_ : Nat -> Nat -> Nat
  zero  + m = m
  suc n + m = suc (n + m)

  _*_ : Nat -> Nat -> Nat
  zero  * m = zero
  suc n * m = m + (n * m)

  infixr 40 _::_
  data List (A : Set) : Set where
    []   : List A
    _::_ : A -> List A -> List A

  identity : (A : Set) -> A -> A
  identity A x = x

  apply : (A : Set)(B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
  apply A B f a = f a

  id : {A : Set} -> A -> A
  id x = x

  map : {A B : Set} -> (A -> B) -> List A -> List B
  map f []        = []
  map f (x :: xs) = f x :: map f xs

  _++_ : {A : Set} -> List A -> List A -> List A
  []        ++ ys = ys
  (x :: xs) ++ ys = x :: (xs ++ ys)

  data Vec (A : Set) : Nat -> Set where
    []   : Vec A zero
    _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)
    
  data   False : Set where
  record True  : Set where

  trivial : True
  trivial = _

  isTrue : Bool -> Set
  isTrue true  = True
  isTrue false = False

  _<_ : Nat -> Nat -> Bool
  _     < zero  = false
  zero  < suc n = true
  suc m < suc n = m < n

  length : {A : Set} -> List A -> Nat
  length []        = zero
  length (x :: xs) = suc (length xs)

  lookup : {A : Set}(xs : List A)(n : Nat) ->
           isTrue (n < length xs) -> A
  lookup []        n       ()
  lookup (x :: xs) zero    p = x
  lookup (x :: xs) (suc n) p = lookup xs n p

  data _==_ {A : Set}(x : A) : A -> Set where
    refl : x == x

  sym : {A : Set} -> {a b : A} ->
        a == b -> b == a
  sym refl = refl

  trans : {A : Set} -> {a b c : A} ->
        a == b -> b == c -> a == c
  trans refl refl = refl

  cong : {A B : Set} -> {a a' : A} ->
        (f : A -> B) -> (a == a') -> (f a == f a')
  cong f refl = refl

  sym-inv-lemma : {A : Set} -> {a b : A} ->
        (p : a == b) -> (sym (sym p) == p)
  sym-inv-lemma refl = refl

  data _≤_ : Nat -> Nat -> Set where
    leq-zero : {n : Nat} -> zero ≤ n
    leq-suc  : {m n : Nat} -> m ≤ n -> suc m ≤ suc n

  leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
  leq-trans leq-zero _ = leq-zero
  leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)

  zeroSmallerThanOne : zero ≤ suc zero
  zeroSmallerThanOne = leq-zero

  oneSmallerThanTwo : suc zero ≤ suc (suc zero)
  oneSmallerThanTwo = leq-suc leq-zero

  zeroSmallerThanTwo : zero ≤ suc (suc zero)
  zeroSmallerThanTwo = leq-trans zeroSmallerThanOne oneSmallerThanTwo

  min : Nat -> Nat -> Nat
  min x y with x < y
  min x y | true  = x
  min x y | false = y

  filter : {A : Set} -> (A -> Bool) -> List A -> List A
  filter p [] = []
  filter p (x :: xs) with p x
  ... | true  = x :: filter p xs
  ... | false = filter p xs

  data _≠₁_ : Nat -> Nat -> Set where
    z≠s : {n : Nat} -> zero ≠₁ suc n
    s≠z : {n : Nat} -> suc n ≠₁ zero
    s≠s : {m n : Nat} -> m ≠₁ n -> suc m ≠₁ suc n

  data Equal₁? (m n : Nat) : Set where
    eq  : m == n -> Equal₁? m n
    neq : m ≠₁ n -> Equal₁? m n

  equal₁? : (m n : Nat) -> Equal₁? m n
  equal₁? zero zero    = eq refl
  equal₁? zero (suc n) = neq z≠s
  equal₁? (suc m) zero = neq s≠z
  equal₁? (suc m) (suc n)  with equal₁? m n
  equal₁? (suc m) (suc .m) | eq refl = eq refl
  equal₁? (suc m) (suc n)  | neq p   = neq (s≠s p)

  infix 20 _⊆_
  data _⊆_ {A : Set} : List A -> List A -> Set where
    stop : [] ⊆ []
    drop : forall {xs y ys} -> xs ⊆ ys -> xs ⊆ y :: ys
    keep : forall {x xs ys} -> xs ⊆ ys -> x :: xs ⊆ x :: ys

  lem-filter : {A : Set}(p : A -> Bool)(xs : List A) ->
               filter p xs ⊆ xs
  lem-filter p [] = stop
  lem-filter p (x :: xs) with p x
  ... | true = keep (lem-filter p xs)
  ... | false = drop (lem-filter p xs)
