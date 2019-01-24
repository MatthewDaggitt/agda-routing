module RoutingLib.lmv34.Playground.Exercises2 where
  import RoutingLib.lmv34.Playground.AgdaBasics
  open RoutingLib.lmv34.Playground.AgdaBasics

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

  lem-!-tab : forall {A n} (f : Fin n -> A) (i : Fin n) ->
              ((tabulate f) ! i) == f i
  lem-!-tab f fzero = refl
  lem-!-tab f (fsuc j) = lem-!-tab (f ∘ fsuc) j

  lem-tab-! : forall {A n} (xs : Vec A n) -> tabulate (_!_ xs) == xs
  lem-tab-! [] = refl
  lem-tab-! (x :: xs) = cong (λ xs' -> x :: xs') (lem-tab-! xs)

  -- Exercise 2.3
  ⊆-refl : {A : Set}{xs : List A} -> xs ⊆ xs
  ⊆-refl {xs = []} = stop
  ⊆-refl {xs = x :: xs} = keep ⊆-refl

  ⊆-trans : {A : Set}{xs ys zs : List A} -> xs ⊆ ys -> ys ⊆ zs -> xs ⊆ zs
  ⊆-trans stop stop = stop
  ⊆-trans stop (drop q) = drop q
  ⊆-trans (drop p) (drop q) = drop (⊆-trans (drop p) q)
  ⊆-trans (keep p) (drop q) = drop (⊆-trans (keep p) q)
  ⊆-trans (drop p) (keep q) = drop (⊆-trans p q)
  ⊆-trans (keep p) (keep q) = keep (⊆-trans p q)

  data SubList {A : Set} : List A -> Set where
    []   : SubList []
    _::_ : forall x {xs} -> SubList xs -> SubList (x :: xs)
    skip : forall {x xs} -> SubList xs -> SubList (x :: xs)

  forget : {A : Set} {xs : List A} -> SubList xs -> List A
  forget {xs = xs} s = xs

  lem-forget : {A : Set} {xs : List A} (zs : SubList xs) ->
               forget zs ⊆ xs
  lem-forget [] = stop
  lem-forget (x :: zs) = keep (lem-forget zs)
  lem-forget (skip zs) = keep (lem-forget zs)

  filter' : {A : Set} -> (A -> Bool) -> (xs : List A) -> SubList xs
  filter' p [] = []
  filter' p (x :: xs) with p x
  ... | true = x :: (filter' p xs)
  ... | false = skip (filter' p xs)
