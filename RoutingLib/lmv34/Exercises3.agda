module RoutingLib.lmv34.Exercises3 where
  import RoutingLib.lmv34.Exercises2
  open RoutingLib.lmv34.Exercises2
  import RoutingLib.lmv34.AgdaBasics
  open RoutingLib.lmv34.AgdaBasics

  isFalse : Bool → Set
  isFalse true = False
  isFalse false = True

  -- Exerise 3.1
  data Compare : Nat -> Nat -> Set where
    less : forall {n} k -> Compare n (n + suc k)
    more : forall {n} k -> Compare (n + suc k) n
    same : forall {n}   -> Compare n n

  compare : (n m : Nat) -> Compare n m
  compare zero zero = same
  compare zero (suc m) = less m
  compare (suc n) zero = more n
  compare (suc n) (suc m) with compare n m
  ... | less k = less k
  ... | more k = more k
  ... | same   = same

  difference : Nat -> Nat -> Nat
  difference n m with compare n m
  ... | less k = (suc k)
  ... | more k = (suc k)
  ... | same   = zero

  --Exercise 3.2
  infixr 30 _⇒_
  data Type : Set where
    ₁   : Type
    _⇒_ : Type → Type → Type

  data _≠_ : Type → Type → Set where
    unitVSfun : forall {σ τ} → ₁     ≠ σ ⇒ τ
    funVSunit : forall {σ τ} → σ ⇒ τ ≠ ₁
    leftFun   : forall {σ₁ σ₂ τ} → σ₁ ≠ σ₂ → σ₁ ⇒ τ ≠ σ₂ ⇒ τ
    rightFun  : forall {σ τ₁ τ₂} → τ₁ ≠ τ₂ → σ ⇒ τ₁ ≠ σ ⇒ τ₂
    allFun    : forall {σ₁ σ₂ τ₁ τ₂} → σ₁ ≠ σ₂ → τ₁ ≠ τ₂ → σ₁ ⇒ τ₁ ≠ σ₂ ⇒ τ₂

  data Equal? : Type -> Type -> Set where
    yes : forall {τ}   → Equal? τ τ
    no  : forall {σ τ} → σ ≠ τ  → Equal? σ τ 

  _=?=_ : (σ τ : Type) -> Equal? σ τ
  ₁ =?= ₁ = yes
  (_ ⇒ _) =?= ₁ = no funVSunit
  ₁ =?= (_ ⇒ _) = no unitVSfun
  (σ₁ ⇒ τ₁) =?= (σ₂ ⇒ τ₂) with σ₁ =?= σ₂ | τ₁ =?= τ₂
  ... | yes  | yes  = yes
  ... | no p | yes  = no (leftFun p)
  ... | yes  | no q = no (rightFun q)
  ... | no p | no q = no (allFun p q)

  -- Exercise 3.3
  data _∈_ {A : Set}(x : A) : List A → Set where
    hd : forall {xs} → x ∈ x :: xs
    tl : forall {y xs} → x ∈ xs → x ∈ y :: xs

  infixr 30 _::₁_
  data All {A : Set}(P : A → Set) : List A → Set where
    []   : All P []
    _::₁_ : forall {x xs} → P x → All P xs → All P (x :: xs)

  lemma-All-∈ : forall {A x xs}{P : A → Set} →
                All P xs → x ∈ xs → P x
  lemma-All-∈ [] ()
  lemma-All-∈ (p ::₁ a) hd = p
  lemma-All-∈ (p ::₁ a) (tl i) = lemma-All-∈ a i

  satisfies : {A : Set} → (A → Bool) → A → Set
  satisfies p x = isTrue (p x)

  data Inspect {A : Set}(x : A) : Set where
    it : (y : A) → x == y → Inspect x

  inspect : {A : Set}(x : A) → Inspect x
  inspect x = it x refl

  trueIsTrue : {x : Bool} -> x == true -> isTrue x
  trueIsTrue refl = _

  falseIsFalse : {x : Bool} → x == false → isFalse x
  falseIsFalse refl = _

  lem-filter-sound : {A : Set}(p : A → Bool)(xs : List A) →
                       All (satisfies p) (filter p xs)
  lem-filter-sound p [] = []
  lem-filter-sound p (x :: xs) with inspect (p x)
  lem-filter-sound p (x :: xs) | it y prf      with p x | prf
  lem-filter-sound p (x :: xs) | it .true prf  | true   | refl = trueIsTrue prf ::₁ lem-filter-sound p xs
  lem-filter-sound p (x :: xs) | it .false prf | false  | refl = lem-filter-sound p xs
  
  lem-filter-complete : {A : Set}(p : A → Bool)(x : A){xs : List A} →
                        x ∈ xs → satisfies p x → x ∈ filter p xs
  lem-filter-complete p x {[]} el px = el
  lem-filter-complete p x {x₁ :: xs} el px with inspect (p x)
  lem-filter-complete p x {x₁ :: xs} el px | it y x₂ = {!!}
