open import Relation.Binary using (DecSetoid; Rel; Decidable; Reflexive; Transitive; Symmetric; _Respects_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong) renaming (refl to ≡-refl)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using () renaming (Decidable to Decidableᵤ)
open import Data.Product using (Σ; ∃; _,_; _×_; proj₁)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Any using (here; there)
open import Data.List.All using ([]; _∷_; map)
open import Data.List.All.Properties using (¬Any⇒All¬; All¬⇒¬Any)
open import Data.Nat using (_≤_; _<_; suc)
open import Data.Nat.Properties using (≤-step; ≤-refl)
open import Algebra.FunctionProperties using (Op₂)
open import Function using (_∘_)

open import RoutingLib.Data.List using (dfilter)
open import RoutingLib.Data.List.Properties using (|dfilter[xs]|≤|xs|)
open import RoutingLib.Data.List.All using ([]; _∷_)
open import RoutingLib.Data.List.Uniqueness using (Unique)

module RoutingLib.Data.List.Uniset.Properties {c ℓ} (DS : DecSetoid c ℓ) where
  
  open DecSetoid DS renaming (Carrier to A; setoid to S)
  open import Data.List.Any.Membership S using () renaming (_∈_ to _∈ₗ_)
  open import Data.List.Any.Membership.Properties
  open import RoutingLib.Data.List.Uniqueness.Properties using (dfilter!⁺)
  open import RoutingLib.Data.List.Uniset DS

  private

    _≉_ : Rel A ℓ
    x ≉ y = ¬ (x ≈ y)

    _∈ₗ?_ : Decidable _∈ₗ_
    _∈ₗ?_ = ∈-dec S _≟_

    x≉-resp-≈ : ∀ x → (x ≉_) Respects _≈_
    x≉-resp-≈ x z≈y x≉z x≈y = x≉z (trans x≈y (sym z≈y))

    count≡0 : ∀ {x xs xs!} → x ∉ (xs , xs!) → length (dfilter (x ≟_) xs) ≡ 0
    count≡0 {x} {[]} x∉xs = ≡-refl
    count≡0 {x} {y ∷ xs} {_ ∷ xs!} x∉xs with x ≟ y
    ... | no  _   = count≡0 {xs! = xs!} (x∉xs ∘ there)
    ... | yes x≈y = contradiction (here x≈y) x∉xs

    count≡1 : ∀ {x xs xs!} → x ∈ (xs , xs!) → length (dfilter (x ≟_) xs) ≡ 1
    count≡1 {_} {[]} ()
    count≡1 {x} {y ∷ xs} {x∉xs ∷ xs!} x∈ with x ≟ y | x∈
    ... | yes x≈y | _          = cong suc (count≡0 {xs! = xs!} (All¬→¬Any (map (λ y≉z x≈z → y≉z (trans (sym x≈y) x≈z)) x∉xs)))
    ... | no  x≉y | here x≈y   = contradiction x≈y x≉y
    ... | no  _   | there x∈xs = count≡1 {xs! = xs!} x∈xs




  -- Empty set

  ∉∅ : ∀ {x} → x ∉ ∅
  ∉∅ ()


  -- Filtering

  ∈-filter : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) → P Respects _≈_ → ∀ {x} → P x → ∀ X → x ∈ X → x ∈ filter P? X
  ∈-filter P? resp Px X x∈X = ∈-dfilter S P? resp Px x∈X

  ∉-filter₁ : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) → ∀ {x X} → x ∉ X → x ∉ filter P? X
  ∉-filter₁ P? x∉X = ∉-dfilter₁ S P? x∉X

  ∉-filter₂ : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) → P Respects _≈_ → ∀ {x} → ¬ P x → ∀ X → x ∉ filter P? X
  ∉-filter₂ P? resp ¬Px X = ∉-dfilter₂ S P? resp ¬Px (proj₁ X)

  |filterX|≤|X| : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) X → size (filter P? X) ≤ size X
  |filterX|≤|X| P? (xs , _)  = |dfilter[xs]|≤|xs| P? xs

{-
  filter-size₂ : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) X {x} → x ∈ X → ¬ P x → size (filter P? X) < size X
  filter-size₂ P? (xs , xs!) = {!!}
-}

  ⊆-filter₁ : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) X → filter P? X ⊆ X
  ⊆-filter₁ P? ([] , xs!) ()
  ⊆-filter₁ P? (x ∷ xs , _ ∷ xs!) x∈fX with P? x
  ... | no  _ = there (⊆-filter₁ P? (xs , xs!) x∈fX)
  ... | yes _ with x∈fX
  ...   | here ≈     = here ≈
  ...   | there x∈xs = there (⊆-filter₁ P? (xs , xs!) x∈xs)

  ⊆-filter₂ : ∀ {p} {P : A → Set p} (P? : Decidableᵤ P) 
                {q} {Q : A → Set q} (Q? : Decidableᵤ Q)
                → (∀ {x} → P x → Q x) 
                → ∀ X → filter P? X ⊆ filter Q? X
  ⊆-filter₂ P? Q? P⇒Q (xs , _) x∈fₚX = ⊆-dfilter S P? Q? P⇒Q xs x∈fₚX


  -- Addition

  ∈-add₁ : ∀ x X → x ∈ add x X
  ∈-add₁ x (xs , xs!) with x ∈ₗ? xs
  ... | yes x∈xs = x∈xs
  ... | no  x∉xs = here refl

  ∈-add₂ : ∀ y {x X} → x ∈ X → x ∈ add y X
  ∈-add₂ y {X = xs , _} x∈X with y ∈ₗ? xs
  ... | yes _ = x∈X
  ... | no  _ = there x∈X

  add-size₁ : ∀ x X → size X ≤ size (add x X)
  add-size₁ x (xs , xs!) with x ∈ₗ? xs
  ... | yes _ = ≤-refl
  ... | no  _ = ≤-step ≤-refl
  
  add-size₂ : ∀ x X → x ∉ X → size (add x X) ≡ suc (size X)
  add-size₂ x (xs , xs!) x∉X with x ∈ₗ? xs
  ... | yes x∈X = contradiction x∈X x∉X
  ... | no  _   = ≡-refl

  add-size₃ : ∀ x X → x ∉ X → size X < size (add x X)
  add-size₃ x (xs , xs!) x∉X with x ∈ₗ? xs
  ... | yes x∈X = contradiction x∈X x∉X
  ... | no  _   = ≤-refl

  add-size₄ : ∀ x X → x ∈ X → size (add x X) ≡ size X
  add-size₄ x (xs , xs!) x∈X with x ∈ₗ? xs
  ... | yes _   = ≡-refl
  ... | no  x∉X = contradiction x∈X x∉X


  -- Removal

  ∈-remove : ∀ y {x X} → x ∈ X → y ≉ x → x ∈ remove y X
  ∈-remove y {x} {X} x∈X x≉y = ∈-filter _ (x≉-resp-≈ y) x≉y X x∈X

  ∉-remove₁ : ∀ y {x X} → x ∉ X → x ∉ remove y X
  ∉-remove₁ y {X = X} x∉X = ∉-filter₁ _ {X = X} x∉X

  ∉-remove₂ : ∀ x X → x ∉ remove x X
  ∉-remove₂ x X = ∉-filter₂ _ (x≉-resp-≈ x) (λ x≉x → x≉x refl) X


  |X/x|≤|X| : ∀ x X → size (remove x X) ≤ size X
  |X/x|≤|X| x X = |filterX|≤|X| _ X


  -- Subset

  ∅⊆X : ∀ X → ∅ ⊆ X
  ∅⊆X _ ()

  ⊆-refl : Reflexive _⊆_
  ⊆-refl x∈X = x∈X

  ⊆-trans : Transitive _⊆_
  ⊆-trans X⊆Y Y⊆Z x∈X = Y⊆Z (X⊆Y x∈X)

  --_⊆?_ : Decidable _⊆_
  --_⊆?_ X Y = {!!}


  -- Membership

  _∈?_ : Decidable _∈_
  x ∈? X = x ∈ₗ? proj₁ X

  

{-
    length-⊆ : ∀ {xs ys} → Unique S xs → xs ⊆ ys → length xs ≤ length ys
    length-⊆                    []          _     = z≤n
    length-⊆ {_}      {[]}      (_ ∷ _)     xs⊆ys = contradiction (xs⊆ys (here refl)) λ()
    length-⊆ {x ∷ xs} {y ∷ ys} (x∉xs ∷ xs!) xs⊆ys = subst (λ v → length (x ∷ xs) ≤ v) (length-remove S (xs⊆ys (here refl))) (s≤s (length-⊆ xs! (⊆-remove S (xs⊆ys ∘ there) (xs⊆ys (here refl)) (All¬→¬Any x∉xs))))


    length-⊂ : ∀ {v xs ys} → Unique S xs → xs ⊆ ys → v ∉ xs → v ∈ ys → length xs < length ys
    length-⊂               {ys = []}     _              _        _      ()
    length-⊂ {xs = []}     {ys = y ∷ ys} _              _        _      _    = s≤s z≤n
    length-⊂ {xs = x ∷ xs}               (x∉xs ∷ xs!)   x∷xs⊆ys v∉x∷xs v∈ys = subst (length (x ∷ xs) <_) (length-remove S (x∷xs⊆ys (here refl))) (s≤s (length-⊂ xs! (⊆-remove S (x∷xs⊆ys ∘ there) (x∷xs⊆ys (here refl)) (All¬→¬Any x∉xs)) (λ v∈xs → v∉x∷xs (there v∈xs)) (∈-remove S (x∷xs⊆ys (here refl)) v∈ys (λ x≈v → v∉x∷xs (∈-resp-≈ S (here refl) x≈v))) ))

    length-⊆-⊇ : ∀ {xs ys} → Unique S xs → Unique S ys → xs ⊆ ys → ys ⊆ xs → length xs ≡ length ys
    length-⊆-⊇ xs! ys! xs⊆ys ys⊆xs = ≤-antisym (length-⊆ xs! xs⊆ys) (length-⊆ ys! ys⊆xs)
-}
