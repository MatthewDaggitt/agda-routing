open import Level using (_⊔_)
open import Data.Nat using (zero; suc; z≤n; s≤s; _≤_; _<_)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; Eq)
open import Data.List using (List; []; _∷_; length; gfilter; filter; map; concat; _++_; drop; take)
open import Data.List.Any using (here; there; any)
open import Data.List.All using (All; []; _∷_; lookup) renaming (map to mapₐ; tabulate to tabulateₐ)
open import Data.List.All.Properties using (gmap)
open import Data.Fin using (Fin) renaming (suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_; id)
open import Relation.Binary using (Setoid; Rel)
open import Relation.Binary.PropositionalEquality using (subst; _≡_) renaming (refl to ≡-refl; setoid to ≡-setoid)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Decidable)

open import RoutingLib.Data.List
open import RoutingLib.Data.List.Membership as Membership using ()
open import RoutingLib.Data.List.Membership.Properties as MembershipP using ()
open import RoutingLib.Data.List.All using (AllPairs; []; _∷_)
open import RoutingLib.Data.List.All.Properties
open import RoutingLib.Data.Nat.Properties using (ℕₛ; ≤-antisym; <⇒≢)
open import RoutingLib.Data.Fin.Properties using (suc≢zero)
open import RoutingLib.Data.Maybe.Base
open import RoutingLib.Data.Maybe.Properties using (just-injective)
open import RoutingLib.Data.List.Uniqueness as Uniqueness using (Unique)
import RoutingLib.Data.List.Disjoint as Disjoint
import RoutingLib.Data.List.Disjoint.Properties as DisjointProperties
open import RoutingLib.Data.List.Permutation using (_⇿_)

module RoutingLib.Data.List.Uniqueness.Properties where

  module SingleSetoid {c ℓ} (S : Setoid c ℓ) where

    open Setoid S renaming (Carrier to A)
    open Membership S using (_∈_; _∉_; _⊆_; deduplicate)
    open Disjoint S using (_#_; ∈ₗ⇒∉ᵣ; contractₗ)
    open DisjointProperties S using (#-concat; #⇒AllAll≉) 
{-
    filter! : ∀ P {xs} → Unique S xs → Unique S (filter P xs)
    filter! _ [] = []
    filter! P {x ∷ xs} (x∉xs ∷ xs!) with predBoolToMaybe P x | inspect (predBoolToMaybe P) x
    ... | nothing | _  = filter! P xs!
    ... | just v  | [ t ] with P x
    ...   | false = contradiction t λ()
    ...   | true  = ¬Any→All¬ (∉-filter₁ S P (∉-resp-≈ S (All¬→¬Any x∉xs) (reflexive (just-injective t)))) ∷ filter! P xs!
-}

    deduplicate!⁺ : ∀ _≟_ xs → Unique S (deduplicate _≟_ xs)
    deduplicate!⁺ _≟_ [] = []
    deduplicate!⁺ _≟_ (x ∷ xs) with any (x ≟_) xs
    ... | yes _    = deduplicate!⁺ _≟_ xs
    ... | no  x∉xs = ¬Any⇒All¬ (x∉xs ∘ (MembershipP.∈-deduplicate⁻ S _≟_)) ∷ deduplicate!⁺ _≟_ xs
    
    dfilter!⁺ : ∀ {b} {P : A → Set b} (P? : Decidable P) → ∀ {xs} → Unique S xs → Unique S (dfilter P? xs)
    dfilter!⁺ P? xs! = AllPairs-dfilter⁺ P? xs!

    ++!⁺ : ∀ {xs ys} → Unique S xs → Unique S ys → xs # ys → Unique S (xs ++ ys)
    ++!⁺ xs! ys! xs#ys = AllPairs-++⁺ xs! ys! (#⇒AllAll≉ xs#ys)

    concat!⁺ : ∀ {xss} → All (Unique S) xss → AllPairs _#_ xss → Unique S (concat xss)
    concat!⁺  []          _                 = []
    concat!⁺ (xs! ∷ xss!) (x∷xs#xss ∷ xss#) = ++!⁺ xs! (concat!⁺ xss! xss#) (#-concat x∷xs#xss)

    tabulate! : ∀ {n} (f : Fin n → A) → (∀ {i j} → f i ≈ f j → i ≡ j) → Unique S (tabulate f)
    tabulate! {n = zero}  f _     = []
    tabulate! {n = suc n} f f-inj = All-tabulate⁺ (λ _ → suc≢zero ∘ f-inj ∘ sym) ∷ tabulate! (f ∘ fsuc) (suc-injective ∘ f-inj)

{-
    tabulate!⁺ : ∀ {n} (f : Fin n → A) → (∀ {i j} → f i ≈ f j → i ≡ j) → Unique S (tabulate f)
    tabulate!⁺ f f-inj = AllPairs-tabulate⁺ ? ?
-}

    drop!⁺ : ∀ {xs} n → Unique S xs → Unique S (drop n xs)
    drop!⁺ = AllPairs-drop⁺

    take!⁺ : ∀ {xs} n → Unique S xs → Unique S (take n xs)
    take!⁺ = AllPairs-take⁺

    
    -- Other

    perm! : ∀ {xs ys} → Unique S xs → xs ⇿ ys → Unique S ys
    perm! xs! xs⇿ys = AllPairs-⇿ (λ i≉j → i≉j ∘ sym) xs! xs⇿ys
    

  open SingleSetoid public





  module DoubleSetoid {c₁ c₂ ℓ₁ ℓ₂} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) where

    open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_)
    open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_)

    private
      _≉₁_ : Rel A₁ ℓ₁
      x ≉₁ y = ¬ x ≈₁ y

      _≉₂_ : Rel A₂ ℓ₂
      x ≉₂ y = ¬ x ≈₂ y
      
    map!⁺ : ∀ {f} → (∀ {x y} → x ≉₁ y → f x ≉₂ f y) → ∀ {xs} → Unique S₁ xs → Unique S₂ (map f xs)
    map!⁺ _     [] = []
    map!⁺ f-inj (x∉xs ∷ xs!) = gmap (λ x≉y → f-inj x≉y) x∉xs ∷ map!⁺ f-inj xs!

    gfilter!⁺ : ∀ f → (∀ {x y} → x ≉₁ y → f x ≡ nothing ⊎ f y ≡ nothing ⊎ Eq _≉₂_ (f x) (f y))
               → ∀ {xs} → Unique S₁ xs → Unique S₂ (gfilter f xs)
    gfilter!⁺ = AllPairs-gfilter⁺
    
  open DoubleSetoid public



  module TripleSetoid {c₁ c₂ c₃ ℓ₁ ℓ₂ ℓ₃} (S₁ : Setoid c₁ ℓ₁) (S₂ : Setoid c₂ ℓ₂) (S₃ : Setoid c₃ ℓ₃) where

    open Setoid S₁ renaming (Carrier to A₁; _≈_ to _≈₁_; sym to sym₁; trans to trans₁)
    open Setoid S₂ renaming (Carrier to A₂; _≈_ to _≈₂_; sym to sym₂; trans to trans₂)
    open Setoid S₃ renaming (Carrier to A₃; _≈_ to _≈₃_)
    
    open Disjoint S₃ using (_#_)
    open MembershipP using (∈-map⁻; combine-∈)

    combine!⁺ : ∀ {xs ys} f → (∀ {w x y z} → ¬ (w ≈₁ y) ⊎ ¬ (x ≈₂ z) → ¬ (f w x ≈₃ f y z)) → Unique S₁ xs → Unique S₂ ys → Unique S₃ (combine f xs ys)
    combine!⁺ _ _ [] _ = []
    combine!⁺ {x ∷ xs} {ys} f f-inj (x∉xs ∷ xs!) ys! = ++!⁺ S₃ (map!⁺ S₂ S₃ (f-inj ∘ inj₂) ys!) (combine!⁺ f f-inj xs! ys!) map#combine
      where
      
      pres : ∀ {a} {b} → a ≈₁ b → ¬ (x ≈₁ a) → ¬ (x ≈₁ b)
      pres a≈b x≉a x≈b = x≉a (trans₁ x≈b (sym₁ a≈b))

      map#combine : map (f x) ys # combine f xs ys
      map#combine (v∈map , v∈com) with ∈-map⁻ S₂ S₃ v∈map | combine-∈ S₁ S₂ S₃ f xs ys v∈com
      ... | (c , _ , v≈fxc) | (a , b , a∈xs , _ , v≈fab) = contradiction (trans (sym v≈fxc) v≈fab) (f-inj (inj₁ (All-∈ S₁ pres x∉xs a∈xs)))
 
  open TripleSetoid public

  

  upTo!⁺ : ∀ n → Unique ℕₛ (upTo n)
  upTo!⁺ n = AllPairs-applyUpTo⁺₁ id n (λ i<j _ → <⇒≢ i<j)

  between!⁺ : ∀ s e → Unique ℕₛ (between s e)
  between!⁺ s e = AllPairs-applyBetween⁺₁ id s e (λ _ i<j _ → <⇒≢ i<j)
