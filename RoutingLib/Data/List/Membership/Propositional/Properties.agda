open import Algebra.FunctionProperties using (Op₂; Selective)
open import Data.Nat using (ℕ; suc; zero; _<_; _≤_; s≤s; z≤n; _≟_)
open import Data.Nat.Properties using (⊔-sel; m≤m⊔n; ≤+≢⇒<; ⊔-identityʳ; n≤m⊔n; ≤-trans)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List
open import Data.List.Any as Any using (here; there)
open import Data.List.Any.Membership.Propositional using (_∈_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; _,_; _×_; proj₂)
open import Relation.Binary using (Setoid; Decidable; DecSetoid)
open import Relation.Binary.PropositionalEquality using (_≡_; setoid; refl; cong; cong₂)
open import Relation.Binary.List.Pointwise using (≡⇒Rel≡)
open import Relation.Nullary using (yes; no)
open import Relation.Unary using () renaming (Decidable to Decidableᵤ)
open import Function using (_∘_; id)

open import RoutingLib.Data.List using (combine; allFinPairs)
open import RoutingLib.Data.Nat.Properties using (ℕₛ)
open import RoutingLib.Data.List.Permutation using (_⇿_)
import RoutingLib.Data.List.Membership.Setoid as SetoidMembership

module RoutingLib.Data.List.Membership.Propositional.Properties where

  import RoutingLib.Data.List.Membership.Setoid.Properties as GM

  ∈-resp-≡ : ∀ {a} {A : Set a} {x y : A} {xs ys} → x ≡ y → xs ≡ ys → x ∈ xs → y ∈ ys 
  ∈-resp-≡ refl refl = id

  -- stdlib
  ∈-++⁺ʳ : ∀ {a} {A : Set a} {v : A} xs {ys} → v ∈ ys → v ∈ xs ++ ys
  ∈-++⁺ʳ = GM.∈-++⁺ʳ (setoid _)

  -- stdlib
  ∈-++⁺ˡ : ∀ {a} {A : Set a} {v : A} {xs ys} → v ∈ xs → v ∈ xs ++ ys
  ∈-++⁺ˡ = GM.∈-++⁺ˡ (setoid _)

  -- stdlib
  ∈-++⁻ : ∀ {a} {A : Set a} {v : A}  xs {ys} → v ∈ xs ++ ys → v ∈ xs ⊎ v ∈ ys
  ∈-++⁻ = GM.∈-++⁻ (setoid _)

  -- stdlib
  ∈-concat⁺ : ∀ {a} {A : Set a} {v : A} {xs xss} →
              v ∈ xs → xs ∈ xss → v ∈ concat xss
  ∈-concat⁺ v∈xs xs∈xss = GM.∈-concat⁺ (setoid _) v∈xs (Any.map ≡⇒Rel≡ xs∈xss)
  
  ∈-combine⁺ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
              {u v xs ys} (f : A → B → C) → u ∈ xs → v ∈ ys →
              f u v ∈ combine f xs ys
  ∈-combine⁺ f = GM.∈-combine (setoid _) (setoid _) (setoid _) (cong₂ f)

  ∈-applyUpTo⁺ : ∀ {a} {A : Set a} (f : ℕ → A) {n i} →
                 i < n → f i ∈ applyUpTo f n
  ∈-applyUpTo⁺ = GM.∈-applyUpTo⁺ (setoid _)

  ∈-upTo⁺ : ∀ {n i} → i < n → i ∈ upTo n
  ∈-upTo⁺ = ∈-applyUpTo⁺ id
  
  ∈-applyDownFrom⁺ : ∀ {a} {A : Set a} (f : ℕ → A) {n i} →
                     i < n → f i ∈ applyDownFrom f n
  ∈-applyDownFrom⁺ f {suc n} {i} (s≤s i≤n) with i ≟ n
  ... | yes i≡n = here (cong f i≡n)
  ... | no  i≢n = there (∈-applyDownFrom⁺ f (≤+≢⇒< i≤n i≢n))

  ∈-downFrom⁺ : ∀ {n i} → i < n → i ∈ downFrom n
  ∈-downFrom⁺ i<n = ∈-applyDownFrom⁺ id i<n

  {-
  ∈-applyBetween⁺ : ∀ {a} {A : Set a} (f : ℕ → A) {s e i} →
                    s ≤ i → i < e → f i ∈ applyBetween f s e
  ∈-applyBetween⁺ = GM.∈-applyBetween⁺ (setoid _)

  ∈-applyBetween⁻ : ∀ {a} {A : Set a} (f : ℕ → A) s e {v} →
                    v ∈ applyBetween f s e → ∃ λ i → s ≤ i × i < e × v ≡ f i
  ∈-applyBetween⁻ = GM.∈-applyBetween⁻ (setoid _)
  
  
  ∈-between⁺ : ∀ {s e i} → s ≤ i → i < e → i ∈ between s e
  ∈-between⁺ = ∈-applyBetween⁺ id

  ∈-between⁻ : ∀ s e {i} → i ∈ between s e → s ≤ i × i < e
  ∈-between⁻ s e i∈ with ∈-applyBetween⁻ id s e i∈
  ... | i , s≤i , i<e , refl = s≤i , i<e
  -}
  
  -- stdlib
  ∈-tabulate⁺ : ∀ {a n} {A : Set a} (f : Fin n → A) i → f i ∈ tabulate f
  ∈-tabulate⁺ = GM.∈-tabulate⁺ (setoid _)

  ∈-allFin⁺ : ∀ {n} i → i ∈ allFin n
  ∈-allFin⁺ = ∈-tabulate⁺ id

  ∈-allFinPairs⁺ : ∀ {n} i j → (i , j) ∈ allFinPairs n
  ∈-allFinPairs⁺ i j = ∈-combine⁺ _,_ (∈-allFin⁺ i) (∈-allFin⁺ j)

  

  ∈-perm : ∀ {a} {A : Set a} {x : A} {xs ys} → x ∈ xs → xs ⇿ ys → x ∈ ys
  ∈-perm = GM.∈-perm (setoid _)

  -- stdlib
  ∈-length : ∀ {a} {A : Set a} {x : A} {xs} → x ∈ xs → 1 ≤ length xs
  ∈-length x∈xs = GM.∈-length (setoid _) x∈xs

  -- stdlib
  ∈-filter⁺ : ∀ {a p} {A : Set a} {P : A → Set p} (P? : Decidableᵤ P) →
               ∀ {v} → P v → ∀ {xs} → v ∈ xs → v ∈ filter P? xs
  ∈-filter⁺ P? = GM.∈-filter⁺ (setoid _) P? λ {refl → id}

  -- stdlib
  ∈-filter⁻ : ∀ {a p} {A : Set a} {P : A → Set p} (P? : Decidableᵤ P)  →
               ∀ {v xs} → v ∈ filter P? xs → v ∈ xs × P v
  ∈-filter⁻ P? = GM.∈-filter⁻ (setoid _) P? λ {refl → id}

  -- stdlib
  ∈-lookup : ∀ {a} {A : Set a} (xs : List A) i → lookup xs i ∈ xs
  ∈-lookup = GM.∈-lookup (setoid _)

  -- stdlib
  foldr-∈ : ∀ {a} {A : Set a} {_•_ : Op₂ A} → Selective _≡_ _•_ → ∀ e xs →
            foldr _•_ e xs ≡ e ⊎ foldr _•_ e xs ∈ xs 
  foldr-∈ = GM.foldr-∈ (setoid _)
