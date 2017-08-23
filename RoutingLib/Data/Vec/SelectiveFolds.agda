open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; cong; subst) renaming (refl to ≡-refl; sym to ≡-sym)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Nullary using (yes; no)
open import Algebra.FunctionProperties.Core using (Op₂)
open import Algebra.FunctionProperties using (Associative; Idempotent; Commutative; Selective; Congruent₂)
open import Data.Fin using (Fin) renaming (_≤_ to _≤Fin_; zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; foldr₁; foldr; lookup; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (∃; ∃₂; _×_; _,_; proj₁; proj₂)
open import Function using (_∘_)

module RoutingLib.Data.Vec.SelectiveFolds
  {a ℓ} (S : Setoid a ℓ) (_•_ : Op₂ (Setoid.Carrier S)) (pres : Congruent₂ (Setoid._≈_ S) _•_) (sel : Selective (Setoid._≈_ S) _•_)
  where

  open Setoid S renaming (Carrier to A)
  open import RoutingLib.Algebra.Selectivity.Properties _≈_ _•_ sel using (idem)
  open import RoutingLib.Algebra.Selectivity.NaturalOrders S _•_ pres using (_≤ᵣ_; _≤ₗ_; ≤ᵣ-resp-≈) renaming (≤ᵣ-antisym to ≤ᵣ-antisym'; ≤ᵣ-absᵣ to ≤ᵣ-absᵣ'; ≤ᵣ-absₗ to ≤ᵣ-absₗ; ≤ᵣ-trans to ≤ᵣ-trans'; ≤ᵣ-isPartialOrder to ≤ᵣ-isPartialOrder'; ≤ᵣ-total to ≤ᵣ-total')
  open import Relation.Binary.NonStrictToStrict _≈_ _≤ᵣ_ using () renaming (_<_ to _<ᵣ_; trans to ass⇨<ᵣ-trans; irrefl to <ᵣ-irrefl)

  ∃-foldr₁ : ∀ {n} → (xs : Vec A (suc n)) → ∃ λ i → foldr₁ _•_ xs ≈ lookup i xs
  ∃-foldr₁ (x ∷ [])     = fzero , refl
  ∃-foldr₁ (x ∷ y ∷ xs) with sel x (foldr₁ _•_ (y ∷ xs))
  ... | inj₁ x•f≈x = fzero , x•f≈x
  ... | inj₂ x•f≈f with ∃-foldr₁ (y ∷ xs)
  ...    | (i , f[y∷xs]≈y∷xsᵢ) = fsuc i , trans x•f≈f f[y∷xs]≈y∷xsᵢ

  ∃-foldr : ∀ {n} e (xs : Vec A n) → (∃ λ i → foldr (λ _ → A) _•_ e xs ≈ lookup i xs) ⊎ foldr (λ _ → A) _•_ e xs ≈ e
  ∃-foldr e [] = inj₂ refl
  ∃-foldr e (x ∷ xs) with sel x (foldr (λ _ → A) _•_ e xs)
  ... | inj₁ x≤fxs = inj₁ (fzero , x≤fxs)
  ... | inj₂ fxs≤x with ∃-foldr e xs
  ...   | inj₁ (i , fxs≈xsᵢ) = inj₁ (fsuc i , trans fxs≤x fxs≈xsᵢ)
  ...   | inj₂ fxs≈e = inj₂ (trans fxs≤x fxs≈e)




  module _ (comm : Commutative _≈_ _•_) (assoc : Associative _≈_ _•_) where

    private

      ≤ᵣ-isPartialOrder : IsPartialOrder _≈_ _≤ᵣ_
      ≤ᵣ-isPartialOrder = ≤ᵣ-isPartialOrder' comm assoc idem

      ≤ᵣ-trans : Transitive _≤ᵣ_
      ≤ᵣ-trans = ≤ᵣ-trans' assoc

      ≤ᵣ-antisym : Antisymmetric _≈_ _≤ᵣ_
      ≤ᵣ-antisym = ≤ᵣ-antisym' comm

      ≤ᵣ-total : Total _≤ᵣ_
      ≤ᵣ-total = ≤ᵣ-total' sel comm

      <ᵣ-trans : Transitive _<ᵣ_
      <ᵣ-trans = ass⇨<ᵣ-trans ≤ᵣ-isPartialOrder

    ------------
    -- foldr₁ --
    ------------

    foldr₁≤xs : ∀ {n} → (xs : Vec A (suc n)) → ∀ i → foldr₁ _•_ xs ≤ᵣ lookup i xs
    foldr₁≤xs (x ∷ [])     fzero     = idem x
    foldr₁≤xs (x ∷ [])     (fsuc ())
    foldr₁≤xs (x ∷ y ∷ xs) fzero     = ≤ᵣ-absₗ assoc idem x (foldr₁ _•_ (y ∷ xs))
    foldr₁≤xs (x ∷ y ∷ xs) (fsuc l)  = ≤ᵣ-trans (≤ᵣ-absᵣ' comm assoc idem (foldr₁ _•_ (y ∷ xs)) x) (foldr₁≤xs (y ∷ xs) l)







    -----------
    -- foldr --
    -----------

    foldrₓₛ≤xsᵢ : ∀ {n} e (xs : Vec A n) → ∀ i → foldr (λ _ → A) _•_ e xs ≤ᵣ lookup i xs
    foldrₓₛ≤xsᵢ e []       ()
    foldrₓₛ≤xsᵢ e (x ∷ xs) fzero     = ≤ᵣ-absₗ assoc idem x (foldr (λ _ → A) _•_ e xs)
    foldrₓₛ≤xsᵢ e (x ∷ xs) (fsuc i)  = ≤ᵣ-trans (≤ᵣ-absᵣ' comm assoc idem (foldr (λ _ → A) _•_ e xs) x) (foldrₓₛ≤xsᵢ e xs i)

    foldrₑ≤e : ∀ {n} e (xs : Vec A n) → foldr (λ _ → A) _•_ e xs ≤ᵣ e
    foldrₑ≤e e []       = idem e
    foldrₑ≤e e (x ∷ xs) = ≤ᵣ-trans (≤ᵣ-absᵣ' comm assoc idem (foldr (λ _ → A) _•_ e xs) x) (foldrₑ≤e e xs)


{-
    foldrₓₛ≈foldrᵥₛ e [] [] _ = refl
    foldrₓₛ≈foldrᵥₛ e (x ∷ xs) (y ∷ ys) eqCon with eqCon fzero
    ... | inj₂ ((fzero , _ , x≉x) ,       _)                        = contradiction refl x≉x
    ... | inj₂ (_ ,                       (fzero , _ , y≉y))        = contradiction refl y≉y
    ... | inj₂ ((fsuc l , xsₗ≤x , xsₗ≉x) , (fsuc m , ysₘ≤y , ysₘ≉y)) = trans (trans (≤ᵣ-trans (foldrₓₛ≤xsᵢ e xs l) xsₗ≤x) (foldrₓₛ≈foldrᵥₛ e xs ys res)) (sym (≤ᵣ-trans (foldrₓₛ≤xsᵢ e ys m) ysₘ≤y))

      where
      res : ∀ k → lookup k xs ≈ lookup k ys ⊎ (∃ λ i → lookup i xs <ᵣ lookup k xs) × (∃ λ j → lookup j ys <ᵣ lookup k ys)
      res k with eqCon (fsuc k)
      ... | inj₁ xsₖ≈ysₖ = inj₁ xsₖ≈ysₖ
      ... | inj₂ ((fsuc i , xsᵢ<xsₖ) , (fsuc j , ysⱼ<ysₖ)) = inj₂ ((i , xsᵢ<xsₖ) ,                       (j , ysⱼ<ysₖ))
      ... | inj₂ ((fzero  , x<xsₖ)  , (fsuc j , ysⱼ<ysₖ)) = inj₂ ((l , <ᵣ-trans (xsₗ≤x , xsₗ≉x) x<xsₖ) , (j , ysⱼ<ysₖ))
      ... | inj₂ ((fsuc i , xsᵢ<xsₖ) , (fzero , y<ysₖ))   = inj₂ ((i , xsᵢ<xsₖ) ,                       (m , <ᵣ-trans (ysₘ≤y , ysₘ≉y) y<ysₖ))
      ... | inj₂ ((fzero  , x<xsₖ)  , (fzero , y<ysₖ))   = inj₂ ((l , <ᵣ-trans (xsₗ≤x , xsₗ≉x) x<xsₖ) , (m ,  <ᵣ-trans (ysₘ≤y , ysₘ≉y) y<ysₖ))


    ... | inj₁ x≈y with sel x (foldr (λ A → _) _•_ e xs) | sel y (foldr (λ A → _) _•_ e ys) | ∃-foldr e xs | ∃-foldr e ys
    ...   | inj₁ x≤f | inj₁ y≤f | _ | _ = trans (trans x≤f x≈y) (sym y≤f)
    ...   | inj₁ x≤f | inj₂ f≤y | _ | _ = {!!}
    ...   | inj₂ f≤x | inj₁ y≤f | _ | _ = {!!}
    ...   | inj₂ f≤x | inj₂ f≤y | inj₂ fxs≈e      | inj₂ fys≈e        = pres x≈y (trans fxs≈e (sym fys≈e))
    ...   | inj₂ f≤x | inj₂ f≤y | inj₂ fxs≈e      | inj₁ (j , fys≈ysⱼ) = {!!}
    ...   | inj₂ f≤x | inj₂ f≤y | inj₁ (i , f≈xsᵢ) | inj₂ fys≈e          = {!!}
    ...   | inj₂ f≤x | inj₂ f≤y | inj₁ (i , f≈xsᵢ) | inj₁ (j , fys≈ysⱼ) = pres x≈y (foldrₓₛ≈foldrᵥₛ e xs ys res)

      where
      res : ∀ k → (lookup k xs ≈ lookup k ys ⊎
          (∃ λ l → lookup l xs <ᵣ lookup k xs) ×
          (∃ λ m → lookup m ys <ᵣ lookup k ys))
      res k with eqCon (fsuc k)
      ... | inj₁ xsₖ≈ysₖ = inj₁ xsₖ≈ysₖ
      ... | inj₂ ((fzero  , x<xsₖ)  , (fzero , y<ysₖ))   = inj₂ ((i , {!!}) , (j , {!!}))
      ... | inj₂ ((fzero  , x<xsₖ)  , (fsuc m , ysₘ<ysₖ)) = inj₂ ((i , {!!}) , (m , ysₘ<ysₖ))
      ... | inj₂ ((fsuc l , xsₗ<xsₖ) , (fzero , y<ysₖ))   = inj₂ ((l , xsₗ<xsₖ) , (j , {!!}))
      ... | inj₂ ((fsuc l , xsₗ<xsₖ) , (fsuc m , ysₘ<ysₖ)) = inj₂ ((l , xsₗ<xsₖ) , (m , ysₘ<ysₖ))
-}



{-
    foldr₁[xs]≈foldr₁[ys] : ∀ {n} (xs ys : Vec A (suc n)) → (∀ k → lookup k xs ≈ lookup k ys ⊎ ((∃ λ l → lookup l xs <ᵣ lookup k xs) × (∃ λ m → lookup m ys <ᵣ lookup k ys))) → foldr₁ _•_ xs ≈ foldr₁ _•_ ys
    foldr₁[xs]≈foldr₁[ys] (x ∷ []) (y ∷ []) eqCon with eqCon fzero
    ... | inj₁ x≈y = x≈y
    ... | inj₂ ((fzero   , (_ , x≉x)) , _) = contradiction refl x≉x
    ... | inj₂ ((fsuc () , _)         , _)
    foldr₁[xs]≈foldr₁[ys] (x₁ ∷ x₂ ∷ xs) (y₁ ∷ y₂ ∷ ys) eqCon with eqCon fzero | sel x₁ (foldr₁ _•_ (x₂ ∷ xs)) | sel y₁ (foldr₁ _•_ (y₂ ∷ ys))
    ... | inj₂ ((fzero , (_ , x≉x)) , _) | _          | _          = contradiction refl x≉x
    ... | inj₂ (_ , (fzero , (_ , y≉y))) | _          | _          = contradiction refl y≉y
    ... | inj₁ x≈y                       | inj₁ x•f≈x | inj₁ y•f≈y = trans (trans x•f≈x x≈y) (sym y•f≈y)
    ... | inj₁ x≈y                       | inj₁ x•f≈x | inj₂ y•f≈f = res2

      where

      res2 : x₁ • (foldr₁ _•_ (x₂ ∷ xs)) ≈ y₁ • (foldr₁ _•_ (y₂ ∷ ys))
      res2 with ∃-foldr (y₂ ∷ ys)
      ... | (j , f≈ysⱼ) with eqCon (fsuc j)
      ...   | inj₁ xsⱼ≈ysⱼ = pres x≈y (≤ᵣ-antisym
        (≤ᵣ-resp-≈ refl (trans xsⱼ≈ysⱼ (sym f≈ysⱼ)) (foldr₁≤xs (x₂ ∷ xs) j))
        (≤ᵣ-trans (≤ᵣ-resp-≈ refl (sym x≈y) y•f≈f) (trans (comm (foldr₁ _•_ (x₂ ∷ xs)) x₁) x•f≈x)))
      ...   | inj₂ (_ , (fzero , y≤ysⱼ , y≉ysⱼ))     = contradiction (≤ᵣ-antisym y≤ysⱼ (≤ᵣ-resp-≈ f≈ysⱼ refl y•f≈f)) y≉ysⱼ
      ...   | inj₂ (_ , (fsuc l , ysₗ≤ysⱼ , ysₗ≉ysⱼ)) = contradiction (≤ᵣ-antisym ysₗ≤ysⱼ (≤ᵣ-resp-≈ f≈ysⱼ refl (foldr₁≤xs (y₂ ∷ ys) l))) ysₗ≉ysⱼ

    ... | inj₁ x≈y                       | inj₂ x•f≈f | inj₁ y•f≈y = res2

      where

      res2 : x₁ • (foldr₁ _•_ (x₂ ∷ xs)) ≈ y₁ • (foldr₁ _•_ (y₂ ∷ ys))
      res2 with ∃-foldr (x₂ ∷ xs)
      ... | (j , f≈xsⱼ) with eqCon (fsuc j)
      ...   | inj₁ xsⱼ≈ysⱼ = pres x≈y (≤ᵣ-antisym
        (≤ᵣ-trans x•f≈f (≤ᵣ-resp-≈ (sym x≈y) refl (trans (comm (foldr₁ _•_ (y₂ ∷ ys)) y₁) y•f≈y)))
        (≤ᵣ-resp-≈ refl (trans (sym xsⱼ≈ysⱼ) (sym f≈xsⱼ)) (foldr₁≤xs (y₂ ∷ ys) j)))
      ...   | inj₂ ((fzero , x≤xsⱼ , x≉xsⱼ) , _)     = contradiction (≤ᵣ-antisym x≤xsⱼ (≤ᵣ-resp-≈ f≈xsⱼ refl x•f≈f)) x≉xsⱼ
      ...   | inj₂ ((fsuc l , xsₗ≤xsⱼ , xsₗ≉xsⱼ) , _) = contradiction (≤ᵣ-antisym xsₗ≤xsⱼ (≤ᵣ-resp-≈ f≈xsⱼ refl (foldr₁≤xs (x₂ ∷ xs) l))) xsₗ≉xsⱼ

    ... | inj₁ x≈y                       | inj₂ x•f≈f | inj₂ y•f≈f = pres x≈y (foldr₁[xs]≈foldr₁[ys] (x₂ ∷ xs) (y₂ ∷ ys) res)

      where

      lemma : ∀ {s t u v} → t ≈ s → t ≤ᵣ u → u <ᵣ v → s <ᵣ v
      lemma t≈s t≤u (u≤v , u≉v) = (≤ᵣ-resp-≈ t≈s refl (≤ᵣ-trans t≤u u≤v)) , (λ s≈v → u≉v (≤ᵣ-antisym u≤v (≤ᵣ-resp-≈ (trans t≈s s≈v) refl t≤u)))

      res : ∀ k →
        lookup k (x₂ ∷ xs) ≈ lookup k (y₂ ∷ ys) ⊎
        ∃ (λ l → lookup l (x₂ ∷ xs) <ᵣ lookup k (x₂ ∷ xs)) ×
        ∃ (λ m → lookup m (y₂ ∷ ys) <ᵣ lookup k (y₂ ∷ ys))
      res k with eqCon (fsuc k) | ∃-foldr (x₂ ∷ xs) | ∃-foldr (y₂ ∷ ys)
      ... | inj₁ xsₖ≈ysₖ                                  | _          | _           = inj₁ xsₖ≈ysₖ
      ... | inj₂ ((fsuc l , xsₗ<xsₖ) , (fsuc m , ysₗ<ysₖ)) | _          | _           = inj₂ ((l , xsₗ<xsₖ) , (m , ysₗ<ysₖ))
      ... | inj₂ ((fsuc l , xsₗ<xsₖ) , (fzero , y<ysₖ))   | _          | (j , f≈ysⱼ)  = inj₂ ((l , xsₗ<xsₖ) , (j , lemma f≈ysⱼ y•f≈f y<ysₖ))
      ... | inj₂ ((fzero , x<xsₖ)   , (fsuc m , ysₗ<ysₖ)) | (i , f≈xsᵢ) | _           = inj₂ ((i , lemma f≈xsᵢ x•f≈f x<xsₖ) , (m , ysₗ<ysₖ))
      ... | inj₂ ((fzero , x<xsₖ)   , (fzero , y<ysₖ))    | (i , f≈xsᵢ) | (j , f≈ysⱼ) = inj₂ ((i , lemma f≈xsᵢ x•f≈f x<xsₖ) , (j , lemma f≈ysⱼ y•f≈f y<ysₖ))


    ... | inj₂ ((fsuc l , (xsₗ≤x , xsₗ≉x)) , _)       | inj₁ x•f≈x | _          = contradiction (≤ᵣ-antisym xsₗ≤x (≤ᵣ-trans (trans (comm (foldr₁ _•_ (x₂ ∷ xs)) x₁) x•f≈x) (foldr₁≤xs (x₂ ∷ xs) l))) xsₗ≉x
    ... | inj₂ ( _ , (fsuc l , (ysₗ≤y , ysₗ≉y)))      | _          | inj₁ y•f≈y = contradiction (≤ᵣ-antisym ysₗ≤y (≤ᵣ-trans (trans (comm (foldr₁ _•_ (y₂ ∷ ys)) y₁) y•f≈y) (foldr₁≤xs (y₂ ∷ ys) l))) ysₗ≉y
    ... | inj₂ ((fsuc l , xsₗ<x) , (fsuc m , ysₘ<y)) | inj₂ x•f≈f | inj₂ y•f≈f = trans (trans x•f≈f (foldr₁[xs]≈foldr₁[ys] (x₂ ∷ xs) (y₂ ∷ ys) res)) (sym y•f≈f)

      where


      res : ∀ k → lookup k (x₂ ∷ xs) ≈ lookup k (y₂ ∷ ys) ⊎
        ∃ (λ l₁ → lookup l₁ (x₂ ∷ xs) <ᵣ lookup k (x₂ ∷ xs)) ×
        ∃ (λ m₁ → lookup m₁ (y₂ ∷ ys) <ᵣ lookup k (y₂ ∷ ys))
      res k with eqCon (fsuc k)
      ... | inj₁ xsₖ≈ysₖ                                     = inj₁ xsₖ≈ysₖ
      ... | inj₂ ((fsuc l₂ , xsₗ<xsₖ) , (fsuc m₂ , ysₘ<ysₖ))  = inj₂ ((l₂ , xsₗ<xsₖ) , (m₂ , ysₘ<ysₖ))
      ... | inj₂ ((fzero   , x<xsₖ)  , (fsuc m₂ , ysₘ₂<ysₖ)) = inj₂ ((l , <ᵣ-trans ≤ᵣ-isPartialOrder xsₗ<x x<xsₖ) ,      (m₂ , ysₘ₂<ysₖ))
      ... | inj₂ ((fsuc l₂ , xsₗ<xsₖ) , (fzero , y<ysₖ))      = inj₂ ((l₂ , xsₗ<xsₖ) , (m , <ᵣ-trans ≤ᵣ-isPartialOrder ysₘ<y y<ysₖ))
      ... | inj₂ ((fzero   , x<xsₖ)  , (fzero , y<ysₖ))      = inj₂ ((l , (<ᵣ-trans ≤ᵣ-isPartialOrder xsₗ<x x<xsₖ)) , (m , (<ᵣ-trans ≤ᵣ-isPartialOrder ysₘ<y y<ysₖ)))
-}
