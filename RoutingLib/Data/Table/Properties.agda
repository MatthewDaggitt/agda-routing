open import Algebra.FunctionProperties using (Op₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_∘_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_)
  renaming (refl to ≡-refl)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.Table
open import RoutingLib.Data.Table.All using (All)
open import RoutingLib.Data.Table.Any using (Any)
open import RoutingLib.Algebra.FunctionProperties

module RoutingLib.Data.Table.Properties where

  -- Properties of foldr

  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where

    foldr-forces×ʳ : _•_ Forces-×ʳ P → ∀ e {n} (t : Table A n) →
                    P (foldr _•_ e t) → P e
    foldr-forces×ʳ forces _ {zero}  t Pe = Pe
    foldr-forces×ʳ forces e {suc n} t Pf =
      foldr-forces×ʳ forces e (t ∘ fsuc) (forces _ _ Pf)
      
    foldr-forces× : _•_ Forces-× P → ∀ e {n} (t : Table A n) →
                    P (foldr _•_ e t) → All P t
    foldr-forces× forces _ _ Pfold fzero    = proj₁ (forces _ _ Pfold)
    foldr-forces× forces _ _ Pfold (fsuc i) =
      foldr-forces× forces _ _ (proj₂ (forces _ _ Pfold)) i
    
    foldr-×pres : _•_ ×-Preserves P → ∀ {e} → P e →
                  ∀ {n} {t : Table A n} → All P t →
                  P (foldr _•_ e t)
    foldr-×pres pres Pe {zero}  PM = Pe
    foldr-×pres pres Pe {suc n} PM =
      pres (PM fzero) (foldr-×pres pres Pe (PM ∘ fsuc))

    foldr-⊎presʳ : _•_ ⊎-Preservesʳ P → ∀ {e} → P e →
                        ∀ {n} (t : Table A n) → P (foldr _•_ e t)
    foldr-⊎presʳ pres Pe {zero}  t = Pe
    foldr-⊎presʳ pres Pe {suc n} t =
      pres _ (foldr-⊎presʳ pres Pe (t ∘ fsuc))

    foldr-⊎pres : _•_ ⊎-Preserves P → ∀ e {n} {t : Table A n} →
                       Any P t → P (foldr _•_ e t)
    foldr-⊎pres pres e (fzero  , Pt₀) = pres _ _ (inj₁ Pt₀)
    foldr-⊎pres pres e (fsuc i , Ptᵢ) =
      pres _ _ (inj₂ (foldr-⊎pres pres e (i , Ptᵢ)))



  -- Properties of foldr⁺
  
  module _ {a p} {A : Set a} (P : Pred A p) {_•_ : Op₂ A} where

    foldr⁺-forces× : _•_ Forces-× P → ∀ {n} (t : Table A (suc n)) →
                    P (foldr⁺ _•_ t) → All P t
    foldr⁺-forces× forces t Pft fzero    = foldr-forces×ʳ P (forces×⇒forces×ʳ forces) (t fzero) (t ∘ fsuc) Pft
    foldr⁺-forces× forces t Pft (fsuc i) = foldr-forces× P forces (t fzero) (t ∘ fsuc) Pft i
    
    foldr⁺-×pres : _•_ ×-Preserves P → ∀ {n} {t : Table A (suc n)} →
                   All P t → P (foldr⁺ _•_ t)
    foldr⁺-×pres pres PM = foldr-×pres P pres (PM fzero) (PM ∘ fsuc)

    foldr⁺-⊎pres : _•_ ⊎-Preserves P → ∀ {n} {t : Table A (suc n)} →
                       Any P t → P (foldr⁺ _•_ t)
    foldr⁺-⊎pres pres {t = t} (fzero  , Pt₀) = foldr-⊎presʳ P (⊎pres⇒⊎presʳ pres) Pt₀ (t ∘ fsuc)
    foldr⁺-⊎pres pres (fsuc i , Ptᵢ) = foldr-⊎pres P pres _ (i , Ptᵢ)
