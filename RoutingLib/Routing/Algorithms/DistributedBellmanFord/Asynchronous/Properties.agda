open import Data.Nat using (_≤_; _<_; zero; suc; z≤n; s≤s) renaming (_≟_ to _≟ℕ_)
open import Data.Fin.Subset using (_∈_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; inspect; [_]) renaming (refl to ≡-refl)
open import Induction.WellFounded using (Acc; acc)
open import Data.Vec using (foldr; map; allFin)
open import Data.Vec.Properties using (map-cong)
open import Data.Product using (∃)
open import Data.Sum using (_⊎_)

open import RoutingLib.Routing.Definitions
open import RoutingLib.Asynchronous.Core
open import RoutingLib.Data.Nat.Properties using (n≤0⇒n≡0; ≤-refl)
open import RoutingLib.Data.Fin.Subset using (_∈?_)
open import RoutingLib.Induction.Nat using () renaming (<-well-founded to <-wf)
open import RoutingLib.Algebra.FunctionProperties using (Selective)

module RoutingLib.Routing.Algorithms.DistributedBellmanFord.Asynchronous.Properties
  {a b ℓ n} (rp : RoutingProblem a b ℓ n) (sch : AdmissableSchedule n) where

  open RoutingProblem rp
  open AdmissableSchedule sch

  open import RoutingLib.Routing.Algorithms.DistributedBellmanFord.Asynchronous rp sch
  open import RoutingLib.Asynchronous.Properties sch

  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ : ∀ X i j {s t} → s ≡ t → (tAcc : Acc _<_ t) → (sAcc : Acc _<_ s) → δ' tAcc X i j ≡ δ' sAcc X i j
  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {zero}  ≡-refl (acc tAcc) (acc sAcc) = ≡-refl 
  t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {suc t} ≡-refl (acc tAcc) (acc sAcc) with i ∈? α (suc t)
  ... | yes _ = cong (foldr (λ _ → Route) _⊕_ (I i j)) 
                  (map-cong (λ k → cong (A i k ▷_) (t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X k j ≡-refl (tAcc (β (suc t) i k) (causality t i k)) (sAcc (β (suc t) i k) (causality t i k)))) (allFin n))
  ... | no  _ = t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j ≡-refl (tAcc t ≤-refl) (sAcc t ≤-refl)

  postulate δ'ᵢ-constantSincePreviousActivation : ∀ {t aₜ} X i j → (tAcc : Acc _<_ t) → (aₜ≤t : aₜ ≤ t) → (i∈αₐₜ : i ∈ α aₜ) → (prevAcc : Acc _<_ (previousActivation aₜ≤t i∈αₐₜ)) → δ' tAcc X i j ≈ δ' prevAcc X i j
  {-
  δᵢ-constantSincePreviousActivation {zero}  {zero}  X i j _ 0≤0 i∈α₀ _ rewrite n≤0⇒n≡0 (previousActivation-before 0≤0 i∈α₀) = refl
  δᵢ-constantSincePreviousActivation {zero}  {suc aₜ} X i j _ ()
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) with previousActivation aₜ≤t+1 i∈αₐₜ | inspect (previousActivation aₜ≤t+1) i∈αₐₜ
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) | zero | [ pa≡0 ] with i ∈? α (suc t)
  ...   | yes _ = {!!}
  ...   | no  _ = {!δᵢ-constantSincePreviousActivation X i j ? ? ? ?!}
  δᵢ-constantSincePreviousActivation {suc t} {aₜ}     X i j (acc tAcc) aₜ≤t+1 i∈αₐₜ (acc prevAcc) | suc prevAct | _ = {!!}
  -}

  postulate δᵢ-latestActivation : ∀ {t t'} X i j → (∀ {t''} → t'' ≤ t → i ∈ α t'' → t'' ≤ t') →  δ t X i j ≈ δ t' X i j
  --δᵢ-constantSinceLatestActivation {t} {aₜ} X i j t'-latest = {!!} --δ'ᵢ-constantSincePreviousActivation X i j (<-wf t) aₜ≤t i∈αₐₜ (<-wf (previousActivation aₜ≤t i∈αₐₜ))





  postulate δᵗ⁺¹Xᵢⱼ≈Aᵢₖ▷δᵗXₖⱼ⊎Iᵢⱼ : Selective _≈_ _⊕_ → ∀ {t} X i j → i ∈ α (suc t) → (∃ λ k → δ (suc t) X i j ≈ A i k ▷ δ (β (suc t) i k) X k j) ⊎ (δ (suc t) X i j ≈ I i j)
  
  --σXᵢⱼ≈Aᵢₖ▷Xₖⱼ⊎Iᵢⱼ ⊕-sel X i j with ∃-foldr ⊕-sel (I i j) (extensions X i j)
  --... | inj₁ (k , σXᵢⱼ≈extₖ) = inj₁ (k , (trans σXᵢⱼ≈extₖ (reflexive (lookup-extensions X i j k))))
  --... | inj₂ σXᵢⱼ≈Iᵢⱼ  = inj₂ σXᵢⱼ≈Iᵢⱼ



{-
  with suc t ≟ℕ aₜ 
  ... | yes t+1≡aₜ | yes i∈αₜ₊₁ = {!!}
  ... | yes t+1≡aₜ | no  i∉αₜ₊₁ = {!!} --reflexive (t≡s⇒δ'ᵗᵢⱼ≡δ'ˢᵢⱼ X i j {!t+1≡aₜ!} {!!} {!!})
  ... | no  t+1≢aₜ | yes i∈αₜ₊₁ = {!!}
  ... | no  t+1≢aₜ | no  i∉αₜ₊₁ = {!!} ---constantSincePreviousActivation X {!i!} {!!} {!!} {!!} {!!} {!!}
-}
