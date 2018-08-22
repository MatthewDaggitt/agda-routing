open import Data.Fin using (Fin; zero; suc; fromℕ≤)
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Properties using (_<?_; ≰⇒>)
open import Data.Product
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary using (Pred)

open import RoutingLib.Data.Fin.Properties using (fromℕ≤-injective; pigeonhole)
open import RoutingLib.Data.Nat.Properties using (m<n⇒m≤1+n)
open import RoutingLib.Data.Path.EdgePath.NonEmpty
open import RoutingLib.Data.Path.EdgePath.NonEmpty.All
open import RoutingLib.Data.Path.EdgePath.NonEmpty.Properties

module RoutingLib.Data.Path.EdgePath.NonEmpty.Finiteness where

  -- Lookup functions
  
  lookupₑ : (p : Pathⁿᵗ) → Fin (length p) → Edge
  lookupₑ []              ()
  lookupₑ (e ∷ _ ∣ _ ∣ _) zero    = e
  lookupₑ (_ ∷ p ∣ _ ∣ _) (suc i) = lookupₑ p i

  data NonEmpty : Pathⁿᵗ → Set where
    nonEmpty : ∀ e p e⇿p e∉p → NonEmpty (e ∷ p ∣ e⇿p ∣ e∉p)

  lookupᵥ : ∀ {p : Pathⁿᵗ} → NonEmpty p → Fin (suc (length p)) → ℕ
  lookupᵥ (nonEmpty e p e⇿p e∉p)  zero          = proj₁ e
  lookupᵥ (nonEmpty e p e⇿p e∉p)  (suc zero)    = proj₂ e
  lookupᵥ (nonEmpty e [] e⇿p e∉p) (suc (suc ()))
  lookupᵥ (nonEmpty e (f ∷ p ∣ f⇿p ∣ f∉p) e⇿p e∉p) (suc (suc i)) =
    lookupᵥ (nonEmpty f p f⇿p f∉p) (suc i)

  -- Proofs
  
  ∉-lookup : ∀ {p : Pathⁿᵗ} (p⁺ : NonEmpty p) →
             ∀ {i} → i ∉ p → ∀ k → lookupᵥ p⁺ k ≢ i
  ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) zero = x ∘ sym
  ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (suc zero) = x₁ ∘ sym
  ∉-lookup (nonEmpty .(_ , _) [] e⇿p e∉p) (notHere x x₁ i∉p) (suc (suc ()))
  ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) zero = x ∘ sym
  ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (suc zero) = x₁ ∘ sym
  ∉-lookup (nonEmpty .(_ , _) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) e⇿p e∉p) (notHere x x₁ i∉p) (suc (suc k)) =
    ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) i∉p (suc k)

  ∉-lookup₂ : ∀ {p : Pathⁿᵗ} (p⁺ : NonEmpty p) →
              ∀ {i j} → (i , j) ⇿ p → ∀ k → lookupᵥ p⁺ (suc k) ≢ j
  ∉-lookup₂ (nonEmpty (j , l) p                     e⇿p _)                   (continue x) zero    = ij⇿p⇒i≢j e⇿p ∘ sym
  ∉-lookup₂ (nonEmpty (j , l) []                    _   _)                   (continue x) (suc ())
  ∉-lookup₂ (nonEmpty (j , l) (_ ∷ p ∣ _    ∣ _   ) _   (notHere x₁ x₂ e∉p)) (continue x) (suc zero) = x₂ ∘ sym
  ∉-lookup₂ (nonEmpty (j , l) (e ∷ p ∣ e⇿p₁ ∣ e∉p₁) _   e∉p)                 (continue x) (suc (suc k)) =
    ∉-lookup (nonEmpty e p e⇿p₁ e∉p₁) e∉p (suc (suc k))

  lookup! : ∀ {p : Pathⁿᵗ} (p⁺ : NonEmpty p) → ∀ k l → k ≢ l → lookupᵥ p⁺ k ≢ lookupᵥ p⁺ l
  lookup! (nonEmpty e p e⇿p e∉p)               zero           zero           0≢0 = contradiction refl 0≢0
  lookup! (nonEmpty e p e⇿p e∉p)               zero           (suc zero)    _   = ij⇿p⇒i≢j e⇿p
  lookup! (nonEmpty e [] e⇿p e∉p)              zero           (suc (suc ()))
  lookup! (nonEmpty e p e⇿p e∉p)               (suc zero)    zero           _   = ij⇿p⇒i≢j e⇿p ∘ sym
  lookup! (nonEmpty e [] e⇿p e∉p)              (suc (suc ())) _
  lookup! (nonEmpty e p e⇿p e∉p)               (suc zero)    (suc zero)    1≢1 = contradiction refl 1≢1
  lookup! (nonEmpty e [] e⇿p e∉p)              (suc zero)    (suc (suc ()))
  lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) zero           (suc (suc l)) _   =
    (∉-lookup (nonEmpty f p a b) e∉p (suc l)) ∘ sym
  lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (suc (suc k)) zero           _   =
    (∉-lookup (nonEmpty f p a b) e∉p (suc k))
  lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (suc zero)    (suc (suc l)) _   =
    ∉-lookup₂ (nonEmpty f p a b) e⇿p l ∘ sym
  lookup! (nonEmpty e (f ∷ p ∣ a ∣ b) e⇿p e∉p) (suc (suc k)) (suc zero)    _   =
    ∉-lookup₂ (nonEmpty f p a b) e⇿p k
  lookup! (nonEmpty e (_ ∷ _ ∣ _ ∣ _) e⇿p e∉p) (suc (suc k)) (suc (suc l)) k≢l =
    lookup! (nonEmpty _ _ _ _) (suc k) (suc l) (k≢l ∘ cong suc)

  lookup-Allₙ : ∀ {p q} {P : Pred ℕ p} → Allₙ P q → (q⁺ : NonEmpty q) → ∀ i → P (lookupᵥ q⁺ i)
  lookup-Allₙ ([ Pi , _  ]∷ Pq) (nonEmpty _ p e⇿q e∉q)  zero       = Pi
  lookup-Allₙ ([ _  , Pj ]∷ Pq) (nonEmpty e p e⇿q e∉q)  (suc zero) = Pj
  lookup-Allₙ ([ _  , _  ]∷ Pq) (nonEmpty _ [] e⇿q e∉q) (suc (suc ()))
  lookup-Allₙ ([ _  , _  ]∷ Pq) (nonEmpty _ (e ∷ p ∣ e⇿p ∣ e∉p) e⇿q e∉q) (suc (suc i)) =
    lookup-Allₙ Pq (nonEmpty e p e⇿p e∉p) (suc i)

  lookupᵥᶠ : ∀ {n} {p : Pathⁿᵗ} → Allₙ (_< n) p → NonEmpty p → Fin (suc (length p)) → Fin n
  lookupᵥᶠ p<n p⁺ i = fromℕ≤ (lookup-Allₙ p<n p⁺ i)

  lookupᶠ! : ∀ {n} {p : Pathⁿᵗ} (p<n : Allₙ (_< n) p) (p⁺ : NonEmpty p) →
             ∀ {k l} → k ≢ l → lookupᵥᶠ p<n p⁺ k ≢ lookupᵥᶠ p<n p⁺ l
  lookupᶠ! p<n p⁺ {k} {l} k≢l fromEq = lookup! p⁺ k l k≢l (fromℕ≤-injective (lookup-Allₙ p<n p⁺ k) (lookup-Allₙ p<n p⁺ l) fromEq)
  
  |p|<n : ∀ {n} {p : Pathⁿᵗ} → Allₙ (_< n) p → NonEmpty p → length p < n
  |p|<n {n} p<n q@(nonEmpty e p e⇿p e∉p) with suc (length p) <? n
  ... | yes |q|<n = |q|<n
  ... | no  |q|≮n with pigeonhole (≰⇒> |q|≮n) (lookupᵥᶠ p<n q)
  ...   | i , j , i≢j , pᵢ≡pⱼ = contradiction pᵢ≡pⱼ (lookupᶠ! p<n q i≢j)

  |p|≤1+n : ∀ {p n} → Allₙ (_< n) p → length p ≤ suc n
  |p|≤1+n {[]}                _   = z≤n
  |p|≤1+n {e ∷ p ∣ e⇿p ∣ e∉p} p<n = m<n⇒m≤1+n (|p|<n p<n (nonEmpty _ _ e⇿p e∉p))
