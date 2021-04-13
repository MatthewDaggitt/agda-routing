open import Relation.Binary
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid

module RoutingLib.Relation.Binary.Construct.Closure.Transitive.Finite
  {a ℓ r} {S : Setoid a ℓ} (finite : Finite S)
  (let open Setoid S renaming (Carrier to A))
  {R : Rel _ r} (resp : R Respects₂ _≈_)
  where

open import Data.Fin.Subset
open import Data.Fin.Subset.Properties
open import Data.Nat.Induction
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s; _<_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.Product as Prod
open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as P using (_≢_; _≡_; subst)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product
open import Relation.Unary as U using (Pred)

open import RoutingLib.Data.Fin.Subset
open import RoutingLib.Data.Fin.Subset.Properties
open import RoutingLib.Relation.Nullary.Finite.Bijection.Setoid.Properties finite
open import RoutingLib.Relation.Binary.Construct.Closure.Transitive.Any

open Finite finite
   
R⁺ = TransClosure R
respʳ = proj₁ resp
respˡ = proj₂ resp

length : ∀ {x y} → R⁺ x y → ℕ
length [ x∼y ]      = zero
length (x∼y ∷ R⁺yz) = suc (length R⁺yz)

data R⁺ᶠ : (P : Subset n) (x y : A) → Set (a ⊔ ℓ ⊔ r) where
  nil  : ∀ {p x y} → f x ∈ p → R x y → R⁺ᶠ p x y
  cons : ∀ {p x y z} → f x ∈ p → R x y → R⁺ᶠ (p - f x) y z → R⁺ᶠ p x z

R⁺ᶠ⇒R⁺ : ∀ {p x y} → R⁺ᶠ p x y → R⁺ x y
R⁺ᶠ⇒R⁺ (nil  _ Rxy)      = [ Rxy ]
R⁺ᶠ⇒R⁺ (cons _ Rxy R⁺yz) = Rxy ∷ R⁺ᶠ⇒R⁺ R⁺yz

_∈⁺_ : A → ∀ {x y} → R⁺ x y → Set ℓ
v ∈⁺ Rxy = AnyNode (v ≈_) Rxy

_∈⁺ᶠ_ : ∀ {p} → A → ∀ {x y} → R⁺ᶠ p x y → Set ℓ
v ∈⁺ᶠ R⁺ᶠxy = v ∈⁺ R⁺ᶠ⇒R⁺ R⁺ᶠxy

R⁺ᶠ⇒R⁺-cancel-∈ : ∀ {p v x y} {R⁺ᶠxy : R⁺ᶠ p x y} → v ∈⁺ (R⁺ᶠ⇒R⁺ R⁺ᶠxy) → v ∈⁺ᶠ R⁺ᶠxy
R⁺ᶠ⇒R⁺-cancel-∈ {R⁺ᶠxy = nil  _ _}   v∈R⁺xy         = v∈R⁺xy
R⁺ᶠ⇒R⁺-cancel-∈ {R⁺ᶠxy = cons _ _ _} (here₂ v≈x)    = here₂ v≈x
R⁺ᶠ⇒R⁺-cancel-∈ {R⁺ᶠxy = cons _ _ _} (there v∈R⁺xy) = there (R⁺ᶠ⇒R⁺-cancel-∈ v∈R⁺xy)

v∉Rxy⇒fx≉fv : ∀ {v x y} {R⁺xy : R⁺ x y} → ¬ (v ∈⁺ R⁺xy) → f x ≢ f v
v∉Rxy⇒fx≉fv {R⁺xy = [ Rxy ]}    v∉R⁺xy fv≡fx = v∉R⁺xy (here₁ (sym (injective fv≡fx)))
v∉Rxy⇒fx≉fv {R⁺xy = Rxy ∷ R⁺yz} v∉R⁺xy fv≡fx = v∉R⁺xy (here₂ (sym (injective fv≡fx)))

v∉∷⇒v∉ : ∀ {p v x y z} (fx∈p : f x ∈ p) {Rxy : R x y} {R⁺ᶠyz : R⁺ᶠ _ y z} → ¬ (v ∈⁺ᶠ cons fx∈p Rxy R⁺ᶠyz) → ¬ (v ∈⁺ᶠ R⁺ᶠyz)
v∉∷⇒v∉ fx∈p ¬∈ v = ¬∈ (there v)

transfer : ∀ {p q x y} → p ≡ q → R⁺ᶠ p x y → R⁺ᶠ q x y
transfer P.refl r = r

∈-transfer⁻ : ∀ {p q v x y} (p≡q : p ≡ q) (R⁺xy : R⁺ᶠ p x y) → v ∈⁺ᶠ transfer p≡q R⁺xy → v ∈⁺ᶠ R⁺xy
∈-transfer⁻ P.refl r ∈ = ∈

contract : ∀ {p v x y} {R⁺ᶠxy : R⁺ᶠ p x y} → ¬ (v ∈⁺ᶠ R⁺ᶠxy) → R⁺ᶠ (p - f v) x y
contract {R⁺ᶠxy = nil  fx∈p Rxy}       v∉R = nil  (x∈p∧x≢y⇒x∈p-y fx∈p (v∉Rxy⇒fx≉fv v∉R)) Rxy
contract {x = x} {y} {R⁺ᶠxy = cons {y = z} fx∈p Rxy R⁺ᶠyz} v∉R = cons (x∈p∧x≢y⇒x∈p-y fx∈p (v∉Rxy⇒fx≉fv v∉R)) Rxy
  (transfer (p─x─y≡p─y─x _ (f x) (f _)) (contract (v∉∷⇒v∉ fx∈p v∉R)) )

∈-contract⁻ : ∀ {p w v x y} {R⁺ᶠxy : R⁺ᶠ p x y} (v∉R⁺xy : ¬ (v ∈⁺ᶠ R⁺ᶠxy)) →
              w ∈⁺ᶠ contract v∉R⁺xy → w ∈⁺ᶠ R⁺ᶠxy
∈-contract⁻ {R⁺ᶠxy = nil  _ x₁}      v∉ (here₁ w≈x) = here₁ w≈x
∈-contract⁻ {R⁺ᶠxy = cons _ x₁ _}    v∉ (here₂ w≈x) = here₂ w≈x
∈-contract⁻ {R⁺ᶠxy = cons fx∈p x₁ R⁺yz} v∉ (there w∈R⁺yz) = there (∈-contract⁻ (v∉∷⇒v∉ fx∈p v∉) (∈-transfer⁻ _ _ (R⁺ᶠ⇒R⁺-cancel-∈ w∈R⁺yz)))

_∈⁺?_ : ∀ v {x y} (R⁺xy : R⁺ x y) → Dec (v ∈⁺ R⁺xy)
v ∈⁺? R⁺xy = anyNode? (v ≟_) R⁺xy

truncate : ∀ {v x y} {R⁺xy : R⁺ x y} → v ∈⁺ R⁺xy → R⁺ v y
truncate (here₁ {Rxy = Rxy}               v≈x) = [ respˡ (sym v≈x) Rxy ]
truncate (here₂ {Rxy = Rxy} {R⁺yz = R⁺yz} v≈x) = respˡ (sym v≈x) Rxy ∷ R⁺yz
truncate (there v∈R⁺yz)                        = truncate v∈R⁺yz

truncate-length : ∀ {v x y} {R⁺xy : R⁺ x y} (v∈R⁺xy : v ∈⁺ R⁺xy) → length (truncate v∈R⁺xy) ≤ length R⁺xy
truncate-length (here₁ v≈x)         = z≤n
truncate-length (here₂ v≈x)    = ≤-refl
truncate-length (there v∈R⁺yz) = ≤-trans (truncate-length v∈R⁺yz) (n≤1+n _)

∈-truncate⁻ : ∀ {v w x y} {R⁺xy : R⁺ x y} (w∈R⁺xy : w ∈⁺ R⁺xy) → v ∈⁺ truncate w∈R⁺xy → v ∈⁺ R⁺xy
∈-truncate⁻ (here₁ w≈x)    (here₁ v≈w) = here₁ (trans v≈w w≈x)
∈-truncate⁻ (here₂ w≈x)    (here₂ v≈w) = here₂ (trans v≈w w≈x)
∈-truncate⁻ (here₂ w≈x)    (there v∈t) = there v∈t
∈-truncate⁻ (there w∈R⁺xy) v∈t         = there (∈-truncate⁻ w∈R⁺xy v∈t)

R⁺ᶠ-respʳ-≈ : ∀ {p} → (R⁺ᶠ p) Respectsˡ _≈_
R⁺ᶠ-respʳ-≈ {p} x≈w (nil  fx∈p Rxy)      rewrite cong x≈w = nil  fx∈p (respˡ x≈w Rxy)
R⁺ᶠ-respʳ-≈ {p} x≈w (cons fx∈p Rxy R⁺yz) rewrite cong x≈w = cons fx∈p (respˡ x≈w Rxy) R⁺yz

R⁺ᶠ? : Decidable R → ∀ {P : Subset n} → Acc _<_ ∣ P ∣ → ∀ x y → Dec (R⁺ᶠ P x y)
R⁺ᶠ? R? {P} (acc rec) x y with f x ∈? P
... | no fx∉p  = no λ {(nil fx∈p _) → fx∉p fx∈p; (cons fx∈p _ _) → fx∉p fx∈p}
... | yes fx∈p with R? x y
...   | yes Rxy = yes (nil fx∈p Rxy)
...   | no ¬Rxy with any? (λ z → R? x z ×-dec R⁺ᶠ? R? (rec ∣ P - f x ∣ (x∈p⇒∣p-x∣<∣p∣ fx∈p)) z y)
  (λ w≈z → Prod.map (respʳ w≈z) (R⁺ᶠ-respʳ-≈ w≈z))
...     | no not               = no λ {(nil _ Rxy) → ¬Rxy Rxy; (cons {y = z} _ Rxz R⁺zy) → not (z , Rxz , R⁺zy)}
...     | yes (z , Rxz , R⁺zy) = yes (cons fx∈p Rxz R⁺zy)

mutual

  R⁺⇒R⁺ᶠ : ∀ {x y} (R⁺xy : R⁺ x y) → Acc _<_ (length R⁺xy) → R⁺ᶠ (⊤ {n}) x y
  R⁺⇒R⁺ᶠ {x} [ Rxy ]      _ = nil  ∈⊤ Rxy
  R⁺⇒R⁺ᶠ {x} (Rxy ∷ R⁺yz) (acc rec) with x ∈⁺? R⁺yz
  ... | yes x∈R⁺yz = R⁺⇒R⁺ᶠ (truncate x∈R⁺yz) (rec _ (s≤s (truncate-length x∈R⁺yz)))
  ... | no  x∉R⁺yz = cons ∈⊤ Rxy (contract (x∉R⁺yz ∘ R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ (rec _ ≤-refl)))

  R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ : ∀ {v x y} {R⁺xy : R⁺ x y} (rec : Acc _<_ (length R⁺xy)) → v ∈⁺ᶠ (R⁺⇒R⁺ᶠ R⁺xy rec) → v ∈⁺ R⁺xy
  R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ {_}     {R⁺xy = [ Rxy ]}    _         v∈R⁺xy = v∈R⁺xy
  R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ {v} {x = x} {R⁺xy = Rxy ∷ R⁺yz} (acc rec) v∈R⁺xy with x ∈⁺? R⁺yz
  ... | yes x∈R⁺yz = there (∈-truncate⁻ x∈R⁺yz (R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ _ v∈R⁺xy))
  ... | no  x∉R⁺yz with v∈R⁺xy
  ...   | here₂ v≈x    = here₂ v≈x
  ...   | there v∈R⁺yz = there (R⁺⇒R⁺ᶠ-pres-∈⁺ᶠ _ (∈-contract⁻ _ (R⁺ᶠ⇒R⁺-cancel-∈ v∈R⁺yz)))

R⁺? : Decidable R → Decidable (TransClosure R)
R⁺? R? x y = Dec.map′ R⁺ᶠ⇒R⁺ (λ v → R⁺⇒R⁺ᶠ v (<-wellFounded _)) (R⁺ᶠ? R? (<-wellFounded ∣ ⊤ {n = n} ∣)  x y)
