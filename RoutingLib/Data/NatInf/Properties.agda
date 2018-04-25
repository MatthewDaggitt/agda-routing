open import Data.Nat using (zero; suc) renaming (_+_ to _+ℕ_; _≤_ to _≤ℕ_; z≤n to z≤ℕn; s≤s to s≤ℕs; _≤′_ to _≤'ℕ_; ≤′-refl to ≤'ℕ-refl; ≤′-step to ≤'ℕ-step)
open import Data.Nat.Properties using (+-suc; n≤1+n; <⇒≢) renaming (+-identityʳ to +-idʳℕ; +-comm to +-commℕ; +-mono-≤ to +ℕ-mono-≤ℕ) renaming (⊓-sel to ⊓ℕ-sel; m⊓n≤n to m⊓n≤ℕn; m⊓n≤m to m⊓n≤ℕm)
open import Data.Product using (∃; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_)
open import Level using () renaming (zero to lzero)
open import Relation.Binary using (_⇒_; Reflexive; Antisymmetric; Transitive; _Preserves₂_⟶_⟶_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; _≢_; setoid)
open import Relation.Nullary.Negation using (contradiction)

open import RoutingLib.Algebra.FunctionProperties
open import RoutingLib.Data.NatInf

module RoutingLib.Data.NatInf.Properties where
  

  open import Algebra.FunctionProperties {lzero} {A = ℕ∞} _≡_ using (Idempotent)
  open import Algebra.FunctionProperties.Consequences (setoid ℕ∞) using (sel⇒idem)

  -- Properties of equality
  -- A number is not equal to ∞
  ≢∞ : ∀ {m} → N m ≢ ∞
  ≢∞ ()

  -- If x is not infinity, then x is a number
  ≢∞⇒≡N : ∀ {x} → x ≢ ∞ → ∃ λ m → x ≡ N m
  ≢∞⇒≡N {∞} x≢∞ = contradiction refl x≢∞
  ≢∞⇒≡N {N x} x≢∞ = x , refl

  -- If x is a number, then it is not infinity
  ≡N⇒≢∞ : ∀ {x} → (∃ λ m → x ≡ N m) → x ≢ ∞
  ≡N⇒≢∞ (m , refl) ()

  -- Inequality in ℕ implies inequality in ℕ∞
  ≢ℕ⇒≢ : ∀ {m n} → m ≢ n → N m ≢ N n
  ≢ℕ⇒≢ m≢n refl = m≢n refl

  -- Inequality in ℕ∞ for numbers implies inequality in ℕ
  ≢⇒≢ℕ : ∀ {m n} → N m ≢ N n → m ≢ n
  ≢⇒≢ℕ Nm≢Nn refl = Nm≢Nn refl

  -- Equality holds over suc
  ≡-suc : ∀ x y → N x ≡ N y → N (suc x) ≡ N (suc y)
  ≡-suc zero zero refl = cong N (cong suc refl)
  ≡-suc zero (suc y) ()
  ≡-suc (suc x) zero ()
  ≡-suc (suc x) (suc .x) refl = cong N (cong suc refl)

  -- Equality in ℕ implies equality in ℕ∞
  ≡ℕ⇒≡ : ∀ {m n} → m ≡ n → N m ≡ N n
  ≡ℕ⇒≡ refl = refl

  ≢⇒extractℕ≢ : ∀ {m n} → m ≢ ∞ → n ≢ ∞ → m ≢ n → extractℕ m ≢ extractℕ n
  ≢⇒extractℕ≢ m≢∞ n≢∞ m≢n with ≢∞⇒≡N m≢∞ | ≢∞⇒≡N n≢∞
  ... | m₁ , p | n₁ , q rewrite p | q = ≢⇒≢ℕ m≢n

  -- Properties of ≤
  ≤-reflexive : _≡_ ⇒ _≤_
  ≤-reflexive {∞} refl = n≤∞
  ≤-reflexive {N zero} refl = z≤n
  ≤-reflexive {N (suc x)} refl = s≤s (≤-reflexive refl)

  ≤-refl : Reflexive _≤_
  ≤-refl = ≤-reflexive refl

  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-antisym z≤n z≤n = refl
  ≤-antisym (s≤s m≤n) (s≤s n≤m) with ≤-antisym m≤n n≤m
  ... | refl = refl
  ≤-antisym n≤∞ n≤∞ = refl

  ≤-trans : Transitive _≤_
  ≤-trans z≤n _ = z≤n
  ≤-trans (s≤s m≤n) (s≤s n≤o) = s≤s (≤-trans m≤n n≤o)
  ≤-trans _ n≤∞ = n≤∞

  ≤-step : ∀ {m n} → m ≤ N n → m ≤ (N 1) + (N n)
  ≤-step z≤n = z≤n
  ≤-step (s≤s m≤n) = s≤s (≤-step m≤n)

  ∞≰ : ∀ {m} → ∞ ≰ N m
  ∞≰ ()

  ≤⇒≤ℕ : ∀ {m n} → N m ≤ N n → m ≤ℕ n
  ≤⇒≤ℕ z≤n = z≤ℕn
  ≤⇒≤ℕ (s≤s m≤n) = s≤ℕs (≤⇒≤ℕ m≤n)

  ≤ℕ⇒≤ : ∀ {m n} → m ≤ℕ n → N m ≤ N n
  ≤ℕ⇒≤ z≤ℕn = z≤n
  ≤ℕ⇒≤ (s≤ℕs m≤n) = s≤s (≤ℕ⇒≤ m≤n)

  n≤0⇒n≡0 : ∀ n → n ≤ N 0 → n ≡ N 0
  n≤0⇒n≡0 n n≤0 = ≤-antisym n≤0 z≤n

  ≤⇒extractℕ≤ : ∀ {m n} → m ≢ ∞ → n ≢ ∞ → m ≤ n → extractℕ m ≤ℕ extractℕ n
  ≤⇒extractℕ≤ m≢∞ n≢∞ m≤n with ≢∞⇒≡N m≢∞ | ≢∞⇒≡N n≢∞
  ... | m₁ , p | n₁ , q rewrite p | q = ≤⇒≤ℕ m≤n

  -- Properties of <
  <⇒≤ : ∀ {m n} → m < n → m ≤ n
  <⇒≤ {∞} {∞} n≤∞ = n≤∞
  <⇒≤ {∞} {N x} ()
  <⇒≤ {N x} {∞} n≤∞ = n≤∞
  <⇒≤ {N x} {N (suc n)} (s≤s m<n) = ≤-trans m<n (≤ℕ⇒≤ (n≤1+n n))

  <+≢∞⇒≢ : ∀ {m n} → N m < n → N m ≢ n
  <+≢∞⇒≢ {m} {∞} _ = ≢∞
  <+≢∞⇒≢ {m} {N x} m<n = ≢ℕ⇒≢ (<⇒≢ (≤⇒≤ℕ m<n))

  ≤+<⇒< : ∀ {x y z} → x ≤ y → y < z → x < z
  ≤+<⇒< {∞} {∞} {.∞} n≤∞ n≤∞ = n≤∞
  ≤+<⇒< {∞} {N x} {z} () y<z
  ≤+<⇒< {N .0} {∞} {.∞} z≤n n≤∞ = n≤∞
  ≤+<⇒< {N x} {∞} {.∞} n≤∞ n≤∞ = n≤∞
  ≤+<⇒< {N .0} {N x} {.(N (suc _))} z≤n (s≤s y<z) = s≤s z≤n
  ≤+<⇒< {N .0} {N x} {.∞} z≤n n≤∞ = n≤∞
  ≤+<⇒< {N (suc x)} {N (suc y)} {(N (suc z))} (s≤s x≤y) (s≤s y<z) = ≤-trans
                (s≤s (s≤s x≤y)) (s≤s y<z)
  ≤+<⇒< {N .(suc _)} {N .(suc _)} {.∞} (s≤s x≤y) n≤∞ = n≤∞

  <-trans : Transitive _<_
  <-trans {∞} {∞} {∞} n≤∞ n≤∞ = n≤∞
  <-trans {∞} {∞} {N x} n≤∞ ()
  <-trans {∞} {N x} {∞} () b
  <-trans {∞} {N x} {N x₁} () b
  <-trans {N x} {∞} {∞} n≤∞ n≤∞ = n≤∞
  <-trans {N x} {∞} {N x₁} n≤∞ ()
  <-trans {N x} {N (suc y)} {∞} (s≤s x<y) n≤∞ = n≤∞
  <-trans {N x} {N (suc y)} {N (suc z)} (s≤s x<y) (s≤s y<z) = ≤-trans (s≤s x<y)
             (≤-trans y<z (≤ℕ⇒≤ (n≤1+n z )))

  -- Properties of ≤'
  ≤'₀ : ∀ {n} → N 0 ≤' n
  ≤'₀ {∞} = ≤'-∞
  ≤'₀ {N zero} = ≤'-refl
  ≤'₀ {N (suc x)} = ≤'-step ≤'₀

  ≤'-pred : ∀ {m n} → N (suc m) ≤' n → N m ≤' n
  ≤'-pred ≤'-∞ = ≤'-∞
  ≤'-pred ≤'-refl = ≤'-step ≤'-refl
  ≤'-pred {zero} (≤'-step sm≤n) = ≤'₀
  ≤'-pred {suc m} (≤'-step sm≤n) = ≤'-step (≤'-pred sm≤n)

  ≤'-trans : Transitive _≤'_
  ≤'-trans ≤'-∞ ()
  ≤'-trans ≤'-refl y≤z = y≤z
  ≤'-trans (≤'-step x≤y) ≤'-∞ = ≤'-∞
  ≤'-trans (≤'-step x≤y) ≤'-refl = ≤'-step x≤y
  ≤'-trans (≤'-step x≤y) (≤'-step y≤z) = ≤'-trans x≤y (≤'-step (≤'-pred y≤z))

  ≤'-suc : ∀ {m n} → N m ≤' N n → N (suc m) ≤' N (suc n)
  ≤'-suc  ≤'-refl = ≤'-refl
  ≤'-suc (≤'-step m≤n) = ≤'-step (≤'-suc m≤n)

  ≤⇒≡⊎<' : ∀ {m n} → m ≤ n → m ≡ n ⊎ m <' n
  ≤⇒≡⊎<' {∞} {∞} n≤∞ = inj₁ refl
  ≤⇒≡⊎<' {∞} {N m} ()
  ≤⇒≡⊎<' {N m} {∞} m≤n = inj₂ ≤'-∞
  ≤⇒≡⊎<' {N 0} {N 0} z≤n = inj₁ refl
  ≤⇒≡⊎<' {N 0} {N (suc n)} z≤n = inj₂ (≤'-suc ≤'₀)
  ≤⇒≡⊎<' {N (suc m)} {N (suc n)} (s≤s m≤n) with ≤⇒≡⊎<' m≤n
  ... | inj₁ m≡n = inj₁ (≡-suc m n m≡n)
  ... | inj₂ m<n = inj₂ (≤'-suc m<n)

  <'⇒≤' : ∀ {m n} → m <' n → m ≤' n
  <'⇒≤' {∞} {n} ()
  <'⇒≤' {N x} {∞} ≤'-∞ = ≤'-∞
  <'⇒≤' {N x} {N .(suc x)} ≤'-refl = ≤'-step ≤'-refl
  <'⇒≤' {N x} {N (suc n)} (≤'-step m<n) = ≤'-pred (≤'-step m<n)

  ≡⇒≤' : ∀ {m n} → (N m) ≡ (N n) → (N m) ≤' (N n)
  ≡⇒≤' refl = ≤'-refl

  ≤'⇒≤'ℕ : ∀ {m n} → N m ≤' N n → m ≤'ℕ n
  ≤'⇒≤'ℕ ≤'-refl = ≤'ℕ-refl
  ≤'⇒≤'ℕ (≤'-step m≤'n) = ≤'ℕ-step (≤'⇒≤'ℕ m≤'n)

  -- Properties of +
  n≤m+n : ∀ m n → n ≤ m + n
  n≤m+n ∞ _ = n≤∞
  n≤m+n (N m) ∞ = n≤∞
  n≤m+n (N m) (N zero) = z≤n
  n≤m+n (N m) (N (suc n)) = subst (N (suc n) ≤_) (sym (cong N (+-suc m n)))
                                                 (s≤s (n≤m+n (N m) (N n)))

  +-identityˡ : ∀ n → (N 0) + n ≡ n
  +-identityˡ ∞ = refl
  +-identityˡ (N x) = refl

  +-identityʳ : ∀ n → n + (N 0) ≡ n
  +-identityʳ ∞ = refl
  +-identityʳ (N n) = cong N (+-idʳℕ n)

  +-comm : ∀ m n → m + n ≡ n + m
  +-comm ∞ ∞ = refl
  +-comm ∞ (N n) = refl
  +-comm (N m) ∞ = refl
  +-comm (N m) (N n) = cong N (+-commℕ m n)

  +-mono-≤ : _+_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  +-mono-≤ {_} {m} {o} {p} z≤n o≤p = ≤-trans (subst (_≤ p) (sym (+-identityˡ o)) (o≤p)) (n≤m+n m p)
  +-mono-≤ {N (suc m)} {N (suc n)} {_} {p} (s≤s m≤n) z≤n = ≤-trans
              (subst (_≤ N (suc n)) (cong N (sym (+-idʳℕ (suc m)))) (s≤s m≤n))
              (subst (N (suc n) ≤_) (+-comm p (N (suc n))) (n≤m+n p (N (suc n))))
  +-mono-≤ (s≤s m≤n) (s≤s o≤p) = s≤s (+-mono-≤ m≤n (s≤s o≤p))
  +-mono-≤ (s≤s m≤n) n≤∞ = n≤∞
  +-mono-≤ {n} {_} {o} n≤∞ o≤p = subst (n + o ≤_) (sym refl) n≤∞

  m<o×n<o⇒m+n<o+o : ∀ {m n o} → m < N o → n < N o → (m + n) < N (o +ℕ o)
  m<o×n<o⇒m+n<o+o {∞} {∞} {o} () n<o
  m<o×n<o⇒m+n<o+o {∞} {N x} {o} () n<o
  m<o×n<o⇒m+n<o+o {N m} {∞} {.(suc _)} (s≤s m<o) ()
  m<o×n<o⇒m+n<o+o {N m} {N n} {(suc o)} (s≤s m<o) (s≤s n<o) = ≤ℕ⇒≤ (s≤ℕs
                  (+ℕ-mono-≤ℕ {m} {o} {n} {suc o} (≤⇒≤ℕ m<o) (≤⇒≤ℕ (≤-step n<o))))

  +-mono : ∀ {a b c d} → a ≡ c → b ≡ d → a + b ≡ c + d
  +-mono refl refl = refl

  -- Properties of ⊓
  ⊓-sel : ∀ x y → (x ⊓ y) ≡ x ⊎ (x ⊓ y) ≡ y
  ⊓-sel ∞ ∞ = inj₁ refl
  ⊓-sel ∞ (N x) = inj₂ refl
  ⊓-sel (N x) ∞ = inj₁ refl
  ⊓-sel (N zero) (N _) = inj₁ refl
  ⊓-sel (N (suc x)) (N zero) = inj₂ refl
  ⊓-sel (N (suc x)) (N (suc y)) with ⊓ℕ-sel x y
  ... | inj₁ m⊓n≡m = inj₁ (cong N (cong suc m⊓n≡m))
  ... | inj₂ m⊓n≡n = inj₂ (cong N (cong suc m⊓n≡n))

  ⊓-idem : Idempotent _⊓_
  ⊓-idem = sel⇒idem ⊓-sel

  m⊓n≤n : ∀ m n → m ⊓ n ≤ n
  m⊓n≤n ∞     ∞     = ≤-refl
  m⊓n≤n ∞     (N n) = ≤-refl
  m⊓n≤n (N m) ∞     = n≤∞
  m⊓n≤n (N m) (N n) = ≤ℕ⇒≤ (m⊓n≤ℕn m n)

  m⊓n≤m : ∀ m n → m ⊓ n ≤ m
  m⊓n≤m ∞     ∞     = ≤-refl
  m⊓n≤m ∞     (N n) = n≤∞
  m⊓n≤m (N m) ∞     = ≤-refl
  m⊓n≤m (N m) (N n) = ≤ℕ⇒≤ (m⊓n≤ℕm m n)

  ⊓-mono-≤ : _⊓_ Preserves₂ _≤_ ⟶ _≤_ ⟶ _≤_
  ⊓-mono-≤ {x} {y} {u} {v} x≤y u≤v with ⊓-sel y v
  ... | inj₁ y⊓v≡y rewrite y⊓v≡y = ≤-trans (m⊓n≤m x u) x≤y
  ... | inj₂ y⊓v≡v rewrite y⊓v≡v = ≤-trans (m⊓n≤n x u) u≤v

  o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesʳ (_≤ m)
  o≤m⇒n⊓o≤m n o≤m = ≤-trans (m⊓n≤n n _) o≤m

  n≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesˡ (_≤ m)
  n≤m⇒n⊓o≤m o n≤m = ≤-trans (m⊓n≤m _ o) n≤m

  n≤m⊎o≤m⇒n⊓o≤m : ∀ {m} → _⊓_ Preservesᵒ (_≤ m)
  n≤m⊎o≤m⇒n⊓o≤m n o (inj₁ n≤m) = n≤m⇒n⊓o≤m o n≤m
  n≤m⊎o≤m⇒n⊓o≤m n o (inj₂ o≤m) = o≤m⇒n⊓o≤m n o≤m

  m≤n×m≤o⇒m≤n⊓o : ∀ {m} → _⊓_ Preservesᵇ (m ≤_)
  m≤n×m≤o⇒m≤n⊓o m≤n m≤o = subst (_≤ _) (⊓-idem _) (⊓-mono-≤ m≤n m≤o)

