open import Function.Reasoning
open import Function using (id)

module RoutingLib.Function.Reasoning where

infix -1 begin⟨_⟩_ beginIrrel⟨_⟩_
infixr 0 ∴_$⟨_⟩_
infix 1 ∴_∎


begin⟨_⟩_ : ∀ {a b} {A : Set a} {B : A → Set b} → (a : A) → (∀ a → B a) → B a
begin⟨ x ⟩ f = f x

beginIrrel⟨_⟩_ : ∀ {a b} {A : Set a} {B : .A → Set b} → .(a : A) → (∀ .a → B a) → B a
beginIrrel⟨ x ⟩ f = f x

∴_$⟨_⟩_ : ∀ {a b c} (A : Set a) {B : A → Set b} {C : (a : A) →  Set c} → (∀ a → B a) → (∀ {a} → B a → C a) → (∀ a → C a)
(∴ A $⟨ f ⟩ g) x = g (f x)

∴_∎ : ∀ {a} (A : Set a) → (A → A)
∴ A ∎ = id

---
--- this is a simple example illustrating the use of this notation. 
---
private 
   example1 : ∀ {a} (A : Set a) → (B : Set a) →  (C : Set a) → (A → B) → (B → C) → A → C 
   example1 A B C f g x = begin⟨ x ⟩
                   ∴ A   $⟨ f ⟩
                   ∴ B   $⟨ g ⟩                   
                   ∴ C   ∎
