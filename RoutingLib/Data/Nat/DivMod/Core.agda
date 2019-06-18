------------------------------------------------------------------------
-- Copied from v0.16 from the standard library
------------------------------------------------------------------------

module RoutingLib.Data.Nat.DivMod.Core where

open import Agda.Builtin.Nat using ()
  renaming (div-helper to divₕ; mod-helper to modₕ)

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod.Core
open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-------------------------------------------------------------------------
-- mod lemmas

-- stdlib

modₕ-minus : ∀ acc a n → modₕ 0 (acc + n) ((acc + a) ∸ modₕ acc (acc + n) a n) (acc + n) ≡ 0
modₕ-minus acc (suc a) (suc n) rewrite +-suc acc a     | +-suc acc n = modₕ-minus (suc acc) a n
modₕ-minus acc zero    n       rewrite +-identityʳ acc | n∸n≡0 acc = refl
modₕ-minus acc (suc a) zero    rewrite +-identityʳ acc = begin
  modₕ 0 acc ((acc + suc a) ∸ modₕ 0 acc a acc) acc ≡⟨ cong (λ v → modₕ 0 acc (v ∸ modₕ 0 acc a acc) acc) (+-suc acc a) ⟩
  modₕ 0 acc ((suc acc + a) ∸ modₕ 0 acc a acc) acc ≡⟨ cong (λ v → modₕ 0 acc v acc) (+-∸-assoc (suc acc) (a[modₕ]n≤a 0 a acc)) ⟩
  modₕ 0 acc (suc acc + (a ∸ modₕ 0 acc a acc)) acc ≡⟨ cong (λ v → modₕ 0 acc v acc) (+-comm (suc acc) _) ⟩
  modₕ 0 acc (a ∸ modₕ 0 acc a acc + suc acc) acc   ≡⟨ a+n[modₕ]n≡a[modₕ]n 0 (a ∸ modₕ 0 acc a acc) acc ⟩
  modₕ 0 acc (a ∸ modₕ 0 acc a acc) acc             ≡⟨ modₕ-minus 0 a acc ⟩
  0                                                 ∎
