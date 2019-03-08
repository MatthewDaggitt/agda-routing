

module db716.Algebra.FoldableStructure where

Struct : Set _
Struct = ∀ {a} → Set a → Set a

FoldL : Struct → Set _
FoldL st = ∀ {a b} {A : Set a} {B : Set b} → (A → B → A) → B → st B → A

FoldR : Struct → Set _
FoldR st = ∀ {a b} {A : Set a} {B : Set b} → (A → B → B) → B → st A → B

infix 4 _∙_

assoc⇒foldl≡foldr : ∀ {a} {A : Set a} {st : Struct} {_∙_ : Op₂ A} → assoc _∙_ → ∀ {x : st A} FoldR 
