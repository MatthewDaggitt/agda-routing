\begin{document}
\begin{code}
open import Relation.Binary using (Rel)
open import Algebra.FunctionProperties using (Op₂)

module db716.Relation.Binary.NaturalOrder {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A) where

open import Relation.Binary using (Reflexive)
open import Algebra.FunctionProperties _≈_ using (Idempotent)

infix 4 _≤ᴸ_

_≤ᴸ_ : Rel A ℓ
x ≤ᴸ y = (x ∙ y) ≈ x

infix 4 _≤ᴿ_

_≤ᴿ_ : Rel A ℓ
x ≤ᴿ y = (y ∙ x) ≈ x


idem⇒reflᴿ : Idempotent _∙_ → Reflexive _≤ᴿ_
idem⇒reflᴿ idemOn {x} = idemOn x

reflᴿ⇒idem : Reflexive _≤ᴿ_ → Idempotent _∙_
reflᴿ⇒idem refl x = refl {x}

reflᴸ⇒idem : Reflexive _≤ᴸ_ → Idempotent _∙_
reflᴸ⇒idem refl x = refl {x}

idem⇒reflᴸ : Idempotent _∙_ → Reflexive _≤ᴸ_
idem⇒reflᴸ idemOn {x} = idemOn x

\end{code}
\end{document}
