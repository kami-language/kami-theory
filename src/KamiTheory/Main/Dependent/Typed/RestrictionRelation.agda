
module KamiTheory.Main.Dependent.Typed.RestrictionRelation where

open import Data.Fin using (#_ ; zero ; suc)
open import Data.List using (_∷_ ; [])

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Typed.Instances




module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}}
       {{_ : isDecidablePreorder ′ P ′}}
       {{_ : hasDecidableEquality P}} where

  private variable
    -- n m : Nat
    p q : Term P n
    Γ  : Con (Term P) n
    A B : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Term P n
    t u s : Term P n
    f g : Term P n
    U V R W W₀ W₁ : P

  data isNot-𝓀-loc : ∀{bs} -> Kind bs -> Set where
    wrongArity : ∀{bs} {k : Kind bs} -> ¬(bs ≡ (0 ∷ 0 ∷ [])) -> isNot-𝓀-loc k
    wrongKind : ∀{k : Kind (0 ∷ 0 ∷ [])} -> ¬(k ≡ 𝓀-loc) -> isNot-𝓀-loc k

  ↯-isNot-𝓀-loc : isNot-𝓀-loc (𝓀-loc) -> 𝟘-𝒰
  ↯-isNot-𝓀-loc (wrongArity x) = x refl
  ↯-isNot-𝓀-loc (wrongKind x) = x refl



  data _[_]⤇_ {n} : Term P n -> P -> Term P n -> Set
  data _[_]⤇s_ {n} : ∀{bs} -> GenTs (Term P) n bs -> P -> GenTs (Term P) n bs -> Set

  data _[_]⤇s_ {n} where
    [] : [] [ W ]⤇s []
    _∷_ : ∀{t u : Term P n} -> t [ W ]⤇ u
        -> ∀{bs} -> ∀{ts us : GenTs (Term P) n bs} -> ts [ W ]⤇s us
        -> (t ∷ ts) [ W ]⤇s (u ∷ us)

  data _[_]⤇_ {n} where
    var : ∀ v -> var v [ W ]⤇ var v
    constₜ : ∀ c -> constₜ c [ W ]⤇ constₜ c
    gen : ∀{bs} -> (k : Kind bs) -> isNot-𝓀-loc k
        -> ∀{ts us} -> ts [ W ]⤇s us
        -> gen k ts [ W ]⤇ gen k us

    gen-loc-keep : ∀ U t -> U ≤ W
              -> t [ W ]⤇ u
              -> loc U t [ W ]⤇ loc U u

    gen-loc-remove : ∀ U t -> ¬(U ≤ W) -> loc U t [ W ]⤇ locskip



