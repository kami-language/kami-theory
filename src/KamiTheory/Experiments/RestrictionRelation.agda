
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


open import Data.Nat using (_+_)


module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}}
       -- {{_ : isDecidablePreorder ′ P ′}}
       -- {{_ : hasDecidableEquality P}}
       where

  private variable
    -- n m : Nat
    p q : Term P n
    Γ Γ₀ Γ₁  : Con (Term P) n
    A B : Term P n
    A₀ A₁ : Term P n
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
  data _[_]⤇s_ : ∀{n bs} -> GenTs (Term P) n bs -> P -> GenTs (Term P) n bs -> Set

  data _[_]⤇s_ where
    [] : ∀{n} -> ([] {n = n}) [ W ]⤇s []
    _∷_ : {n b : ℕ} -> {t u : Term P (b + n)} -> t [ W ]⤇ u
        -> ∀{bs} -> ∀{ts us : GenTs (Term P) n bs} -> ts [ W ]⤇s us
        -> (_∷_ {n = n} {b = b} t ts) [ W ]⤇s (_∷_ {n = n} {b = b} u us)

  data _[_]⤇_ {n} where
    var : ∀ v -> var v [ W ]⤇ var v
    constₜ : ∀ c -> constₜ c [ W ]⤇ constₜ c
    gen : ∀{bs} -> (k : MainKind bs)
        -> ∀{ts us} -> ts [ W ]⤇s us
        -> gen (main k) ts [ W ]⤇ gen (main k) us

    gen-loc-keep : ∀ U t -> U ≤ W
              -> t [ W ]⤇ u
              -> loc U t [ W ]⤇ loc U u

    gen-loc-remove : ∀ U t -> ¬(U ≤ W) -> loc U t [ W ]⤇ locskip

  data _[_]⤇Entry_ {n} : Term P n -> P -> Term P n -> Set where
    _,_ : A [ W ]⤇ B -> p [ W ]⤇ q -> (A / p) [ W ]⤇Entry B / q

  data _[_]⤇Ctx_ : Con (Term P) n -> P -> Con (Term P) n -> Set where
    ε : ε [ W ]⤇Ctx ε
    _∙_ : Γ₀ [ W ]⤇Ctx Γ₁ -> A₀ [ W ]⤇Entry A₁ -> (Γ₀ ∙ A₀) [ W ]⤇Ctx (Γ₁ ∙ A₁)



  -- module _ (_∧_ : P -> P -> P) (_∨_ : P -> P -> P) where
  --   private variable
  --     bs : List ℕ
  --     -- p q : Term P n
  --     p₀ p₁ : Term P n
  --     -- Γ₀ Γ₁ Γ  : Con (Term P) n
  --     -- E₀ E₁ E  : Term P n
  --     -- a b : Term P n
  --     -- X Y : Term P n
  --     -- t s : Term P n
  --     -- U V R W W₀ W₁ : P

  --   glue-GenTs : ∀{t₀ t₁ u : GenTs (Term P) n bs}
  --             -> t₀ [ W ]⤇s u -> t₁ [ W ]⤇s u -> GenTs (Term P) n bs
  --   glue : ∀{t₀ t₁ u : Term P n}
  --             -> t₀ [ W ]⤇ u -> t₁ [ W ]⤇ u -> Term P n

  --   glue-GenTs [] [] = []
  --   glue-GenTs (t ∷ ts) (u ∷ us) = glue t u ∷ glue-GenTs ts us

  --   glue (var v) (var .v) = var v
  --   glue (constₜ c) (constₜ .c) = constₜ c
  --   glue (gen k ts) (gen .k us) = gen (main k) (glue-GenTs ts us)
  --   glue (gen k ts) (gen-loc-remove U t x₂) = loc U t
  --   glue (gen-loc-keep U t ϕ α) (gen-loc-keep .U s ψ β) = loc U (glue α β)
  --   glue (gen-loc-remove U t ¬ϕ) (gen k x₂) = loc U t
  --   glue (gen-loc-remove U t ¬ϕ) (gen-loc-remove V s ¬ψ) = loc U t -- This case should be impossible for well-typed terms... Here we just take the term of one side


  --   glue-Con : ∀{Γ₀ Γ₁ Γ : Con (Term P) n}
  --             -> Γ₀ [ W ]⤇Ctx Γ -> Γ₁ [ W ]⤇Ctx Γ -> Con (Term P) n
  --   glue-Con ε ε = ε
  --   glue-Con (α ∙ (αA , αp)) (β ∙ (βA , βp)) = glue-Con α β ∙ (glue αA βA / glue αp βp)


  --   glue-Ctx : W₀ ⊢Ctx Γ₀ -> W₁ ⊢Ctx Γ₁ -> (α : Γ₀ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (β : Γ₁ [ W₀ ∧ W₁ ]⤇Ctx Γ) -> (W₀ ∨ W₁) ⊢Ctx (glue-Con α β)

  --   glue-Entry : {A₀ A₁ A p₀ p₁ p : Term P n}
  --             -> W₀ ∣ Γ₀ ⊢Entry (A₀ / p₀) -> W₁ ∣ Γ₁ ⊢Entry (A₁ / p₁)
  --             -> (αΓ : Γ₀ [ W₀ ∧ W₁ ]⤇Ctx Γ)
  --             -> (βΓ : Γ₁ [ W₀ ∧ W₁ ]⤇Ctx Γ)
  --             -> (αA : A₀ [ W₀ ∧ W₁ ]⤇ A)
  --             -> (βA : A₁ [ W₀ ∧ W₁ ]⤇ A)
  --             -> (αp : p₀ [ W₀ ∧ W₁ ]⤇ p)
  --             -> (βp : p₁ [ W₀ ∧ W₁ ]⤇ p)
  --             -> (W₀ ∨ W₁) ∣ glue-Con αΓ βΓ ⊢Entry (glue αA βA / glue αp βp)

  --   glue-Ctx ε ε ε ε = ε
  --   glue-Ctx (Γ₀P ∙ E₀P) (Γ₁P ∙ E₁P) (α ∙ (αA , αp)) (β ∙ (βA , βp)) = glue-Ctx Γ₀P Γ₁P α β ∙ glue-Entry E₀P E₁P α β αA βA αp βp

  --   glue-Entry (UUⱼ {{ΓP = because ΓP₀}}) (UUⱼ {{ΓP = because ΓP₁}}) α β (gen .Ukind []) (gen .Ukind []) (constₜ .(mlmod (Local _))) (constₜ .(mlmod (Local _))) = UUⱼ {{ΓP = because (glue-Ctx ΓP₀ ΓP₁ α β)}}
  --   glue-Entry NNⱼ E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Vecⱼ E₀P x) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry Emptyⱼ E₁P α β αA βA αp βp = {!!}
  --   glue-Entry Unitⱼ E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Πⱼ E₀P ▹ E₀P₁) E₁P α β (gen .Pikind (x ∷ ())) (gen .Pikind x₁) αp βp
  --   glue-Entry (Σⱼ E₀P ▹ E₀P₁) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Univ-Comⱼ x) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Locⱼ U E₀P) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Comⱼ E₀P) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Endⱼ E₀P) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (E₀P ≫ⱼ E₀P₁) E₁P α β αA βA αp βp = {!!}
  --   glue-Entry (Shareⱼ U V ϕ E₀P) E₁P α β αA βA αp βp = {!!}

