-- Original file by Joakim Öhman et al.
-- See here: https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/Untyped.agda
--
-- Original license:
-- ```
--   Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel
--   Permission is hereby granted, free of charge, to any person obtaining a copy
--   of this software and associated documentation files (the "Software"), to deal
--   in the Software without restriction, including without limitation the rights
--   to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
--   copies of the Software, and to permit persons to whom the Software is
--   furnished to do so, subject to the following conditions:

--   The above copyright notice and this permission notice shall be included in all
--   copies or substantial portions of the Software.

--   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
--   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
--   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
--   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
--   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
--   OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
--   SOFTWARE.
-- ```

{-# OPTIONS --without-K #-}

module KamiTheory.Main.Dependent.Typed where

open import KamiTheory.Main.Dependent.Untyped

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const)
open import Agora.Order.Preorder

record isDerivable (A : 𝒰 𝑖) : 𝒰 𝑖 where
  field derive : Maybe A

open isDerivable {{...}} public

record isTrue (A : 𝒰 𝑖) : 𝒰 𝑖 where
  constructor because
  field proof : A

open isTrue {{...}} public

instance
  isTrue:isDerivable : ∀{A : 𝒰 𝑖} -> {{der : isDerivable A}} {a : A} -> {{_ :  derive {{der}} ≡ just a}} -> isTrue A
  isTrue:isDerivable {a = a} = record { proof = a }



module KamiTyped (P : Preorder (ℓ₀ , ℓ₀ , ℓ₀)) {{_ : isDiscrete ⟨ P ⟩}} where

  -- open DUN.KamiUntyped ⟨ P ⟩ hiding (_∷_)

  infixl 30 _∙_
  infix 30 Πⱼ_▹_
  infix 30 Σⱼ_▹_
  infix 30 ⟦_⟧ⱼ_▹_


  -- data MLMod : Set where
  --   local : (U : ⟨ P ⟩) -> MLMod
  --   global : MLMod

  -- data Mod (n : Nat) : Set where
  --   ml : MLMod -> Mod n
  --   com : Term ⟨ P ⟩ n -> Mod n

  -- record Term (n : Nat) : Set where
  --   constructor _/_
  --   field type : Term ⟨ P ⟩ n
  --   field mod : Mod n

  open Term

  private
    variable
      -- n m : Nat
      p q : Term ⟨ P ⟩ n
      Γ  : Con (Term ⟨ P ⟩) n
      A B : Term ⟨ P ⟩ n
      L K : Term ⟨ P ⟩ n
      E F : Term ⟨ P ⟩ n
      t s : Term ⟨ P ⟩ n
      G : Term ⟨ P ⟩ (1+ n)
      x : Fin n
      U V : ⟨ P ⟩

  -- wk1-Mod : Mod n -> Mod (1+ n)
  -- wk1-Mod (ml x) = ml x
  -- wk1-Mod (com x) = com (wk1 x)

  -- wk1-Term : Term ⟨ P ⟩ n → Term (1+ n)
  -- wk1-Term (A / p) = wk1 A / wk1-Mod p


  -- Well-typed variables
  data _∶_∈_ : (x : Fin n) (E : Term ⟨ P ⟩ n) (Γ : Con (Term ⟨ P ⟩) n) → Set where
    zero :                       x0 ∶ wk1 E ∈ (Γ ∙ E)
    suc  : (h : x ∶ E ∈ Γ) → (x +1) ∶ wk1 E ∈ (Γ ∙ F)

  data TypeKind : Set where
    Local Global : TypeKind

  private variable
    k l : TypeKind


  mutual


    -- Well-formed context
    data ⊢_ : Con (Term ⟨ P ⟩) n → Set where
      ε   : ⊢ ε
      _∙_ : ⊢ Γ
          → Γ ⊢Entry E
          → ⊢ Γ ∙ E


    -- data _⊢Var_∶_∷_ : {Γ : Con (Term ⟨ P ⟩) n} -> (ΓP : ⊢ Γ)
    --                 -> (x : Fin n) (E : Term ⟨ P ⟩ n) (k : TypeKind) → Set where
    --   zero : ∀{ΓP : ⊢ Γ}
    --          -> {EP : Γ ⊢Entry E ∷ k}
    --          -> (ΓP ∙ EP) ⊢Var x0 ∶ wk1 E ∷ k
    --   suc : ∀{ΓP : ⊢ Γ}
    --          -> ΓP ⊢Var x ∶ E ∷ k
    --          -> {FP : Γ ⊢Entry F}
    --          -> (ΓP ∙ FP) ⊢Var (x +1) ∶ wk1 E ∷ k


    -- Well-formed ml modality
    -- data _⊢MLMod_∷_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n -> TypeKind → Set where
    --   globalⱼ : Γ ⊢MLMod ◯ ∷ Global
    --   localⱼ : ∀ U -> Γ ⊢MLMod ▲ U ∷ Local

    -- Well-formed modality
    -- data _⊢Mod_∷_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → TypeKind -> Set where
    --   mlⱼ : Γ ⊢MLMod p -> Γ ⊢Mod p ∷ k



    -- _⊢Sort_ : (Γ : Con (Term ⟨ P ⟩) n) -> Term ⟨ P ⟩ n -> Set
    -- _⊢Sort_ Γ L = Γ ⊢Sort L ∷ Local

    -- _⊢Sort_ : (Γ : Con (Term ⟨ P ⟩) n) -> Term ⟨ P ⟩ n -> Set
    -- _⊢Sort_ Γ L = Γ ⊢Sort L ∷ Global

    -- Well-formed type
    data _⊢Sort_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n -> Set where
      UUⱼ    : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Sort UU
      NNⱼ    : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Sort NN
      Emptyⱼ : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Sort Empty
      Unitⱼ  : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Sort Unit

      Πⱼ_▹_  : Γ ⊢Entry E → Γ ∙ E ⊢Sort B → Γ ⊢Sort Π E ▹ B
      Σⱼ_▹_  : Γ ⊢Entry F → Γ ∙ F ⊢Sort G → Γ ⊢Sort Σ F ▹ G
      -- univ   : Γ ⊢Sort A ∶ UU
      --       → Γ ⊢Sort A

      -- Kami types
      Locⱼ : (U : ⟨ P ⟩) -> Γ ⊢Sort L -> Γ ⊢Sort (L ＠ U)

    -- Well-formed entry
    data _⊢Entry_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n -> Set where
      UUⱼ    : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Entry (UU / ▲ U)
      NNⱼ    : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Entry (NN / ▲ U)
      Emptyⱼ : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Entry (Empty / ▲ U)
      Unitⱼ  : {{_ : isTrue (⊢ Γ)}} → Γ ⊢Entry (Unit / ▲ U)

      -- Πⱼ_▹_  : Γ ⊢Entry E → Γ ∙ E ⊢Sort B → Γ ⊢Sort Π E ▹ B
      Σⱼ_▹_  : ∀{q} -> Γ ⊢Entry (A / ML q)
             → Γ ∙ (A / ML q) ⊢Entry (B / ML q)
             → Γ ⊢Entry (Σ (A / ML q) ▹ B / ML q)

      -- -- univ   : Γ ⊢Sort A ∶ UU
      -- --       → Γ ⊢Sort A

      -- Kami types
      Locⱼ : (U : ⟨ P ⟩) -> Γ ⊢Entry (L / ▲ U) -> Γ ⊢Entry (L ＠ U / ◯)


    -- Well-formed term of a type
    data _⊢_∶_/_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n -> Term ⟨ P ⟩ n → Set where
      -- Πⱼ_▹_     : ∀ {F G}
      --           → Γ     ⊢ F ∶ U
      --           → Γ ∙ F ⊢ G ∶ U
      --           → Γ     ⊢ Π F ▹ G ∶ U
      -- Σⱼ_▹_     : ∀ {F G}
      --           → Γ     ⊢ F ∶ U
      --           → Γ ∙ F ⊢ G ∶ U
      --           → Γ     ⊢ Σ F ▹ G ∶ U
      -- ℕⱼ        : ⊢ Γ → Γ ⊢Sort ℕ ∶ U
      -- Emptyⱼ    : ⊢ Γ → Γ ⊢Sort Empty ∶ U
      -- Unitⱼ     : ⊢ Γ → Γ ⊢Sort Unit ∶ U

      var       : ∀ {A x}
                -> {{_ : isTrue (⊢ Γ)}}
                → x ∶ (A / p) ∈ Γ
                → Γ ⊢ (Term.var x) ∶ A / p

      lamⱼ      : ∀ {t q}
                → Γ ⊢Entry E
                → Γ ∙ E ⊢ t ∶ B / ML q
                → Γ     ⊢ lam t ∶ Π E ▹ B / ML q

      _∘ⱼ_      : ∀ {g a F G}
                → Γ ⊢ g ∶ Π F ▹ G / q
                → Γ ⊢ a ∶ F / p
                → Γ ⊢ g ∘ a ∶ G [ a ] / q

      prodⱼ     : ∀ A B -> ∀{t u}
                → {{_ : isTrue (Γ ⊢Entry (A / p))}}
                → {{_ : isTrue (Γ ∙ (A / p) ⊢Sort B)}}
                → Γ ⊢ t ∶ A / p
                → Γ ⊢ u ∶ G [ t ] / p
                → Γ ⊢ t ,ₜ u ∶ Σ F ▹ G / p
      fstⱼ      : ∀ A B -> ∀{t}
                → {{_ : isTrue (Γ ⊢Entry (A / p))}}
                → {{_ : isTrue (Γ ∙ (A / p) ⊢Sort B)}}
                → Γ ⊢ t ∶ Σ (A / p) ▹ B / p
                → Γ ⊢ fstₜ t ∶ A / p

      sndⱼ      : ∀ A B -> ∀{t}
                → {{_ : isTrue (Γ ⊢Entry (A / p))}}
                → {{_ : isTrue (Γ ∙ (A / p) ⊢Sort B)}}
                → Γ ⊢ t ∶ Σ (A / p) ▹ B / p
                → Γ ⊢ sndₜ t ∶ B [ fstₜ t ] / p

      -- sndⱼ      : ∀ {F G t}
      --           → Γ ⊢Sort F
      --           → Γ ∙ F ⊢ G
      --           → Γ ⊢Sort t ∶ Σ F ▹ G
      --           → Γ ⊢Sort snd t ∶ G [ fst t ]


      locⱼ : Γ ⊢ t ∶ A / ▲ U -> Γ ⊢ loc U t ∶ (A ＠ U) / ◯
      unlocⱼ : Γ ⊢ t ∶ (A ＠ U) / ◯ -> Γ ⊢ unloc t ∶ A / ▲ U

  private
    _>>=_ = bind-Maybe

  mutual
    {-# TERMINATING #-}
    derive-Entry : ∀ (Γ : Con (Term ⟨ P ⟩) n) E -> Maybe (Γ ⊢Entry E)
    derive-Entry Γ (UU / ▲ U)    = map-Maybe (λ P -> UUⱼ {{because P}}) (derive-Ctx Γ)
    derive-Entry Γ (NN / ▲ U)    = map-Maybe (λ P -> NNⱼ {{because P}}) (derive-Ctx Γ)
    derive-Entry Γ (Empty / ▲ U) = map-Maybe (λ P -> Emptyⱼ {{because P}}) (derive-Ctx Γ)
    derive-Entry Γ (Unit / ▲ U)  = map-Maybe (λ P -> Unitⱼ {{because P}}) (derive-Ctx Γ)
    derive-Entry Γ (L ＠ U / ◯)  = map-Maybe (Locⱼ U) (derive-Entry Γ (L / ▲ U))
    derive-Entry Γ (Σ (A / ML p) ▹ B / ML q) with p ≟-Str q
    ... | left x = nothing
    ... | just refl-≡ = do
      A' <- derive-Entry Γ (A / ML p)
      B' <- derive-Entry (Γ ∙ (A / ML q)) (B / ML q)
      just (Σⱼ A' ▹ B')
    derive-Entry Γ E = nothing


    derive-Ctx : ∀ (Γ : Con (Term ⟨ P ⟩) n) -> Maybe (⊢ Γ)
    derive-Ctx ε = just ε
    derive-Ctx (Γ ∙ E) = do
      E' <- derive-Entry Γ E
      Γ' <- derive-Ctx Γ
      just (Γ' ∙ E')

  derive-Sort : ∀ (Γ : Con (Term ⟨ P ⟩) n) E -> Maybe (Γ ⊢Sort E)
  derive-Sort Γ (UU)    = map-Maybe (λ P -> UUⱼ {{because P}}) (derive-Ctx Γ)
  derive-Sort Γ (NN)    = map-Maybe (λ P -> NNⱼ {{because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Empty) = map-Maybe (λ P -> Emptyⱼ {{because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Unit)  = map-Maybe (λ P -> Unitⱼ {{because P}}) (derive-Ctx Γ)
  derive-Sort Γ (L ＠ U)  = map-Maybe (Locⱼ U) (derive-Sort Γ (L))
  derive-Sort Γ E = nothing


  derive-Term : ∀ Γ -> (t A p : Term ⟨ P ⟩ n) -> Γ ⊢ t ∶ A / p
  derive-Term Γ t A p = {!!}

  instance
    isDerivable:Con : isDerivable (⊢ Γ)
    isDerivable:Con = record { derive = derive-Ctx _ }

  instance
    isDerivable:Entry : isDerivable (Γ ⊢Entry A)
    isDerivable:Entry = record { derive = derive-Entry _ _ }

  instance
    isDerivable:Sort : isDerivable (Γ ⊢Sort A)
    isDerivable:Sort = record { derive = derive-Sort _ _ }

  module Examples where

    _⊢_/_≔_ : (Γ : Con (Term ⟨ P ⟩) n) -> Term ⟨ P ⟩ n → Term ⟨ P ⟩ n -> Term ⟨ P ⟩ n → Set
    Γ ⊢ A / p ≔ t = Γ ⊢ t ∶ A / p

    T0 : ε ⊢Sort NN
    T0 = NNⱼ

    t0 : ε ⊢ (NN / ▲ U) ▹▹ (NN ×× NN) / ▲ U
           ≔ lam (var x0 ,ₜ var x0)

    t0 = lamⱼ NNⱼ (prodⱼ NN NN (var zero) (var zero))

    t1 : ε ⊢ _ ∶ ((((NN ＠ U) / ◯) ×× (NN ＠ U)) / ◯) ▹▹ (NN ×× NN) / ▲ U
    t1 = lamⱼ (Σⱼ Locⱼ _ NNⱼ ▹ Locⱼ _ NNⱼ) (prodⱼ NN NN (unlocⱼ (fstⱼ (NN ＠ _) (NN ＠ _) (var zero))) ((unlocⱼ (sndⱼ (NN ＠ _) (NN ＠ _) (var zero)))))



{-

      -- zeroⱼ     : ⊢ Γ
      --           → Γ ⊢Sort zero ∶ ℕ
      -- sucⱼ      : ∀ {n}
      --           → Γ ⊢Sort       n ∶ ℕ
      --           → Γ ⊢Sort suc n ∶ ℕ
      -- natrecⱼ   : ∀ {G s z n}
      --           → Γ ∙ ℕ ⊢ G
      --           → Γ       ⊢ z ∶ G [ zero ]
      --           → Γ       ⊢ s ∶ Π ℕ ▹ (G ▹▹ G [ suc (var x0) ]↑)
      --           → Γ       ⊢ n ∶ ℕ
      --           → Γ       ⊢ natrec G z s n ∶ G [ n ]

      -- Emptyrecⱼ : ∀ {A e}
      --           → Γ ⊢Sort A → Γ ⊢Sort e ∶ Empty → Γ ⊢Sort Emptyrec A e ∶ A

      -- starⱼ     : ⊢ Γ → Γ ⊢Sort star ∶ Unit

      -- conv      : ∀ {t A B}
      --           → Γ ⊢Sort t ∶ A
      --           → Γ ⊢Sort A ≡ B
      --           → Γ ⊢Sort t ∶ B

    -- Type equality
    -- data _⊢_≡_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
    --   univ   : ∀ {A B}
    --         → Γ ⊢Sort A ≡ B ∶ U
    --         → Γ ⊢Sort A ≡ B
    --   refl   : ∀ {A}
    --         → Γ ⊢Sort A
    --         → Γ ⊢Sort A ≡ A
    --   sym    : ∀ {A B}
    --         → Γ ⊢Sort A ≡ B
    --         → Γ ⊢Sort B ≡ A
    --   trans  : ∀ {A B C}
    --         → Γ ⊢Sort A ≡ B
    --         → Γ ⊢Sort B ≡ C
    --         → Γ ⊢Sort A ≡ C
    --   Π-cong : ∀ {F H G E}
    --         → Γ     ⊢ F
    --         → Γ     ⊢ F ≡ H
    --         → Γ ∙ F ⊢ G ≡ E
    --         → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E
    --   Σ-cong : ∀ {F H G E}
    --         → Γ     ⊢ F
    --         → Γ     ⊢ F ≡ H
    --         → Γ ∙ F ⊢ G ≡ E
    --         → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E

    -- Term equality
  --   data _⊢_≡_∶_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
  --     refl          : ∀ {t A}
  --                   → Γ ⊢Sort t ∶ A
  --                   → Γ ⊢Sort t ≡ t ∶ A
  --     sym           : ∀ {t u A}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort u ≡ t ∶ A
  --     trans         : ∀ {t u r A}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort u ≡ r ∶ A
  --                   → Γ ⊢Sort t ≡ r ∶ A
  --     conv          : ∀ {A B t u}
  --                   → Γ ⊢Sort t ≡ u ∶ A
  --                   → Γ ⊢Sort A ≡ B
  --                   → Γ ⊢Sort t ≡ u ∶ B
  --     Π-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ≡ H       ∶ U
  --                   → Γ ∙ F ⊢ G ≡ E       ∶ U
  --                   → Γ     ⊢ Π F ▹ G ≡ Π H ▹ E ∶ U
  --     Σ-cong        : ∀ {E F G H}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ F ≡ H       ∶ U
  --                   → Γ ∙ F ⊢ G ≡ E       ∶ U
  --                   → Γ     ⊢ Σ F ▹ G ≡ Σ H ▹ E ∶ U
  --     app-cong      : ∀ {a b f g F G}
  --                   → Γ ⊢Sort f ≡ g ∶ Π F ▹ G
  --                   → Γ ⊢Sort a ≡ b ∶ F
  --                   → Γ ⊢Sort f ∘ a ≡ g ∘ b ∶ G [ a ]
  --     β-red         : ∀ {a t F G}
  --                   → Γ     ⊢ F
  --                   → Γ ∙ F ⊢ t ∶ G
  --                   → Γ     ⊢ a ∶ F
  --                   → Γ     ⊢ (lam t) ∘ a ≡ t [ a ] ∶ G [ a ]
  --     η-eq          : ∀ {f g F G}
  --                   → Γ     ⊢ F
  --                   → Γ     ⊢ f ∶ Π F ▹ G
  --                   → Γ     ⊢ g ∶ Π F ▹ G
  --                   → Γ ∙ F ⊢ wk1 f ∘ var x0 ≡ wk1 g ∘ var x0 ∶ G
  --                   → Γ     ⊢ f ≡ g ∶ Π F ▹ G
  --     fst-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ≡ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort fst t ≡ fst t' ∶ F
  --     snd-cong      : ∀ {t t' F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ≡ t' ∶ Σ F ▹ G
  --                   → Γ ⊢Sort snd t ≡ snd t' ∶ G [ fst t ]
  --     Σ-β₁          : ∀ {F G t u}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ∶ F
  --                   → Γ ⊢Sort u ∶ G [ t ]
  --                   → Γ ⊢Sort fst (prod t u) ≡ t ∶ F
  --     Σ-β₂          : ∀ {F G t u}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort t ∶ F
  --                   → Γ ⊢Sort u ∶ G [ t ]
  --                   → Γ ⊢Sort snd (prod t u) ≡ u ∶ G [ fst (prod t u) ]
  --     Σ-η           : ∀ {p r F G}
  --                   → Γ ⊢Sort F
  --                   → Γ ∙ F ⊢ G
  --                   → Γ ⊢Sort p ∶ Σ F ▹ G
  --                   → Γ ⊢Sort r ∶ Σ F ▹ G
  --                   → Γ ⊢Sort fst p ≡ fst r ∶ F
  --                   → Γ ⊢Sort snd p ≡ snd r ∶ G [ fst p ]
  --                   → Γ ⊢Sort p ≡ r ∶ Σ F ▹ G
  --     suc-cong      : ∀ {m n}
  --                   → Γ ⊢Sort m ≡ n ∶ ℕ
  --                   → Γ ⊢Sort suc m ≡ suc n ∶ ℕ
  --     natrec-cong   : ∀ {z z′ s s′ n n′ F F′}
  --                   → Γ ∙ ℕ ⊢ F ≡ F′
  --                   → Γ     ⊢ z ≡ z′ ∶ F [ zero ]
  --                   → Γ     ⊢ s ≡ s′ ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ n ≡ n′ ∶ ℕ
  --                   → Γ     ⊢ natrec F z s n ≡ natrec F′ z′ s′ n′ ∶ F [ n ]
  --     natrec-zero   : ∀ {z s F}
  --                   → Γ ∙ ℕ ⊢ F
  --                   → Γ     ⊢ z ∶ F [ zero ]
  --                   → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ natrec F z s zero ≡ z ∶ F [ zero ]
  --     natrec-suc    : ∀ {n z s F}
  --                   → Γ     ⊢ n ∶ ℕ
  --                   → Γ ∙ ℕ ⊢ F
  --                   → Γ     ⊢ z ∶ F [ zero ]
  --                   → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                   → Γ     ⊢ natrec F z s (suc n) ≡ (s ∘ n) ∘ (natrec F z s n)
  --                           ∶ F [ suc n ]
  --     Emptyrec-cong : ∀ {A A' e e'}
  --                   → Γ ⊢Sort A ≡ A'
  --                   → Γ ⊢Sort e ≡ e' ∶ Empty
  --                   → Γ ⊢Sort Emptyrec A e ≡ Emptyrec A' e' ∶ A
  --     η-unit        : ∀ {e e'}
  --                   → Γ ⊢Sort e ∶ Unit
  --                   → Γ ⊢Sort e' ∶ Unit
  --                   → Γ ⊢Sort e ≡ e' ∶ Unit

  -- -- Term reduction
  -- data _⊢_⇒_∶_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
  --   conv           : ∀ {A B t u}
  --                 → Γ ⊢Sort t ⇒ u ∶ A
  --                 → Γ ⊢Sort A ≡ B
  --                 → Γ ⊢Sort t ⇒ u ∶ B
  --   app-subst      : ∀ {A B t u a}
  --                 → Γ ⊢Sort t ⇒ u ∶ Π A ▹ B
  --                 → Γ ⊢Sort a ∶ A
  --                 → Γ ⊢Sort t ∘ a ⇒ u ∘ a ∶ B [ a ]
  --   β-red          : ∀ {A B a t}
  --                 → Γ     ⊢ A
  --                 → Γ ∙ A ⊢ t ∶ B
  --                 → Γ     ⊢ a ∶ A
  --                 → Γ     ⊢ (lam t) ∘ a ⇒ t [ a ] ∶ B [ a ]
  --   fst-subst      : ∀ {t t' F G}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ⇒ t' ∶ Σ F ▹ G
  --                 → Γ ⊢Sort fst t ⇒ fst t' ∶ F
  --   snd-subst      : ∀ {t t' F G}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ⇒ t' ∶ Σ F ▹ G
  --                 → Γ ⊢Sort snd t ⇒ snd t' ∶ G [ fst t ]
  --   Σ-β₁           : ∀ {F G t u}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ∶ F
  --                 → Γ ⊢Sort u ∶ G [ t ]
  --                 → Γ ⊢Sort fst (prod t u) ⇒ t ∶ F
  --   Σ-β₂           : ∀ {F G t u}
  --                 → Γ ⊢Sort F
  --                 → Γ ∙ F ⊢ G
  --                 → Γ ⊢Sort t ∶ F
  --                 → Γ ⊢Sort u ∶ G [ t ]
  --                 -- TODO(WN): Prove that 𝔍 ∶ G [ t ] is admissible
  --                 → Γ ⊢Sort snd (prod t u) ⇒ u ∶ G [ fst (prod t u) ]
  --   natrec-subst   : ∀ {z s n n′ F}
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ n ⇒ n′ ∶ ℕ
  --                 → Γ     ⊢ natrec F z s n ⇒ natrec F z s n′ ∶ F [ n ]
  --   natrec-zero    : ∀ {z s F}
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ natrec F z s zero ⇒ z ∶ F [ zero ]
  --   natrec-suc     : ∀ {n z s F}
  --                 → Γ     ⊢ n ∶ ℕ
  --                 → Γ ∙ ℕ ⊢ F
  --                 → Γ     ⊢ z ∶ F [ zero ]
  --                 → Γ     ⊢ s ∶ Π ℕ ▹ (F ▹▹ F [ suc (var x0) ]↑)
  --                 → Γ     ⊢ natrec F z s (suc n) ⇒ (s ∘ n) ∘ (natrec F z s n) ∶ F [ suc n ]
  --   Emptyrec-subst : ∀ {n n′ A}
  --                 → Γ ⊢Sort A
  --                 → Γ     ⊢ n ⇒ n′ ∶ Empty
  --                 → Γ     ⊢ Emptyrec A n ⇒ Emptyrec A n′ ∶ A

  -- Type reduction
  data _⊢_⇒_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
    univ : ∀ {A B}
        → Γ ⊢Sort A ⇒ B ∶ U
        → Γ ⊢Sort A ⇒ B

  -- Term reduction closure
  data _⊢_⇒*_∶_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
    id  : ∀ {A t}
        → Γ ⊢Sort t ∶ A
        → Γ ⊢Sort t ⇒* t ∶ A
    _⇨_ : ∀ {A t t′ u}
        → Γ ⊢Sort t  ⇒  t′ ∶ A
        → Γ ⊢Sort t′ ⇒* u  ∶ A
        → Γ ⊢Sort t  ⇒* u  ∶ A

  -- Type reduction closure
  data _⊢_⇒*_ (Γ : Con (Term ⟨ P ⟩) n) : Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set where
    id  : ∀ {A}
        → Γ ⊢Sort A
        → Γ ⊢Sort A ⇒* A
    _⇨_ : ∀ {A A′ B}
        → Γ ⊢Sort A  ⇒  A′
        → Γ ⊢Sort A′ ⇒* B
        → Γ ⊢Sort A  ⇒* B

  -- Type reduction to whnf
  _⊢_↘_ : (Γ : Con (Term ⟨ P ⟩) n) → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set
  Γ ⊢Sort A ↘ B = Γ ⊢Sort A ⇒* B × Whnf B

  -- Term reduction to whnf
  _⊢_↘_∶_ : (Γ : Con (Term ⟨ P ⟩) n) → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set
  Γ ⊢Sort t ↘ u ∶ A = Γ ⊢Sort t ⇒* u ∶ A × Whnf u

  -- Type equality with well-formed types
  _⊢_:≡:_ : (Γ : Con (Term ⟨ P ⟩) n) → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set
  Γ ⊢Sort A :≡: B = Γ ⊢Sort A × Γ ⊢Sort B × (Γ ⊢Sort A ≡ B)

  -- Term equality with well-formed terms
  _⊢_:≡:_∶_ : (Γ : Con (Term ⟨ P ⟩) n) → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Term ⟨ P ⟩ n → Set
  Γ ⊢Sort t :≡: u ∶ A = (Γ ⊢Sort t ∶ A) × (Γ ⊢Sort u ∶ A) × (Γ ⊢Sort t ≡ u ∶ A)

  -- Type reduction closure with well-formed types
  record _⊢_:⇒*:_ (Γ : Con (Term ⟨ P ⟩) n) (A B : Term ⟨ P ⟩ n) : Set where
    constructor [_,_,_]
    field
      ⊢A : Γ ⊢Sort A
      ⊢B : Γ ⊢Sort B
      D  : Γ ⊢Sort A ⇒* B

  open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

  -- Term reduction closure with well-formed terms
  record _⊢_:⇒*:_∶_ (Γ : Con (Term ⟨ P ⟩) n) (t u A : Term ⟨ P ⟩ n) : Set where
    constructor [_,_,_]
    field
      ⊢t : Γ ⊢Sort t ∶ A
      ⊢u : Γ ⊢Sort u ∶ A
      d  : Γ ⊢Sort t ⇒* u ∶ A

  open _⊢_:⇒*:_∶_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

  -- Well-formed substitutions.
  data _⊢ˢ_∶_ (Δ : Con Term m) : (σ : Subst m n) (Γ : Con (Term ⟨ P ⟩) n) → Set where
    id  : ∀ {σ} → Δ ⊢ˢ σ ∶ ε
    _,_ : ∀ {A σ}
        → Δ ⊢ˢ tail σ ∶ Γ
        → Δ ⊢  head σ ∶ subst (tail σ) A
        → Δ ⊢ˢ σ      ∶ Γ ∙ A

  -- Conversion of well-formed substitutions.
  data _⊢ˢ_≡_∶_ (Δ : Con Term m) : (σ σ′ : Subst m n) (Γ : Con (Term ⟨ P ⟩) n) → Set where
    id  : ∀ {σ σ′} → Δ ⊢ˢ σ ≡ σ′ ∶ ε
    _,_ : ∀ {A σ σ′}
        → Δ ⊢ˢ tail σ ≡ tail σ′ ∶ Γ
        → Δ ⊢  head σ ≡ head σ′ ∶ subst (tail σ) A
        → Δ ⊢ˢ      σ ≡ σ′      ∶ Γ ∙ A

  -- Note that we cannot use the well-formed substitutions.
  -- For that, we need to prove the fundamental theorem for substitutions.

  ⟦_⟧ⱼ_▹_ : (W : BindingType) → ∀ {F G}
      → Γ     ⊢ F
      → Γ ∙ F ⊢ G
      → Γ     ⊢ ⟦ W ⟧ F ▹ G
  ⟦ BΠ ⟧ⱼ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
  ⟦ BΣ ⟧ⱼ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

  ⟦_⟧ⱼᵤ_▹_ : (W : BindingType) → ∀ {F G}
      → Γ     ⊢ F ∶ U
      → Γ ∙ F ⊢ G ∶ U
      → Γ     ⊢ ⟦ W ⟧ F ▹ G ∶ U
  ⟦ BΠ ⟧ⱼᵤ ⊢F ▹ ⊢G = Πⱼ ⊢F ▹ ⊢G
  ⟦ BΣ ⟧ⱼᵤ ⊢F ▹ ⊢G = Σⱼ ⊢F ▹ ⊢G

  -}



