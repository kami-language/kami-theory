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

-- {-# OPTIONS --without-K #-}

module KamiTheory.Main.Dependent.Typed.Definition where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const)
open import Agora.Order.Preorder

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product





-- module _ {P : 𝒰 _} {{_ : Preorder (ℓ₀ , ℓ₀ , ℓ₀) on P}} {{_ : hasDecidableEquality P}} where
module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}}
       {{_ : hasDecidableEquality P}} where

  -- open DUN.KamiUntyped P hiding (_∷_)

  infixl 30 _∙_
  infix 30 Πⱼ_▹_
  infix 30 Σⱼ_▹_
  infix 30 ⟦_⟧ⱼ_▹_


  -- data MLMod : Set where
  --   local : (U : P) -> MLMod
  --   global : MLMod

  -- data Mod (n : Nat) : Set where
  --   ml : MLMod -> Mod n
  --   com : Term P n -> Mod n

  -- record Term (n : Nat) : Set where
  --   constructor _/_
  --   field type : Term P n
  --   field mod : Mod n

  open Term

  private variable
    -- n m : Nat
    p q : Term P n
    Γ  : Con (Term P) n
    A B : Term P n
    a b : Term P n
    X Y : Term P n
    L K : Term P n
    E F : Term P n
    t s : Term P n
    f g : Term P n
    G : Term P (1+ n)
    x : Fin n
    U V R : P

  -- wk1-Mod : Mod n -> Mod (1+ n)
  -- wk1-Mod (ml x) = ml x
  -- wk1-Mod (com x) = com (wk1 x)

  -- wk1-Term : Term P n → Term (1+ n)
  -- wk1-Term (A / p) = wk1 A / wk1-Mod p


  -- Well-typed variables
  data _∶_∈_ : (x : Fin n) (E : Term P n) (Γ : Con (Term P) n) → Set where
    zero :                       x0 ∶ wk1 E ∈ (Γ ∙ E)
    suc  : (h : x ∶ E ∈ Γ) → (x +1) ∶ wk1 E ∈ (Γ ∙ F)

  data TypeKind : Set where
    Local Global : TypeKind

  private variable
    k l : TypeKind


  mutual


    -- Well-formed context
    data ⊢_ : Con (Term P) n → Set where
      ε   : ⊢ ε
      _∙_ : ⊢ Γ
          → Γ ⊢Entry E
          → ⊢ Γ ∙ E

    -- Well-formed type
    data _⊢Sort_ (Γ : Con (Term P) n) : Term P n -> Set where
      UUⱼ    : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Sort UU
      NNⱼ    : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Sort NN
      Vecⱼ   : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Sort A → Γ ⊢Sort F → Γ ⊢Sort Vec A F
      Emptyⱼ : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Sort Empty
      Unitⱼ  : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Sort Unit

      Πⱼ_▹_  : Γ ⊢Entry E → Γ ∙ E ⊢Sort B → Γ ⊢Sort Π E ▹ B
      Σⱼ_▹_  : Γ ⊢Entry F → Γ ∙ F ⊢Sort G → Γ ⊢Sort Σ F ▹ G
      -- univ   : Γ ⊢Sort A ∶ UU
      --       → Γ ⊢Sort A

      -- Kami types
      Locⱼ : (U : P) -> Γ ⊢Sort L -> Γ ⊢Sort (L ＠ U)

    -- Well-formed entry
    data _⊢Entry_ (Γ : Con (Term P) n) : Term P n -> Set where
      UUⱼ    : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Entry (UU / ▲ U)
      NNⱼ    : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Entry (NN / ▲ U)
      Emptyⱼ : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Entry (Empty / ▲ U)
      Unitⱼ  : {{ΓP : isTrue (⊢ Γ)}} → Γ ⊢Entry (Unit / ▲ U)

      -- Πⱼ_▹_  : Γ ⊢Entry E → Γ ∙ E ⊢Sort B → Γ ⊢Sort Π E ▹ B
      Σⱼ_▹_  : ∀{q} -> Γ ⊢Entry (A / ML q)
             → Γ ∙ (A / ML q) ⊢Entry (B / ML q)
             → Γ ⊢Entry (Σ (A / ML q) ▹ B / ML q)

      -- univ   : Γ ⊢Sort A ∶ UU
      --       → Γ ⊢Sort A

      -------------------
      -- Kami types (global ◯)
      Locⱼ : (U : P) -> Γ ⊢Entry (L / ▲ U) -> Γ ⊢Entry (L ＠ U / ◯)
      Comⱼ : Γ ⊢Entry (A / ◯) -> Γ ⊢Entry (Com R A / ◯)

      -------------------
      -- Kami types (communication ⇄)

      -- The identity communication
      Endⱼ : Γ ⊢Entry (A / ◯) -> Γ ⊢Entry (End / ⇄ R A)

      -- We concatenate two communications
      _≫ⱼ_ : Γ ⊢Entry (X / ⇄ R A)
           -> Γ ∙ (A / ◯) ⊢Entry (F / ⇄ R (wk1 B))
           -> Γ ⊢Entry (X ≫ F / ⇄ R B)

      -- We share a local value of type "A ＠ U" to be "A ＠ V"
      Shareⱼ : Γ ⊢Entry (A / ▲ V)
             -> ∀ (U V : P) -> (ϕ : V ≤ U)
             -> Γ ⊢Entry (Share A U V / ⇄ R (A ＠ V))


    -- Well-formed term of a type
    data _⊢_∶_/_ (Γ : Con (Term P) n) : Term P n → Term P n -> Term P n → Set where

      -------------------
      -- Communication

      -- We end a communication by giving a value of the
      -- required type
      endⱼ : Γ ⊢ a ∶ A / ◯ -> Γ ⊢ end a ∶ End / ⇄ R A

      -- If we have:
      --  - `a`: a com of type `X` which gives us a value of type A
      --  - `b`: a com of type `Y` which (assuming a : A) gives us B,
      -- we can compose these communications to get one of type `X ≫ Y`
      _>ⱼ_ : Γ ⊢ a ∶ X / ⇄ R A
           -> Γ ∙ (A / ◯) ⊢ b ∶ Y / ⇄ R (wk1 B)
           -> Γ ⊢ (a > b) ∶ X ≫ Y / ⇄ R B

      -- If we have a value (a ∶ A ＠ U) then we can share it so it is
      -- available at V.
      shareⱼ : Γ ⊢Entry (A / ▲ V)
           -> Γ ⊢ a ∶ (A ＠ U) / ◯
           -> (ϕ : V ≤ U)
           -> Γ ⊢ share a ∶ Share A U V / ⇄ R (A ＠ V)

      -------------------
      -- Generic


      -- Πⱼ_▹_     : ∀ {F G}
      --           → Γ     ⊢ F ∶ U
      --           → Γ ∙ F ⊢ G ∶ U
      --           → Γ     ⊢ Π F ▹ G ∶ U
      -- Σⱼ_▹_     : ∀ {F G}
      --           → Γ     ⊢ F ∶ U
      --           → Γ ∙ F ⊢ G ∶ U
      --           → Γ     ⊢ Σ F ▹ G ∶ U
      ℕⱼ        : {{_ : isTrue (⊢ Γ)}} → Γ ⊢ NN ∶ UU / p
      Vecⱼ      : ∀ {F l}
                → Γ ⊢ F ∶ UU / p
                → Γ ⊢ l ∶ NN / p
                → Γ ⊢ Vec F l ∶ UU / p
      -- Emptyⱼ    : ⊢ Γ → Γ ⊢Sort Empty ∶ U
      -- Unitⱼ     : ⊢ Γ → Γ ⊢Sort Unit ∶ U

      var       : ∀ {A x}
                -> {{ΓP : isTrue (⊢ Γ)}}
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

      zeroⱼ     :  {{_ : isTrue (⊢ Γ)}}
                → Γ ⊢ zeroₜ ∶ NN / p
      sucⱼ      : ∀ {n}
                → Γ ⊢      n ∶ NN / p
                → Γ ⊢ sucₜ n ∶ NN / p

      natrecⱼ   : ∀ {G s z n}
                → (Γ ∙ (NN / ▲ U) ⊢Sort G)
                → Γ       ⊢ z ∶ G [ zeroₜ ] / p
                → Γ       ⊢ s ∶ Π NN ▹ (G ▹▹ G [ sucₜ (var x0) ]↑) / p
                → Γ       ⊢ n ∶ NN / p
                → Γ       ⊢ natrec G z s n ∶ G [ n ] / p

      nilⱼ      : ∀ {A}
                → Γ ⊢ nilₜ ∶ Vec A zeroₜ / p
      consⱼ     : ∀ {A v vs n}
                → Γ ⊢         v ∶ A / p
                → Γ ⊢        vs ∶ Vec A n / p
                → Γ ⊢ consₜ v vs ∶ Vec A (sucₜ n) / p

      vecrecⱼ   : ∀ {G A s z l v n}
                → {{_ : isTrue (Γ ∙ (Vec A l / p) ⊢Sort G)}}
                → Γ           ⊢ z ∶ G [ nilₜ ] / p
                → Γ           ⊢ v ∶ A / p
                → Γ           ⊢ s ∶ Π (Vec A l) ▹ (G ▹▹ G [ consₜ (wk1 v) (var x0) ]↑) / p
                → Γ           ⊢ vecrec G z s n ∶ G [ n ] / p


      -- sndⱼ      : ∀ {F G t}
      --           → Γ ⊢Sort F
      --           → Γ ∙ F ⊢ G
      --           → Γ ⊢Sort t ∶ Σ F ▹ G
      --           → Γ ⊢Sort snd t ∶ G [ fst t ]


      locⱼ : Γ ⊢ t ∶ A / ▲ U -> Γ ⊢ loc U t ∶ (A ＠ U) / ◯
      unlocⱼ : Γ ⊢ t ∶ (A ＠ U) / ◯ -> Γ ⊢ unloc t ∶ A / ▲ U





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
    -- data _⊢_≡_ (Γ : Con (Term P) n) : Term P n → Term P n → Set where
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
  --   data _⊢_≡_∶_ (Γ : Con (Term P) n) : Term P n → Term P n → Term P n → Set where
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
  -- data _⊢_⇒_∶_ (Γ : Con (Term P) n) : Term P n → Term P n → Term P n → Set where
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
  data _⊢_⇒_ (Γ : Con (Term P) n) : Term P n → Term P n → Set where
    univ : ∀ {A B}
        → Γ ⊢Sort A ⇒ B ∶ U
        → Γ ⊢Sort A ⇒ B

  -- Term reduction closure
  data _⊢_⇒*_∶_ (Γ : Con (Term P) n) : Term P n → Term P n → Term P n → Set where
    id  : ∀ {A t}
        → Γ ⊢Sort t ∶ A
        → Γ ⊢Sort t ⇒* t ∶ A
    _⇨_ : ∀ {A t t′ u}
        → Γ ⊢Sort t  ⇒  t′ ∶ A
        → Γ ⊢Sort t′ ⇒* u  ∶ A
        → Γ ⊢Sort t  ⇒* u  ∶ A

  -- Type reduction closure
  data _⊢_⇒*_ (Γ : Con (Term P) n) : Term P n → Term P n → Set where
    id  : ∀ {A}
        → Γ ⊢Sort A
        → Γ ⊢Sort A ⇒* A
    _⇨_ : ∀ {A A′ B}
        → Γ ⊢Sort A  ⇒  A′
        → Γ ⊢Sort A′ ⇒* B
        → Γ ⊢Sort A  ⇒* B

  -- Type reduction to whnf
  _⊢_↘_ : (Γ : Con (Term P) n) → Term P n → Term P n → Set
  Γ ⊢Sort A ↘ B = Γ ⊢Sort A ⇒* B × Whnf B

  -- Term reduction to whnf
  _⊢_↘_∶_ : (Γ : Con (Term P) n) → Term P n → Term P n → Term P n → Set
  Γ ⊢Sort t ↘ u ∶ A = Γ ⊢Sort t ⇒* u ∶ A × Whnf u

  -- Type equality with well-formed types
  _⊢_:≡:_ : (Γ : Con (Term P) n) → Term P n → Term P n → Set
  Γ ⊢Sort A :≡: B = Γ ⊢Sort A × Γ ⊢Sort B × (Γ ⊢Sort A ≡ B)

  -- Term equality with well-formed terms
  _⊢_:≡:_∶_ : (Γ : Con (Term P) n) → Term P n → Term P n → Term P n → Set
  Γ ⊢Sort t :≡: u ∶ A = (Γ ⊢Sort t ∶ A) × (Γ ⊢Sort u ∶ A) × (Γ ⊢Sort t ≡ u ∶ A)

  -- Type reduction closure with well-formed types
  record _⊢_:⇒*:_ (Γ : Con (Term P) n) (A B : Term P n) : Set where
    constructor [_,_,_]
    field
      ⊢A : Γ ⊢Sort A
      ⊢B : Γ ⊢Sort B
      D  : Γ ⊢Sort A ⇒* B

  open _⊢_:⇒*:_ using () renaming (D to red; ⊢A to ⊢A-red; ⊢B to ⊢B-red) public

  -- Term reduction closure with well-formed terms
  record _⊢_:⇒*:_∶_ (Γ : Con (Term P) n) (t u A : Term P n) : Set where
    constructor [_,_,_]
    field
      ⊢t : Γ ⊢Sort t ∶ A
      ⊢u : Γ ⊢Sort u ∶ A
      d  : Γ ⊢Sort t ⇒* u ∶ A

  open _⊢_:⇒*:_∶_ using () renaming (d to redₜ; ⊢t to ⊢t-redₜ; ⊢u to ⊢u-redₜ) public

  -- Well-formed substitutions.
  data _⊢ˢ_∶_ (Δ : Con Term m) : (σ : Subst m n) (Γ : Con (Term P) n) → Set where
    id  : ∀ {σ} → Δ ⊢ˢ σ ∶ ε
    _,_ : ∀ {A σ}
        → Δ ⊢ˢ tail σ ∶ Γ
        → Δ ⊢  head σ ∶ subst (tail σ) A
        → Δ ⊢ˢ σ      ∶ Γ ∙ A

  -- Conversion of well-formed substitutions.
  data _⊢ˢ_≡_∶_ (Δ : Con Term m) : (σ σ′ : Subst m n) (Γ : Con (Term P) n) → Set where
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



