
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Instances where

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Order.Lattice

open import KamiTheory.Basics
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
-- open import KamiTheory.Main.Dependent.Modality.Definition

open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import KamiTheory.ThirdParty.logrel-mltt.Tools.Fin
-- open import KamiTheory.ThirdParty.logrel-mltt.Tools.Nat
open import KamiTheory.ThirdParty.logrel-mltt.Tools.Product


-- module _ {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

-- module Typecheck (P' : Preorder (ℓ₀ , ℓ₀ , ℓ₀)) {{_ : hasDecidableEquality ⟨ P' ⟩}} {{_ : isDecidablePreorder ′ ⟨ P' ⟩ ′}} {{_ : hasFiniteMeets ′ ⟨ P' ⟩ ′}} where
-- {P : 𝒰 ℓ₀} {{_ : isSetoid {ℓ₀} P}} {{_ : isPreorder ℓ₀ ′ P ′}} {{_ : hasDecidableEquality P}} where

module Typecheck (P : ModeSystem 𝑖) where

  open Judgements P

  -- private
  --   P : 𝒰 _
  --   P = ⟨ graph P' ⟩

  private variable
    -- n m : Nat
    k l : Mode P
    μs : ModeHom P k l
    p q : Term P n
    t u : Term P n
    Γ  : Con (Entry P) n
    A B : Term P n
    E F : Entry P n
    -- W : P


  Result : 𝒰 𝑖 -> 𝒰 𝑖
  Result X = String +-𝒰 X

  map-Result : ∀{A B : 𝒰 𝑖} -> (A -> B) -> Result A -> Result B
  map-Result f (left a) = left a
  map-Result f (right b) = right (f b)

  bind-Result : ∀{A B : 𝒰 𝑖} -> Result A -> (A -> Result B) -> Result B
  bind-Result (left a) f = left a
  bind-Result (right b) f = f b

  private
    -- _>>=_ = bind-Maybe
    _>>=_ = bind-Result


  {-# TERMINATING #-}
  derive-Entry : ∀ (Γ : Con (Entry P) n) E -> Result (Γ ⊢Entry E)
  derive-Ctx : ∀ (Γ : Con (Entry P) n) -> Result (⊢Ctx Γ)
  derive-Term-Sort↓,Mod↓ : ∀ Γ -> (t A : Term P n) → (p : SomeModeHom P) -> Result (Γ ⊢ t ∶ A // p)

  derive-Term-Sort↑,Mod↑ : ∀ Γ -> (t : Term P n) → Result (∑ λ (E : Entry P n) -> (Γ ⊢ t ∶ E))


  derive-Entry Γ (UU / μs)    = map-Result (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (NN / μs)    = map-Result (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (BB / μs)    = map-Result (λ P -> BBⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Entry Γ (Vec A t // μs) = do
    A′ <- derive-Entry Γ (A // μs )
    t′ <- derive-Term-Sort↓,Mod↓ Γ t NN (μs)
    just (Vecⱼ A′ t′)

  derive-Entry Γ (gen (main 𝓀-Modal) (incl (l ↝ k0 ∋ μ) ⦊ term A ∷ []) // k1 ↝ m ∋ μs) with k0 ≟ k1
  ... | no p = no ""
  ... | yes refl-≡ = do
          A' <- derive-Entry Γ (A / μ ◆ μs)
          just (Modalⱼ A')

  -- map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)


  --derive-Entry Γ (Unit / μs)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  --derive-Entry Γ (L ＠ U / ◯)  = map-Maybe (Locⱼ U) (derive-Entry Γ (L / μs))
  --derive-Entry Γ (Com R A / ◯)  = map-Maybe Comⱼ (derive-Entry Γ (A / ◯))
  {- derive-Entry Γ (Σ (A / ML p) ▹ B / ML q) with p ≟ q
  ... | left x = nothing
  ... | just refl-≡ = do
    A' <- derive-Entry Γ (A / ML p)
    B' <- derive-Entry (Γ ∙ (A / ML q)) (B / ML q)
    just (Σⱼ A' ▹ B')
    -}
  derive-Entry Γ (var x ξ // η) = do
    res <- derive-Term-Sort↓,Mod↓ Γ (var x ξ) UU η
    just (Univⱼ res)
  derive-Entry Γ ((t ∘[ μ ] s) // η) = do
    res <- derive-Term-Sort↓,Mod↓ Γ (t ∘[ μ ] s) UU η
    just (Univⱼ res)
  derive-Entry Γ ((Π A // incl (_ ↝ k ∋ μ) ▹ B) // l ↝ _ ∋ η) with k ≟ l
  ... | no _ = no "fail in Entry Π"
  ... | yes refl = do
    A' <- derive-Entry Γ (A / (μ))
    B' <- derive-Entry (Γ ∙ (A / μ)) (B / η)
    just (Πⱼ A' ▹ B')
  derive-Entry Γ ((Σ A // incl (k0 ↝ k ∋ μ) ▹ B) // l ↝ _ ∋ η) with k ≟ l
  ... | no _ = no "fail in Entry Σ"
  ... | yes refl with k0 ≟ k
  ... | no _ = no "fail in Entry Σ"
  ... | yes refl with μ ≟ id
  ... | no _ = no "fail in Entry Σ"
  ... | yes refl = do
    A' <- derive-Entry Γ (A / η)
    B' <- derive-Entry (Γ ∙ (A / η)) (B / η)
    just (Σⱼ A' ▹ B')
  derive-Entry Γ E = no "fail in Entry: not implemented"


  derive-Ctx ε = just ε
  derive-Ctx (Γ ∙ E) = do
    E' <- derive-Entry Γ E
    Γ' <- derive-Ctx Γ
    just (Γ' ∙ E')
{-
  derive-Sort : ∀ (Γ : Con (Term P) n) E -> Maybe (Γ ⊢Sort E)
  derive-Sort Γ (UU)    = map-Maybe (λ P -> UUⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (NN)    = map-Maybe (λ P -> NNⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Empty) = map-Maybe (λ P -> Emptyⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  derive-Sort Γ (Unit)  = map-Maybe (λ P -> Unitⱼ {{ΓP = because P}}) (derive-Ctx Γ)
  -- derive-Sort Γ (L ＠ U)  = map-Maybe (Locⱼ U) (derive-Sort Γ (L))
  derive-Sort Γ E = nothing
-}

  infer-Var : ∀ Γ -> (t : Fin n) -> ∑ λ (E : Entry P n) -> (t ∶ E ∈ Γ)
  infer-Var (Γ ∙ x) x0 = _ , zero
  infer-Var (Γ ∙ x) (_+1 t) with (E , Ep) <- infer-Var Γ t = _ , suc Ep

  derive-Var-Sort↓,Mod↓ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → (p : SomeModeHom P) -> Maybe (t ∶ A // p ∈ Γ)
  derive-Var-Sort↓,Mod↓ Γ t A p with infer-Var Γ t
  ... | (E , Ep) with E ≟ (A // p)
  ... | no p = nothing
  ... | yes refl-≡ = yes Ep

  derive-Var-Sort↓,Mod↑ : ∀ Γ -> (t : Fin n) -> (A : Term P n) → Maybe (∑ λ μs -> t ∶ A // μs ∈ Γ)
  derive-Var-Sort↓,Mod↑ Γ t A with infer-Var Γ t
  ... | ((A' // μs) , Ap) with A ≟ A'
  ... | no p = nothing
  ... | yes refl-≡ = yes (μs , Ap)


  ------------------------------------------------------------------------
  -- Terms (infering Sort, infering Mod)

  -- derive-Term-Sort↑,Mod↑ : ∀ Γ -> (t : Term P n) -> Maybe (∑ λ (E : Entry P n) -> Γ ⊢ t ∶ E)
  derive-Term-Sort↑,Mod↑ Γ (var x (incl (μ ⇒ η ∋ ξ)))
    with ((vA // μ') , A') <- infer-Var Γ x
    with (_ ↝ _ ∋ μ) ≟ μ'
  ... | no p = no "fail in Sort↑,Mod↑: var, modalities don't match"
  ... | yes refl = do
    G' <- derive-Ctx Γ
    just ((vA ^[ _ ⇒ _ ∋ ξ ] / η) , var A' (_ ⇒ _ ∋ ξ))
    -- just ((vA ^[ _ ⇒ _ ∋ ξ ] / η) , var {{ΓP = because G'}} A' (_ ⇒ _ ∋ ξ))

  derive-Term-Sort↑,Mod↑ Γ _ = no "fail in Sort↑,Mod↑: not implemented"

  -- derive-Term-Sort↑,Mod↑ Γ t = nothing

  ------------------------------------------------------------------------
  -- Terms (checking Sort, infering Mod)
  -- derive-Term-Sort↓,Mod↑ : ∀ Γ -> (t A : Term P n) -> Maybe (∑ λ (μs : Modality P) -> Γ ⊢ t ∶ (A // μs))
  -- derive-Term-Sort↓,Mod↑ Γ (var x) A with derive-Var-Sort↓,Mod↑ Γ x A
  -- ... | nothing = nothing
  -- ... | yes (μs , Ap) = do
  --   G' <- derive-Ctx Γ
  --   yes (μs , var {{ΓP = because G'}} Ap)

  -- derive-Term-Sort↓,Mod↑ Γ t A = nothing

  ------------------------------------------------------------------------
  -- Terms (checking Sort, checking Mod)

  -------------------
  -- modalities
  derive-Term-Sort↓,Mod↓ Γ (mod[[ incl μ ]] t) (Modal A (incl μ')) η with μ ≟ μ'
  ... | no _ = no "fail in Sort↓,Mod↓: mod, modalities don't match"
  ... | yes refl with μ .cod ≟ η .dom
  ... | no _ = no "fail in Sort↓,Mod↓: mod, modalities don't match"
  ... | yes refl with derive-Term-Sort↓,Mod↓ Γ t A (_ ↝ _ ∋ (hom μ ◆ hom η))
  ... | no msg =  no ("fail in Sort↓,Mod↓: mod:: " <> msg)
  ... | yes Ap = yes (modⱼ Ap)


  derive-Term-Sort↓,Mod↓ Γ (letunmod[[ incl μ ]] t into Y by s) Y' ω
    with dom ω ≟ cod μ
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, modalities don't match ")
  ... | yes refl

    with derive-Term-Sort↑,Mod↑ Γ t
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes (T@(X' // μω') , tP)

   with X'
  ... | (Modal X (incl η))

   with μω' ≟ (_ ↝ _ ∋ (hom μ ◆ hom ω))
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, modalities don't match ")
  ... | yes refl

   with cod η ≟ dom μ
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, modalities don't match ")
  ... | yes refl

    with derive-Entry (Γ ∙ (Modal X (incl η) // μω')) (Y // ω)
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes Yp

    with derive-Term-Sort↓,Mod↓ (Γ ∙ (X / hom η ◆ hom μ ◆ hom ω)) s (Y [ mod[[ incl μ ]] (var x0 id) ]↑) ω
  ... | no msg = no ("fail in Sort↓,Mod↓: letunmod:: " <> msg)
  ... | yes sP

    with Y [ t ] ≟ Y'
  ... | no _ = no ("fail in Sort↓,Mod↓: letunmod, motive type doesn't match")
  ... | yes refl

    = yes (letunmodⱼ[ hom μ ] tP into Yp by sP)

  derive-Term-Sort↓,Mod↓ Γ (letunmod[[ incl μ ]] t into Y by s) Y' ω | yes _ | yes _ | _ = no ("fail in Sort↓,Mod↓: letunmod, first term is not of modal type")



-- no "fail in Sort↓,Mod↓: `mod` not implemented"

  -- modality interactions
  -- derive-Term-Sort↓,Mod↓ Γ (narrow t) A (k ↝ l ∋ (`＠` V ⨾ μs)) with derive-Term-Sort↓,Mod↑ Γ t A
  -- ... | nothing = nothing
  -- ... | yes (m ↝ m ∋ id , t') = nothing
  -- ... | yes (.◯ ↝ n ∋ `[]` ⨾ ηs , t') = nothing
  -- ... | yes (.▲ ↝ n ∋ `＠` U ⨾ ηs , t') with n ≟ l
  -- ... | no p = nothing
  -- ... | yes refl with μs ≟ ηs
  -- ... | no p = nothing
  -- ... | yes refl with decide-≤ U V
  -- ... | no p = nothing
  -- ... | yes ϕ = yes (narrowⱼ ϕ t')

  -------------------
  -- standard MLTT
  derive-Term-Sort↓,Mod↓ Γ (var x (incl (μ ⇒ η ∋ ξ))) A η' with (infer-Var Γ x)
  ... | ((vA // μ') , A') with (_ ↝ _ ∋ μ) ≟ μ'
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl with (_ ↝ _ ∋ η) ≟ η'
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl with vA ^[ _ ⇒ _ ∋ ξ ] ≟ A
  ... | no p = no "fail in Sort↓,Mod↓: var (incl)"
  ... | yes refl = do
    G' <- derive-Ctx Γ
    just (var A' (_ ⇒ _ ∋ ξ))
    -- just (var {{ΓP = because G'}} A' (_ ⇒ _ ∋ ξ))


  derive-Term-Sort↓,Mod↓ Γ (var x id) A μ = no "fail in Sort↓,Mod↓: var (id)"
  derive-Term-Sort↓,Mod↓ Γ (var x fail) A μ = no "fail in Sort↓,Mod↓: var (fail)"

  derive-Term-Sort↓,Mod↓ Γ (lam↦ t) (Π A // (incl η) ▹ B) μ
  --   with cod η ≟ dom μ
  -- ... | no _ = no "fail in Sort↓,Mod↓: lam, modalities don't match."
  -- ... | yes refl = do
    -- A' <- derive-Entry Γ (A / (hom η ◆ hom μ))
    -- t' <- derive-Term-Sort↓,Mod↓ (Γ ∙ (A / (hom η ◆ hom μ))) t B μ
    -- just (lamⱼ A' ↦ t')
      = do
    A' <- derive-Entry Γ (A / (hom η))
    t' <- derive-Term-Sort↓,Mod↓ (Γ ∙ (A / (hom η))) t B μ
    just (lamⱼ A' ↦ t')

  derive-Term-Sort↓,Mod↓ Γ (t ∘[[ incl η' ]] s) B' μ' = no "not implemented!" --  with derive-Term-Sort↑,Mod↑ Γ t
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes ((F // μ) , Fp) with μ ≟ μ'
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes refl with F
  -- ... | (Π A // incl ημ ▹ B) with dom μ ≟ cod η
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes refl with η ≟ η'
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes refl with derive-Term-Sort↓,Mod↓ Γ s A (_ ↝ _ ∋ (hom η ◆ hom μ))
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes sP with B' ≟ (B [ untransform-Term s ])
  -- ... | no p = no "fail in Sort↓,Mod↓: ∘"
  -- ... | yes refl = just (Fp ∘ⱼ sP)
  -- derive-Term-Sort↓,Mod↓ Γ (t ∘[[ incl η' ]] s) B' p | yes _ | yes _ | _ = no "fail in Sort↓,Mod↓: ∘, expected Π type"
  -- derive- nothing -- for checking an application we need `infer-Term`


  -- Boleans
  derive-Term-Sort↓,Mod↓ Γ (trueₜ) BB μ with derive-Ctx Γ
  ... | no p = no p
  ... | yes Γp = just (trueⱼ)
  -- ... | yes Γp = just (trueⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (falseₜ) BB μ with derive-Ctx Γ
  ... | no p = no p
  ... | yes Γp = just (falseⱼ )
  -- ... | yes Γp = just (falseⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (boolrec b into G false: f true: t) X μ with X ≟ G [ b ]
  ... | no p = no "fail in Sort↓,Mod↓: boolrec, Motive does not match"
  ... | yes refl = do
    bP <- derive-Term-Sort↓,Mod↓ Γ b BB μ
    GP <- derive-Entry (Γ ∙ (BB // μ)) (G // μ)
    fP <- derive-Term-Sort↓,Mod↓ Γ f (G [ falseₜ ]) μ
    tP <- derive-Term-Sort↓,Mod↓ Γ t (G [ trueₜ ]) μ
    yes (boolrecⱼ bP into GP false: fP true: tP)



  -- Naturals
  derive-Term-Sort↓,Mod↓ Γ (zeroₜ) NN μ with derive-Ctx Γ
  ... | no p = no p
  ... | yes Γp = just (zeroⱼ)
  -- ... | yes Γp = just (zeroⱼ {{because Γp}})

  derive-Term-Sort↓,Mod↓ Γ (sucₜ t) NN μ with derive-Term-Sort↓,Mod↓ Γ t NN μ
  ... | no p = no p
  ... | yes tp = just (sucⱼ tp)


  derive-Term-Sort↓,Mod↓ Γ _ A p = no "fail in Sort↓,Mod↓: not implemented"

  instance
    isDerivable:Con : isDerivable (⊢Ctx Γ)
    isDerivable:Con = record { derive = derive-Ctx _ }

  instance
    isDerivable:Entry : isDerivable (Γ ⊢Entry E)
    isDerivable:Entry = record { derive = derive-Entry _ _ }
{-
  instance
    isDerivable:Sort : isDerivable (Γ ⊢Sort A)
    isDerivable:Sort = record { derive = derive-Sort _ _ }
-}
  instance
    isDerivable:Term : isDerivable (Γ ⊢ t ∶ A / μs)
    isDerivable:Term = record { derive = derive-Term-Sort↓,Mod↓ _ _ _ _ }

  -- instance
  --   isDerivable:ModeTrans : ∀{m n v} -> {μs ηs : ModeHom P m n} -> isDerivable (ModeTrans μs ηs v)
  --   isDerivable:ModeTrans = record { derive = derive-ModeTrans _ _ }


  typecheck : ∀{μs} -> {@(tactic solveWith (derive-Term-Sort↓,Mod↓ Γ t A μs)) derivation : Γ ⊢ t ∶ A // μs} -> Γ ⊢ t ∶ A // μs
  typecheck {derivation = derivation} = derivation

