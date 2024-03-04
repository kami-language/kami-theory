
----------------------------------------------------------
--
-- Example terms in the Kami language, Base
--
-- In this file we setup the Kami language itself,
-- by instantiating MTT with our SRN mode theory,
-- itself instantiated to a topology of 3 processes with
-- common knowledge.
--
-- We introduce various abbreviations to make terms more
-- readable, and show that one direction of the "Axiom K
-- equivalence" is derivable.
--
----------------------------------------------------------



{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.Base where

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition

open import KamiTheory.Basics hiding (typed)
open import KamiTheory.Order.Preorder.Instances
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances


open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Example
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition hiding ([_])
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Example
open import KamiTheory.Main.Generic.ModeSystem.Modality
open import KamiTheory.Main.Generic.ModeSystem.Transition





module ExamplesBase where


  -------------------
  -- The preorder of 3 processes with common knowledge is
  -- the standard preorder on `Fin 3 → Bool`, which inherits
  -- the structure from `Bool` itself. We encode such functions
  -- as bool-vectors of length 3. Note that while we actually
  -- have to take the opposite preorder of that, we do so implicitly
  -- by defining our singleton lists to be inverted, i.e., everywhere
  -- true except at the required position.
  PP : Preorder _
  PP = ′ StdVec 𝟚 3 ′

  -- Singletons are vectors with `true` everywhere except the required
  -- position
  singleton : Fin 3 -> ⟨ PP ⟩
  singleton i = singletonVec true false i

  -- We postulate that the relation is merely a proposition.
  postulate instance
    _ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)

  -------------------
  -- Various shorter notations
  P : 𝒰 _
  P = ⟨ PP ⟩

  -- We call the three processes `uu`, `vv` and `ww`
  uu vv ww : P
  uu = singleton (# 0)
  vv = singleton (# 1)
  ww = singleton (# 2)

  -- this is the common knowledge of both `uu` and `vv`
  uuvv : P
  uuvv = false ∷ (false ∷ (true ∷ []))

  pattern UVP = false ∷ false ∷ true ∷ []
  pattern UP = false ∷ true ∷ true ∷ []
  pattern VP = true ∷ false ∷ true ∷ []

  -------------------
  -- Instantiating the SRN modesystem with the PP preorder
  M : ModeSystem _
  M = SendReceiveNarrow-ModeSystem.SRN-ModeSystem PP {{it}} {{it}}

  open Judgements M public
  open Typecheck M public
  open SendReceiveNarrow-2Graph public
  open 2CellDefinition (graph M) hiding ( [_]) public


  -------------------
  -- Give names to variables, instead of writing lots of "suc"s
  --
  -- We need different versions for terms and for judgements.
  -- And we also have a special notation for variables where the
  -- mode transformation is the identity.

  pattern x0 = var zero (incl idT)
  pattern x1 = var (suc zero) (incl idT)
  pattern x2 = var (suc (suc zero)) (incl idT)
  pattern x3 = var (suc (suc (suc zero))) (incl idT)
  pattern x4 = var (suc (suc (suc (suc zero)))) (incl idT)
  pattern x0[_] ξ = var zero (incl (_ ⇒ _ ∋ ξ))
  pattern x1[_] ξ = var (suc zero) (incl (_ ⇒ _ ∋ ξ))
  pattern x2[_] ξ = var (suc (suc zero)) (incl (_ ⇒ _ ∋ ξ))
  pattern x3[_] ξ = var (suc (suc (suc zero))) (incl (_ ⇒ _ ∋ ξ))

  pattern x0ⱼ = var zero idTⱼ
  pattern x1ⱼ = var (suc zero) idTⱼ
  pattern x2ⱼ = var (suc (suc zero)) idTⱼ
  pattern x3ⱼ = var (suc (suc (suc zero))) idTⱼ
  pattern x4ⱼ = var (suc (suc (suc (suc zero)))) idTⱼ
  pattern x5ⱼ = var (suc (suc (suc (suc (suc zero))))) idTⱼ
  pattern x6ⱼ = var (suc (suc (suc (suc (suc (suc zero)))))) idTⱼ
  pattern x7ⱼ = var (suc (suc (suc (suc (suc (suc (suc zero))))))) idTⱼ

  pattern x0[_]ⱼ ξ = var zero ξ
  pattern x1[_]ⱼ ξ = var (suc zero) ξ
  pattern x2[_]ⱼ ξ = var (suc (suc zero)) ξ
  pattern x3[_]ⱼ ξ = var (suc (suc (suc zero))) ξ
  pattern x4[_]ⱼ ξ = var (suc (suc (suc (suc zero)))) ξ

  pattern x0ⱼ' P = var {{P}} zero idTⱼ
  pattern x1ⱼ' P = var {{P}} (suc zero) idTⱼ
  pattern x2ⱼ' P = var {{P}} (suc (suc zero)) idTⱼ
  pattern x3ⱼ' P = var {{P}} (suc (suc (suc zero))) idTⱼ


  variable
    p q : Term M n
    s t u : Term M n
    Γ  : Con (Entry M) n
    A C : Term M n
    B : Term M m
    U V W R : P
    k l o r : Mode M
    μ : ModeHom M k l
    η : ModeHom M o r
    ν : ModeHom M o r
    μs : Restriction k n

  -- Reversing the order of arguments for term judgements
  _⊢_≔_ : (Γ : Con (Entry M) n) → Target n → Term M n → Set
  Γ ⊢ E ≔ t = Γ ⊢ t ∶ E

  -- The empty context gets a special name
  εε : Con (Entry M) zero
  εε = ε

  -- the identity mode hom
  idM : (a : Mode M) -> ModeHom M a a
  idM a = id

  -- patterns for our modalities
  pattern ＠ u = `＠` u ⨾ id
  pattern ◻ = `[]` ⨾ id



  ---------------------------------------------
  -- small examples

  P0 : εε ∙ (NN / (＠ uu)) ⊢ _ ∶ NN ∥ ((＠ uu) ∷ [])
  P0 = var zero idTⱼ


  C0 : ⊢Ctx (εε ∙ (NN / (＠ uu))) ∥ (＠ uu ∷ [])
  C0 = ε ∙ NNⱼ {{because ε}}


  P1 : εε ⊢ ⟨ NN ∣ ＠ uu ⟩ /▹▹ ⟨ NN ∣ ＠ uu ⟩ ∥ []
       ≔ lam↦ letunmod x0 into ⟨ NN ∣ ＠ uu ⟩ by mod[ ＠ uu ] x0
  P1 = lamⱼ (Modalⱼ (NNⱼ)) ↦ (letunmodⱼ[ id ] (var zero idTⱼ) into (Modalⱼ (NNⱼ)) by (modⱼ ((var zero idTⱼ))))


  postulate
    wk-Type : Γ ⊢Type A ∥ μs -> Γ ∙ (B / η) ⊢Type wk1 A ∥ (id ∷ μs)
    wk-Term : Γ ⊢ t ∶ A ∥ μs -> Γ ∙ (B / η) ⊢ wk1 t ∶ wk1 A ∥ (id ∷ μs)



  _××ⱼ_  : {M : Restriction k _}
          → Γ ⊢Type (A ∥ M)
          → Γ ⊢Type (B ∥ M)
          → Γ ⊢Type ((Σ A // incl (k ↝ k ∋ id) ▹ wk1 B) ∥ M)
  _××ⱼ_ Ap Bp = Σⱼ Ap ▹ wk-Type Bp


  ---------------------------------------------
  -- We show that arbitrary modal types commute with products (Axiom K).
  --
  AxiomK : ε ⊢ Π UU / μ ▹ Π UU / μ ▹ ⟨ x1 ×× x0 ∣ μ ⟩ /▹▹ ⟨ x1 ∣ μ ⟩ ×× ⟨ x0 ∣ μ ⟩ ∥ []
           ≔ (lam↦ lam↦ lam↦ letunmod x0 into _ by (mod[ μ ] (fstₜ x0) ,, mod[ μ ] (sndₜ x0)))
  AxiomK {μ = μ} = lamⱼ UUⱼ ↦
                   lamⱼ UUⱼ ↦
                   lamⱼ Modalⱼ (Univⱼ x1ⱼ ××ⱼ Univⱼ x0ⱼ) ↦
                   letunmodⱼ x0ⱼ
                     into Modalⱼ (Univⱼ x3ⱼ) ××ⱼ Modalⱼ (Univⱼ x2ⱼ)
                     by
                   introⱼΣ Modalⱼ (Univⱼ x3ⱼ) ▹ Modalⱼ (Univⱼ x3ⱼ)
                     by
                   modⱼ (fstⱼ x0ⱼ) , modⱼ (sndⱼ x0ⱼ)


