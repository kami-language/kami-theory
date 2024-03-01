
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples.CrispInduction where

open import Data.Fin using (#_ ; zero ; suc ; Fin)
open import Data.List using (_∷_ ; [])
open import Data.Vec using ([] ; _∷_ ; _++_) renaming (Vec to StdVec)

open import Agora.Conventions hiding (_∙_ ; _∷_ ; k ; const ; _∣_)
open import Agora.Order.Preorder
open import Agora.Setoid.Definition
-- open import Agora.Order.Lattice
-- open import Agora.Data.Normal.Definition
-- open import Agora.Data.Normal.Instance.Setoid
-- open import Agora.Data.Normal.Instance.Preorder
-- open import Agora.Data.Normal.Instance.Lattice
-- open import Agora.Data.Normal.Instance.DecidableEquality

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

-- open import KamiTheory.Data.Open.Definition
-- open import KamiTheory.Data.UniqueSortedList.Definition
-- open import KamiTheory.Order.StrictOrder.Base
-- open import KamiTheory.Order.StrictOrder.Instances.UniqueSortedList
-- open import KamiTheory.Main.Dependent.Modality.Definition




module Examples where
  -- instance
  --   hasDecidableEquality:𝔽 : hasDecidableEquality (𝔽 n)
  --   hasDecidableEquality:𝔽 = hasDecidableEquality:byStrictOrder

  -- isStrictOrder:𝒫ᶠⁱⁿ𝔽3 : hasStrictOrder (𝒫ᶠⁱⁿ (𝔽 3))
  -- isStrictOrder:𝒫ᶠⁱⁿ𝔽3 = it

  -- 𝒫𝔽3 : SortableDecidablePreorder _
  -- 𝒫𝔽3 = 𝒫ᶠⁱⁿ (𝔽 3)

  -- QQ : Preorder _
  -- QQ = 𝒪ᶠⁱⁿ (𝒫𝔽3)

  -- {-# INLINE QQ #-}

  -- PP : Preorder _
  -- PP = -- QQ
  --    ′_′ (Normalform ((𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 3))) since isNormalizable:𝒪ᶠⁱⁿ⁻ʷᵏ)) {_} {{isPreorder:𝒩 {{isPreorder:𝒪ᶠⁱⁿ⁻ʷᵏ {{isSetoid:𝒫ᶠⁱⁿ}} {{isPreorder:𝒫ᶠⁱⁿ}} {{isDecidablePreorder:≤-𝒫ᶠⁱⁿ}}}}}}


  -- singleton : {A : 𝒰 𝑖} -> {{_ : hasDecidableEquality A}} -> (a : A) -> A -> 𝟚
  -- singleton a b with a ≟ b
  -- ... | no x = false
  -- ... | yes x = true


  PP : Preorder _
  PP = ′ StdVec 𝟚 3 ′
  -- 𝔽 3 →# 𝟚

  singleton : Fin 3 -> ⟨ PP ⟩
  singleton i = singletonVec true false i 

  M : ModeSystem _
  M = SendReceiveNarrow-ModeSystem.SRN-ModeSystem PP {{it}} {{{!!}}}


  open Judgements M

  open Typecheck M

  open SendReceiveNarrow-2Graph
  open 2CellDefinition (graph M) hiding ( [_])

  instance
    _ : ∀{a b : ⟨ PP ⟩} -> isProp (a ≤ b)
    _ = {!!}



  -- uu : ⟨ PP ⟩
  -- uu = (((⦗ # 0 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  -- vv : ⟨ PP ⟩
  -- vv = (((⦗ # 1 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  -- ww : ⟨ PP ⟩
  -- ww = (((⦗ # 2 ⦘ ∷ []) since (IB.[] IB.∷ IB.[])) since incl [-])

  -- all = uu ∨ vv ∨ ww

  -- open Typecheck (PP) {{hasDecidableEquality:𝒩}} {{isDecidablePreorder:𝒩}}


  P : 𝒰 _
  P = ⟨ PP ⟩

  uu vv ww : P
  uu = singleton (# 0)
  vv = singleton (# 1)
  ww = singleton (# 2)

  uuvv : P
  uuvv = false ∷ (false ∷ (true ∷ []))

  pattern UVP = false ∷ false ∷ true ∷ []
  pattern UP = false ∷ true ∷ true ∷ []
  pattern VP = true ∷ false ∷ true ∷ []


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



  -- _⟶_ = _▹▹_

  private variable
    -- n m : Nat
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

  _⊢_≔_ : (Γ : Con (Entry M) n) → Target n → Term M n → Set
  Γ ⊢ E ≔ t = Γ ⊢ t ∶ E

  εε : Con (Entry M) zero
  εε = ε


  idM : (a : Mode M) -> ModeHom M a a
  idM a = id

  pattern ＠ u = `＠` u ⨾ id
  pattern ◻ = `[]` ⨾ id



  ---------------------------------------------
  -- small examples

  -- P0 : εε ∙ (NN / (＠ uu)) ⊢ var zero (incl idT[ ＠ uu ]) ∶ NN ∥ ((＠ uu) ∷ [])
  P0 : εε ∙ (NN / (＠ uu)) ⊢ _ ∶ NN ∥ ((＠ uu) ∷ [])
  P0 = var zero idTⱼ
  -- x0[ ? ]ⱼ


  Test : ⊢Ctx (εε ∙ (NN / (＠ uu))) ∥ (＠ uu ∷ [])
  Test = ε ∙ NNⱼ {{because ε}}


  P1 : εε ⊢ ⟨ NN ∣ ＠ uu ⟩ /▹▹ ⟨ NN ∣ ＠ uu ⟩ ∥ []
       ≔ lam↦ letunmod x0 into ⟨ NN ∣ ＠ uu ⟩ by mod[ ＠ uu ] x0
  P1 = lamⱼ (Modalⱼ (NNⱼ)) ↦ (letunmodⱼ[ id ] (var zero idTⱼ) into (Modalⱼ (NNⱼ)) by (modⱼ ((var zero idTⱼ))))



  -- wk-Entry : Γ ⊢Entry A / μ -> Γ ∙ (B / η) ⊢Entry wk1 A / μ
  -- wk-Entry = {!!}

  wk-Term : Γ ⊢ t ∶ A ∥ μs -> Γ ∙ (B / η) ⊢ wk1 t ∶ wk1 A ∥ (id ∷ μs)
  wk-Term = {!!}

  -- wk-Term : Γ ⊢ t ∶ A ∥ (μ ◆ ν) ↳ μs -> Γ ∙ (B / η) ⊢ wk1 t ∶ wk1 A ∥ (μ ∷ ν ↳ μs)
  -- wk-Term = {!!}

  wk-Term[_,_] : ∀ (μ : ModeHom M k l) (ν : ModeHom M l o) -> Γ ⊢ t ∶ A ∥ (μ ◆ ν) ↳ μs -> Γ ∙ (B / η) ⊢ wk1 t ∶ wk1 A ∥ (μ ∷ ν ↳ μs)
  wk-Term[_,_] μ ν tp = {!!}



  -- Axiom K
  -- (Every modality commutes with products)
  --
  -- AxiomK :
  --        (⊢Ctx Γ)
  --        -> (Γ ⊢Entry A / μ)
  --        -> (Γ ⊢Entry B / μ)
  --        -> Γ ⊢ (Modal (A ×× B) μ / id) ▹▹ (Modal A μ) ×× (Modal B μ) / id
  --          ≔ {!!}
  -- AxiomK {Γ = Γ} {A = A} {μ = μ} {B = B} Γp Ap Bp =

  --   let Cp : Γ ⊢Entry Modal (A ×× B) μ / id
  --       Cp = Modalⱼ ((Σⱼ Ap ▹ wk-Entry Bp))

  --   in lamⱼ Cp
  --     (letunmodⱼ (Σⱼ {!Modalⱼ ?!} ▹ {!!}) (var {{because (Γp ∙ Cp)}} zero idT)
  --     {!!})

  -- AxiomK-Example :
  --        ε ⊢ (Modal (NN ×× BB) μ / id) ▹▹ (Modal NN μ) ×× (Modal BB μ) / id
  --          ≔ {!!}
  -- AxiomK-Example {μ = μ} =

  --   let Cp : ε ⊢Entry Modal (NN ×× BB) μ / id
  --       Cp = Modalⱼ ((Σⱼ NNⱼ ▹ BBⱼ))

  --   in lamⱼ Cp
  --     (letunmodⱼ (Σⱼ Modalⱼ (NNⱼ {{because {!!}}}) ▹ Modalⱼ (BBⱼ {{{!!}}})) (var {{because (ε ∙ Cp)}} zero idT)
  --     (prodⱼ (Modal NN μ) (Modal BB μ) {{{!!}}} {{{!!}}} (modⱼ (fstⱼ (var {{{!!}}} zero idT))) ((modⱼ (sndⱼ (var {{{!!}}} zero idT))))))


  -- _××ⱼ_  : {μ : ModeHom M k l}
  --         → Γ ⊢Entry (A / μ)
  --         → Γ ⊢Entry (B / μ)
  --         → Γ ⊢Entry ((Σ A // incl (k ↝ k ∋ id) ▹ wk1 B) / μ)
  -- _××ⱼ_ Ap Bp = Σⱼ Ap ▹ wk-Entry Bp


  ---------------------------------------------
  -- Prop (Axiom K): Arbitrary Modal types commute with products
  --
  {-
  AxiomK : ε ⊢ Π UU / μ ▹ Π UU / μ ▹ ⟨ x1 ×× x0 ∣ μ ⟩ /▹▹ ⟨ x1 ∣ μ ⟩ ×× ⟨ x0 ∣ μ ⟩ / id
           ≔ lam↦ lam↦ lam↦ letunmod x0 by (mod[ μ ] (fstₜ x0) ,, mod[ μ ] (sndₜ x0))
  AxiomK {μ = μ} = lamⱼ UUⱼ ↦
                   lamⱼ UUⱼ ↦
                   lamⱼ Modalⱼ (Univⱼ x1ⱼ ××ⱼ Univⱼ x0ⱼ) ↦
                   letunmodⱼ x0ⱼ
                     into Modalⱼ (Univⱼ x3ⱼ) ××ⱼ Modalⱼ (Univⱼ x2ⱼ)
                     by
                   introⱼΣ Modalⱼ (Univⱼ x3ⱼ) ▹ Modalⱼ (Univⱼ x3ⱼ)
                     by
                   modⱼ (fstⱼ x0ⱼ) , modⱼ (sndⱼ x0ⱼ)
  -}

  ---------------------------------------------
  -- Prop: We can state the unit and counit of the (＠ u ⊣ ◻) adjunction.
  --
  -- We call the unit of this adjunction "dispatch", because it allows
  -- us to schedule computations (at possibly different) locations.
  --
  ηᵈˢ : ∀{u} -> ModeTrans* M all (id) (`＠` u ⨾ ◻)
  ηᵈˢ {u = u} = [ incl [] ∣ (incl (incl (id ⌟[ send u ]⌞ id ⌟) ∷ [])) ]

  _★ηᵈˢ★_ : (μ : ModeHom M k ▲) (η : ModeHom M ▲ l) -> ∀{u} -> ModeTrans* M all ((μ ◆ η)) ((μ ◆ ＠ u ◆ ◻ ◆ η))
  _★ηᵈˢ★_ μ η {u = u} = [ incl [] ∣ (incl (incl (μ ⌟[ send u ]⌞ η ⌟) ∷ [])) ]

  dispatch : ε ⊢ (Π UU /▹ x0 /▹▹ ⟨ x0[ ηᵈˢ ] ∣ ＠ uu ◆ ◻  ⟩) ∥ []
             ≔ lam↦ lam↦ mod[ ＠ uu ◆ ◻ ] x0[ ηᵈˢ ]
  dispatch = lamⱼ UUⱼ ↦
             lamⱼ Univⱼ x0ⱼ ↦
             modⱼ x0[ ηᵈˢ ]ⱼ

  --
  -- The counit on the other hand allows us to wait for the execution
  -- of previously dispatched executions. We thus call it "sync".
  --
  εᵈˢ : ∀{u} -> ModeTrans* M all ((◻ ◆ ＠ u)) (id)
  εᵈˢ {u = u} = [ incl [] ∣ (incl (incl (id ⌟[ recv u ]⌞ id ⌟) ∷ [])) ]

  _★εᵈˢ★_ : (μ : ModeHom M k ◯) (η : ModeHom M ◯ l) -> ∀{u} -> ModeTrans* M all ((μ ◆ ◻ ◆ ＠ u ◆ η)) ((μ ◆ η))
  _★εᵈˢ★_ μ η {u = u} = [ incl [] ∣ (incl (incl (μ ⌟[ recv u ]⌞ η ⌟) ∷ [])) ]

  sync : ε ⊢ (Π UU / (◻ ◆ ＠ uu) ▹ ⟨ x0 ∣ ◻ ◆ ＠ uu  ⟩ /▹▹ x0[ εᵈˢ ]) ∥ []
         ≔ lam↦ lam↦ letunmod x0 into x2[ εᵈˢ ] by x0[ εᵈˢ ]
  sync = lamⱼ UUⱼ ↦
         lamⱼ Modalⱼ (Univⱼ x0ⱼ) ↦
         letunmodⱼ x0ⱼ into Univⱼ x2[ εᵈˢ ]ⱼ by
         x0[ εᵈˢ ]ⱼ

  sync' : ∀{u} -> ε ⊢ (Π UU / (◻ ◆ ＠ u) ▹ ⟨ ⟨ x0 ∣ ◻ ⟩ ∣ ＠ u ⟩ /▹▹ x0[ εᵈˢ ]) ∥ []
         ≔ lam↦ lam↦ letunmod x0 into x2[ εᵈˢ ] by (letunmod[ ＠ u ] x0 into x3[ εᵈˢ ] by x0[ εᵈˢ ])
  sync' {u = u} =
    lamⱼ UUⱼ ↦
    lamⱼ Modalⱼ (Modalⱼ (Univⱼ x0ⱼ)) ↦
    letunmodⱼ x0ⱼ into Univⱼ x2[ εᵈˢ ]ⱼ by
    letunmodⱼ[ ＠ u ] x0ⱼ into Univⱼ x3[ εᵈˢ ]ⱼ by
    x0[ εᵈˢ ]ⱼ






  -- Res = derive-Ctx GG

  _[_]ⱼ : Γ ∙ (A / μ) ⊢ s ∶ B ∥ (id ∷ μs) -> Γ ⊢ t ∶ A ∥ (μ ↳ μs) -> Γ ⊢ (s [ t ]) ∶ B [ t ] ∥ μs
  _[_]ⱼ = {!!}

  -- WITHOUT APP
  -- boolrecⱼ-crisp-h : (Γ ∙ (BB / ＠ uu) ⊢ C ∶ UU  ∥ (id ∷ (◻ ◆ ＠ uu ↳ μs)))
  --                    -> Γ ⊢ 
  --                         Π BB /▹
  --                         ⟨ C [ falseₜ ]  ∣ ◻ ⟩ /▹▹
  --                         ⟨ x1 ∘[ ＠ uu ] trueₜ ∣ ◻ ⟩ /▹▹
  --                         ⟨ x1 ∘[ ＠ uu ] x0[ _★ηᵈˢ★_ id id ] ∣ ◻ ⟩
  --                         ∥ (＠ uu ↳ μs) ≔ _
  -- boolrecⱼ-crisp-h Cp = lamⱼ BBⱼ {{{!!}}} ↦
  --                       lamⱼ Modalⱼ ((Univⱼ ({!wk-Term Cp [ ? ]ⱼ!}))) ↦
  --                       lamⱼ {!!} ↦
  --                       {!!}




  ----------------------------------------------------------
  -- Canonical boolrec
  ----------------------------------------------------------

  {-
  boolrec-crisp-h : εε ⊢ (Π (Π BB / (＠ uu) ▹ UU) / ◻ ◆ ＠ uu ▹
                         ⟨
                          Π BB /▹
                          ⟨ x1 ∘[ ＠ uu ] falseₜ ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ ＠ uu ] trueₜ ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ ＠ uu ] x0[ _★ηᵈˢ★_ id (＠ uu) ] ∣ ◻ ⟩
                         ∣
                          ＠ uu
                         ⟩)
                          ∥ []
                       ≔ _

  boolrec-crisp-h = lamⱼ Πⱼ BBⱼ ▹ UUⱼ ↦ modⱼ
                    (lamⱼ BBⱼ ↦
                     lamⱼ Modalⱼ (Univⱼ (x1ⱼ ∘ⱼ falseⱼ)) ↦
                     lamⱼ Modalⱼ (Univⱼ (x2ⱼ ∘ⱼ trueⱼ)) ↦
                     boolrecⱼ x2ⱼ into Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id (＠ uu) ]ⱼ))
                       false: x1ⱼ
                       true: x0ⱼ
                    )



  boolrec-crisp : εε ⊢
    Π (Π BB / (＠ uu) ▹ UU) / (◻ ◆ ＠ uu) ▹
    Π BB / ＠ uu ▹
    (x1 ∘[ ＠ uu ] falseₜ) / (◻ ◆ ＠ uu) ▹▹
    (x1 ∘[ ＠ uu ] trueₜ)  / (◻ ◆ ＠ uu) ▹▹
    (x1[ id ★εᵈˢ★ id ] ∘[ ＠ uu ] x0[ idTⱼ ]) ∥ []
    ≔ _
  boolrec-crisp =
    lamⱼ proof ↦
    lamⱼ proof ↦
    lamⱼ Univⱼ (x1ⱼ ∘ⱼ falseⱼ) ↦
    lamⱼ Univⱼ (x2ⱼ ∘ⱼ trueⱼ) ↦
      letunmodⱼ[ id ] wk-Term (wk-Term (wk-Term (wk-Term (boolrec-crisp-h)))) ∘ⱼ x3ⱼ
        into (Univⱼ (x4[ εᵈˢ ]ⱼ ∘ⱼ x3[ idTⱼ ]ⱼ))
        by
        (
          (wk-Term (wk-Term (wk-Term (wk-Term (wk-Term sync')))) ∘ⱼ (x4[ idTⱼ ]ⱼ ∘ⱼ x3[ id ★ηᵈˢ★ ＠ uu ]ⱼ))
          ∘ⱼ
          modⱼ ((x0ⱼ ∘ⱼ x3ⱼ ∘ⱼ modⱼ x2ⱼ ∘ⱼ modⱼ x1ⱼ))
        )

  -}






  ---------------------------------------------
  -- Prop: The naturals have a crisp induction
  -- principle under the `＠ u` modality.
  --
  -- We again begin by creating our helper function.


  natrec-crisp-h : ∀{u} -> εε ⊢ (Π (Π NN / (＠ u) ▹ UU) / ◻ ◆ ＠ u ▹
                         ⟨
                          Π NN /▹
                          ⟨ x1 ∘[ ＠ u ] zeroₜ ∣ ◻ ⟩ /▹▹
                          ⟨ Π NN / ＠ u ▹ ((x2 ∘[ ＠ u ] x0) /▹▹ (x2 ∘[ ＠ u ] (sucₜ x0))) ∣ ◻ ⟩ /▹▹
                          ⟨ x1 ∘[ ＠ u ] x0[ _★ηᵈˢ★_ id (＠ u) ] ∣ ◻ ⟩
                         ∣
                          ＠ u
                         ⟩)
                          ∥ []
                       ≔ _

  natrec-crisp-h {u = u} = lamⱼ Πⱼ NNⱼ ▹ UUⱼ ↦ modⱼ
                    (lamⱼ NNⱼ ↦
                     lamⱼ Modalⱼ (Univⱼ (x1ⱼ ∘ⱼ zeroⱼ)) ↦
                     lamⱼ Modalⱼ (Πⱼ NNⱼ {{{!!}}} ▹ (Πⱼ Univⱼ (x3ⱼ ∘ⱼ x0ⱼ) ▹ Univⱼ (x4ⱼ ∘ⱼ sucⱼ x1ⱼ))) ↦
                     natrecⱼ x2ⱼ into Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id (＠ u) ]ⱼ))
                       zero: x1ⱼ
                       suc: (lamⱼ NNⱼ {{{!!}}} ↦
                             lamⱼ Modalⱼ (Univⱼ (x4ⱼ ∘ⱼ x0[ _★ηᵈˢ★_ id (＠ u) ]ⱼ)) ↦
                             letunmodⱼ x0ⱼ
                               into (Modalⱼ (Univⱼ (x6ⱼ ∘ⱼ sucⱼ (x2[ _★ηᵈˢ★_ id (＠ u) ]ⱼ))))
                               by (letunmodⱼ x3ⱼ
                                     into (Modalⱼ (Univⱼ (x7ⱼ ∘ⱼ sucⱼ (x3[ _★ηᵈˢ★_ id (＠ u) ]ⱼ))))
                                     by modⱼ (x0ⱼ ∘ⱼ x3[ _★ηᵈˢ★_ id (＠ u) ]ⱼ ∘ⱼ x1ⱼ))
                            )
                    )


  natrec-crisp : ∀{u} -> εε ⊢
    Π (Π NN / ＠ u ▹ UU) / (◻ ◆ ＠ u) ▹
    Π NN / ＠ u ▹
    (x1 ∘[ ＠ u ] zeroₜ) / (◻ ◆ ＠ u) ▹▹
    (Π NN / ＠ u ▹ ((x2 ∘[ ＠ u ] x0) /▹▹ (x2 ∘[ ＠ u ] sucₜ x0))) / (◻ ◆ ＠ u) ▹▹
    (x1[ id ★εᵈˢ★ id ] ∘[ ＠ u ] x0) ∥ []
    ≔ _
  natrec-crisp {u = u} =
    lamⱼ proof ↦
    lamⱼ proof ↦
    lamⱼ Univⱼ (x1ⱼ ∘ⱼ zeroⱼ) ↦
    lamⱼ (Πⱼ NNⱼ {{{!!}}} ▹ (Πⱼ Univⱼ (x3ⱼ ∘ⱼ x0ⱼ) ▹ Univⱼ (x4ⱼ ∘ⱼ sucⱼ x1ⱼ))) ↦
      letunmodⱼ[ id ] wk-Term (wk-Term (wk-Term (wk-Term (natrec-crisp-h)))) ∘ⱼ x3ⱼ
        into (Univⱼ (x4[ εᵈˢ ]ⱼ ∘ⱼ x3[ idTⱼ ]ⱼ))
        by
        (
          (wk-Term (wk-Term (wk-Term (wk-Term (wk-Term sync')))) ∘ⱼ (x4[ idTⱼ ]ⱼ ∘ⱼ x3[ id ★ηᵈˢ★ ＠ u ]ⱼ))
          ∘ⱼ
          modⱼ ((x0ⱼ ∘ⱼ x3ⱼ ∘ⱼ modⱼ x2ⱼ ∘ⱼ modⱼ x1ⱼ))
        )
