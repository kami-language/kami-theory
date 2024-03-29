-- SPDX-FileCopyrightText: 2024 Maxim Urschumzew <mxmurw@determi.io>
--
-- SPDX-License-Identifier: MIT

{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Dev.2024-01-20.Rules-OneSpace where

open import Agora.Conventions hiding (Σ ; Lift ; k ; m ; n ; Structure)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_ ; _≰_ ; _/_)
-- open import Relation.Nullary.Decidable.Core

open import KamiTheory.Dev.2024-01-20.Core hiding (_＠_)
open import KamiTheory.Dev.2024-01-20.UniqueSortedList hiding (img)
open import KamiTheory.Dev.2024-01-20.Space
open import KamiTheory.Dev.2024-01-20.Sheaf
open import KamiTheory.Dev.2024-01-20.Open
open import KamiTheory.Dev.2024-01-20.StrictOrder.Base

-- We have type contexts and normal contexts which additionally
-- contain location assignments.

---------------------------------------------
-- Base type layer

data BaseType : 𝒰₀ where
  BB NN : BaseType

--
-- We define a basic type theory with a global parameter P
--
Param = Space

private variable P : Param

---------------------------------------------
-- Normal type system layer


module _ {P : Param} where

  private
    isPreorder:P : isPreorder _ ′ ⟨ P ⟩ ′
    isPreorder:P = it

  private variable
    U V W : ⟨ P ⟩
    U₀ U₁ : ⟨ P ⟩
    W₀ W₁ : ⟨ P ⟩
    R : ⟨ P ⟩

  -- of_ : ℕ
  -- of_ = ?

  private variable
    ϕ : _≤_ {{isPreorder:P}} U V
    ψ : _≤_ {{isPreorder:P}} U₀ U₁

  Index = ⟨ P ⟩

  data Ctx (Ix : Index) : 𝒰₀

  private variable
    Γ : Ctx W
    Γ₀ Γ₁ : Ctx W

  -- setup of kinds for types and spaces
  data Kind : 𝒰₀ where
    global : Kind
    local : Kind
    com : ⟨ P ⟩ -> Kind

  private variable
    k l : Kind


  data _⊢Sort_ {W : Index} : ∀ (Γ : Ctx W) -> Kind -> 𝒰₀

  private variable
    S : Γ ⊢Sort k
    T : Γ ⊢Sort l
    T₀ : Γ ⊢Sort k
    T₁ : Γ ⊢Sort k
    S₀ : Γ ⊢Sort l
    S₁ : Γ ⊢Sort l


  GlobalSyntax : ∀ (Γ : Ctx W) -> 𝒰 _
  GlobalSyntax Γ = Γ ⊢Sort global

  syntax GlobalSyntax Γ = Γ ⊢Global

  private variable
    A : Γ ⊢Global
    B : Γ ⊢Global

  LocalSyntax : ∀ (Γ : Ctx W) -> 𝒰 _
  LocalSyntax Γ = Γ ⊢Sort local

  syntax LocalSyntax Γ = Γ ⊢Local

  private variable
    L : Γ ⊢Local
    M : Γ ⊢Local
    N : Γ ⊢Local

  ComSyntax : ∀ (Γ : Ctx W) -> ⟨ P ⟩ -> 𝒰 _
  ComSyntax Γ U = Γ ⊢Sort com U

  syntax ComSyntax Γ U = Γ ⊢Com U

  private variable
    C : Γ ⊢Com U
    D : Γ ⊢Com V

  data DepMod : Kind -> 𝒰₀ where
    global : DepMod global
    local : (U : ⟨ P ⟩) -> DepMod local

  private variable
    d : DepMod k

  data _⊢Mod_ {W} : ∀ (Γ : Ctx W) -> Kind -> 𝒰₀ where
    Dep : (d : DepMod k) -> Γ ⊢Mod k
    -- type : Γ ⊢Mod type
    -- local : (U : ⟨ P ⟩) -> Γ ⊢Mod local -- U tells us at which location this value is located
    Com : (R : ⟨ P ⟩) -> (A : Γ ⊢Global) -> Γ ⊢Mod (com R) -- A tells us the result type of the communication, R the "root"-location of the protocol

  pattern Local U = Dep (local U)
  pattern Global = Dep global


  private variable
    m : Γ ⊢Mod k
    n : Γ ⊢Mod l
    m₀ : Γ ⊢Mod k
    m₁ : Γ ⊢Mod l

  record _⊢Entry_ (Γ : Ctx W) (k : Kind) : 𝒰₀ where
    inductive ; eta-equality
    constructor _/_
    field fst : Γ ⊢Sort k
    field snd : Γ ⊢Mod k

  infixl 25 _/_

  open _⊢Entry_ public

  private variable
    E F : Γ ⊢Entry k
    E₀ E₁ : Γ ⊢Entry k
    F₀ F₁ : Γ ⊢Entry l


  data Ctx W where
    [] : Ctx W
    _,[_] : ∀ (Γ : Ctx W) -> (A : Γ ⊢Entry k) -> Ctx W

  infixl 30 _,[_]


  data _⊢Var_ {W} : ∀ (Γ : Ctx W) -> Γ ⊢Entry k -> 𝒰₀
  data _⊢_ {W} : ∀ (Γ : Ctx W) -> Γ ⊢Entry k -> 𝒰₀

  private variable
    t : Γ ⊢ E
    s : Γ ⊢ F

    t₀ : Γ ⊢ E₀
    t₁ : Γ ⊢ E₁
    s₀ : Γ ⊢ F₀
    s₁ : Γ ⊢ F₁



  --------------------------------------------------------------
  -- Context extensions

  data _⊢Ctx₊ {W : Index} : Ctx W -> 𝒰₂

  _⋆-Ctx₊_ : ∀ (Γ : Ctx W) -> Γ ⊢Ctx₊ -> Ctx W

  data _⊢Ctx₊ where
    [] : Γ ⊢Ctx₊
    _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Entry k -> Γ ⊢Ctx₊


  Γ ⋆-Ctx₊ [] = Γ
  Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]




  infixl 30 _⋆-Ctx₊_ _⋆-Ctx₊₂_ _⋆-Ctx_ [_]Ctx₊∷_


  -- End Context setup
  --------------------------------------------------------------


  wk-Sort : Γ ⊢Sort k -> Γ ,[ E ] ⊢Sort k
  su-Sort : (t : Γ ⊢ E) -> Γ ,[ E ] ⊢Sort k -> Γ ⊢Sort k

  wk-Entry : Γ ⊢Entry k -> Γ ,[ E ] ⊢Entry k
  su-Entry : (t : Γ ⊢ E) -> Γ ,[ E ] ⊢Entry k -> Γ ⊢Entry k

  wk-Term : Γ ⊢ E -> Γ ,[ F ] ⊢ wk-Entry E

  wk-Mod : Γ ⊢Mod k -> Γ ,[ E ] ⊢Mod k

  special-su-top : Γ ,[ E ] ⊢ wk-Entry F ->  Γ ,[ F ] ⊢Sort k -> Γ ,[ E ] ⊢Sort k






  data _⊢Sort_ where

    --------------------------------------------------------------
    -- Generic
    ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    ⨅ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : (A B : Γ ⊢Sort k) -> Γ ⊢Sort k

    --------------------------------------------------------------
    -- Local

    Base : BaseType -> Γ ⊢Local

    -- `Vect L n` is a vector with entries of local type `L`
    -- and of length `n`
    Vect : (L : Γ ⊢Local) -> (n : Γ ⊢ (Base NN) / Local U) -> Γ ⊢Local

    _＠_ : (L : Γ ⊢Local) -> (U : ⟨ P ⟩) -> Γ ⊢Global

    -- NOTE, only well "modalized" if W is the current global
    -- modality
    Ext : Γ ⊢ L ＠ V / Global -> (ϕ : U ≤ V) -> Γ ⊢Global


    --------------------------------------------------------------
    -- Types
    Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global

    --------------------------------------------------------------
    -- Com
    End : Γ ⊢Com U

    -- A single communication of a protocol with R participants.
    -- We are sending local data from location U₀ to be accessible
    -- at location U₁
    [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / Global ] ⊢Com R) -> Γ ⊢Com R



  -- infixr 40 _⇒_
  infixr 50 _⊗_

  -- syntax Loc U L = L ＠ U
  infixl 90 _＠_


  data _⊢Var_ where
    zero : Γ ,[ E ] ⊢Var wk-Entry E
    suc : Γ ⊢Var E -> Γ ,[ F ] ⊢Var wk-Entry E





  ------------------------------------------------------------------------
  -- Weakening


  {-# TERMINATING #-}
  wk-Ctx₊ : (Δ : Γ ⊢Ctx₊) -> Γ ,[ E ] ⊢Ctx₊


  wk-Mod,ind : ∀ Δ -> (m : Γ ⋆-Ctx₊ Δ ⊢Mod k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Mod k

  wk-Sort,ind : ∀ Δ -> (S : Γ ⋆-Ctx₊ Δ ⊢Sort k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Sort k

  wk-Entry,ind : ∀ Δ -> (E : Γ ⋆-Ctx₊ Δ ⊢Entry k) -> Γ ,[ F ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Entry k
  wk-Entry,ind Δ (S / m) = wk-Sort,ind Δ S / wk-Mod,ind Δ m

  wk-Mod,ind Δ (Dep t) = Dep t
  wk-Mod,ind Δ (Com R A) = Com R (wk-Sort,ind Δ A)


  -- wk-Var-ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Sort k} -> Γ ⋆-Ctx₊ Δ ⊢Var AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Var wk-Sort,ind Δ AX

  wk-Term,ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Entry k} -> Γ ⋆-Ctx₊ Δ ⊢ AX -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢ wk-Entry,ind Δ AX
  wk-Term,ind = {!!}


  wk-Ctx₊ [] = []
  wk-Ctx₊ (Δ ,[ E ]) = wk-Ctx₊ Δ ,[ wk-Entry,ind Δ E ]


  wk-Sort,ind Δ (Base x) = Base x
  wk-Sort,ind Δ (Vect L n) = {!!}
  wk-Sort,ind Δ (⨆ A B) = {!!}
  wk-Sort,ind Δ (⨅ S B) = ⨅ (wk-Entry,ind Δ S) (wk-Sort,ind (Δ ,[ S ]) B)
  wk-Sort,ind Δ (x ＠ U) = (wk-Sort,ind Δ x) ＠ U
  wk-Sort,ind Δ (Ext x ϕ) = Ext (wk-Term,ind Δ x) ϕ -- ϕ (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (A ⊗ B) = wk-Sort,ind Δ A ⊗ wk-Sort,ind Δ B
  wk-Sort,ind Δ (Com x x₁) = {!!}
  wk-Sort,ind Δ End = End
  wk-Sort,ind Δ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► x) = {!!}

  wk-Sort S = wk-Sort,ind [] S
  wk-Mod (m) = wk-Mod,ind [] m
  wk-Entry m = wk-Entry,ind [] m
  wk-Term t = wk-Term,ind [] t




  -- End weakening
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Substitution

  su-Ctx₊ : (Γ ⊢ E) -> Γ ,[ E ] ⊢Ctx₊ -> Γ ⊢Ctx₊
  su-Sort,ind : (t : Γ ⊢ E) -> ∀ Δ -> (S : Γ ,[ E ] ⋆-Ctx₊ Δ ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t Δ ⊢Sort k
  su-Mod,ind : (t : Γ ⊢ E) -> ∀ Δ -> (m : Γ ,[ E ] ⋆-Ctx₊ Δ ⊢Mod k) -> Γ ⋆-Ctx₊ su-Ctx₊ t Δ ⊢Mod k
  su-Entry,ind : (t : Γ ⊢ E) -> ∀ Δ -> (E : Γ ,[ E ] ⋆-Ctx₊ Δ ⊢Entry k) -> Γ ⋆-Ctx₊ su-Ctx₊ t Δ ⊢Entry k

  su-Term,ind : (t : Γ ⊢ E) -> ∀ Δ -> {S : _ ⊢Sort k} {m : _ ⊢Mod k}
                -> (s : Γ ,[ E ] ⋆-Ctx₊ Δ ⊢ S / m)
                -> Γ ⋆-Ctx₊ su-Ctx₊ t Δ ⊢ su-Sort,ind t Δ S / su-Mod,ind t Δ m


  -- su-Var-ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Sort k} -> Γ ⋆-Ctx₊ Δ ⊢Var AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ Δ ⊢Var su-Sort,ind Δ AX

  su-Mod,ind t Δ (Dep d) = Dep d
  su-Mod,ind t Δ (Com R A) = Com R (su-Sort,ind t Δ A)
  su-Entry,ind t Δ (S / m) = su-Sort,ind t Δ S / su-Mod,ind t Δ m

  su-Ctx₊ t [] = []
  su-Ctx₊ t (Δ ,[ E ]) = su-Ctx₊ t Δ ,[ su-Entry,ind t _ E ]

  su-Sort,ind t Δ (Base x) = Base x
  su-Sort,ind t Δ (Vect L n) = Vect (su-Sort,ind t Δ L) (su-Term,ind t Δ n)
  su-Sort,ind t Δ (⨆ E S) = {!!}
  su-Sort,ind t Δ (⨅ E S) = {!!}
  su-Sort,ind t Δ (S ⊗ S₁) = {!!}
  su-Sort,ind t Δ (L ＠ U) = su-Sort,ind t Δ L ＠ U
  su-Sort,ind t Δ (Ext x ϕ) = {!!}
  su-Sort,ind t Δ (Com x x₁) = {!!}
  su-Sort,ind t Δ End = {!!}
  su-Sort,ind t Δ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) = {!!}


  su-Sort t T = su-Sort,ind t [] T
  special-su-top t T = su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)

  -- End Substitution
  ------------------------------------------------------------------------


  data _⊢_ {W} where

    ---------------------------------------------
    -- Terms
    var : Γ ⊢Var E -> Γ ⊢ E

    b0 : Γ ⊢ Base BB / Local U
    b1 : Γ ⊢ Base BB / Local U
    n0 : Γ ⊢ Base NN / Local U

    -- We only have to implement this term if our current location `U`
    -- Is part of the implemented locations `W`
    loc : (U ≤ W -> (Γ ⊢ L / Local U)) -> Γ ⊢ (L ＠ U) / Global


    -- Given a value of type L at location U, we can make it into a local
    -- value of type L at location V, as long as V is a location which can access U
    -- (ie, is a superset).
    [_]unloc : (ϕ : U ≤ V) -> Γ ⊢ (L ＠ U) / Global -> Γ ⊢ L / Local V




    fromext : {ϕ : V ≤ U} -> {val : Γ ⊢ L ＠ U / Global} -> Γ ⊢ Ext val ϕ / Global -> Γ ⊢ L ＠ V / Global


    lam : Γ ,[ E ] ⊢ S / (Dep d)  -> Γ ⊢ ⨅ E S / (Dep d)
    app : Γ ⊢ ⨅ (T / (Dep d)) S / n -> (t : Γ ⊢ T / (Dep d)) -> Γ ⊢ su-Sort t S / n


    π₁ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ T / m
    π₂ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ S / m
    _,_ : Γ ⊢ T / m -> Γ ⊢ S / m -> Γ ⊢ (T ⊗ S) / m


    -------------------
    -- protocols
    _∋_ : (P : Γ ⊢Com R) -> Γ ⊢ P / Com R A -> Γ ⊢ Com R A / Global

    _►_ : {ϕ : R ≤ U₁} -> {ψ : U₁ ≤ U₀}
        -> ∀ {C}
        -> (val : Γ ⊢ L ＠ U₀ / Global)
        -> Γ ,[ Ext val ψ / Global ] ⊢ special-su-top (fromext (var zero) ) C / Com R (wk-Sort A)
        -> Γ ⊢ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) / Com R A

    ret : Γ ⊢ A / Global -> Γ ⊢ End / Com R A



  ------------------------------------------------------------------------
  -- Substitution for terms

  su-Term,ind t Δ (var x) = {!!}
  su-Term,ind t Δ b0 = {!!}
  su-Term,ind t Δ b1 = {!!}
  su-Term,ind t Δ n0 = {!!}
  su-Term,ind t Δ (loc s) = loc λ ϕ -> su-Term,ind t Δ (s ϕ)
  su-Term,ind t Δ ([ ϕ ]unloc s) = {!!}
  su-Term,ind t Δ (fromext s) = {!!}
  su-Term,ind t Δ (lam s) = {!!}
  su-Term,ind t Δ (app s s₁) = {!!}
  su-Term,ind t Δ (π₁ s) = {!!}
  su-Term,ind t Δ (π₂ s) = {!!}
  su-Term,ind t Δ (s , s₁) = {!!}
  su-Term,ind t Δ (P ∋ s) = {!!}
  su-Term,ind t Δ (s ► s₁) = {!!}
  su-Term,ind t Δ (ret s) = {!!}

  -- End Substitution for terms
  ------------------------------------------------------------------------




  data _⊢WFMod_ {W : Index} : ∀ (Γ : Ctx W) -> Γ ⊢Mod k -> 𝒰₀
  data _⊢WFSort_ {W : Index} : ∀ (Γ : Ctx W) -> Γ ⊢Entry k -> 𝒰₀

  record _⊢WFEntry_ {W : ⟨ P ⟩} (Γ : Ctx W) (E : Γ ⊢Entry k) : 𝒰₀ where
    inductive ; eta-equality
    constructor _/_
    field fst : Γ ⊢WFSort E
    field snd : Γ ⊢WFMod (snd E)

  data _⊢WFSort_ where
    -- tt : Γ ⊢WFSort S / m

    --------------------------------------------------------------
    -- Generic
    -- ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k

    ⨅ : Γ ⊢WFEntry E -> Γ ,[ E ] ⊢WFSort T / (Dep d) -> Γ ⊢WFSort (⨅ E T) / (Dep d)

    -- (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : Γ ⊢WFSort S / m -> Γ ⊢WFSort T / m -> Γ ⊢WFSort (S ⊗ T) / m

    --------------------------------------------------------------
    -- Local

    Base : ∀{B} -> Γ ⊢WFSort (Base B) / m

    Loc : Γ ⊢WFSort L / Local U -> Γ ⊢WFSort (L ＠ U) / Global


    -- NOTE, only well "modalized" if W is the current global
    -- modality
    -- Ext : Γ ⊢ Loc V L / Global -> (ϕ : U ≤ V) -> Γ ⊢Global


    -- --------------------------------------------------------------
    -- -- Types
    -- Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global

    -- --------------------------------------------------------------
    -- -- Com
    -- End : Γ ⊢Com U

    -- -- A single communication of a protocol with R participants.
    -- -- We are sending local data from location U₀ to be accessible
    -- -- at location U₁
    -- [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / Global ] ⊢Com R) -> Γ ⊢Com R



  data _⊢WFMod_ where
    -- type : Γ ⊢WFMod global
    -- local : Γ ⊢WFMod local U
    Dep : ∀ (d : DepMod k) -> Γ ⊢WFMod (Dep d)
    Com : Γ ⊢WFSort (A / Global) -> Γ ⊢WFMod Com R A


  data _⊢WFCtx {W : Index} : ∀ (Γ : Ctx W) -> 𝒰₀ where
    [] : [] ⊢WFCtx
    _,[_] : Γ ⊢WFCtx -> Γ ⊢WFEntry E -> Γ ,[ E ] ⊢WFCtx



  ----------------------------------------------------------
  -- Meta theorems

  data _[_]⤇_ {W₀} {W₁} : (Γ₀ : Ctx W₀) -> (ϕ : W₁ ≤ W₀) -> (Γ₁ : Ctx W₁) -> 𝒰₀

  private variable
    γ : Γ₀ [ ϕ ]⤇ Γ₁

  data _⊢Sort_⤇_ {W₀} {W₁} : {Γ₀ : Ctx W₀} -> {ϕ : W₁ ≤ W₀} -> {Γ₁ : Ctx W₁}
                         -> Γ₀ [ ϕ ]⤇ Γ₁
                         -> Γ₀ ⊢Sort k
                         -> Γ₁ ⊢Sort k
                         -> 𝒰₀

  private variable
    σ : γ ⊢Sort S₀ ⤇ S₁
    τ : γ ⊢Sort T₀ ⤇ T₁

  data _⊢Mod_⤇_ {W₀} {W₁} : {Γ₀ : Ctx W₀} -> {ϕ : W₁ ≤ W₀} -> {Γ₁ : Ctx W₁}
                         -> Γ₀ [ ϕ ]⤇ Γ₁
                         -> Γ₀ ⊢Mod k
                         -> Γ₁ ⊢Mod k
                         -> 𝒰₀

  record _⊢Entry_⤇_ {W₀} {W₁} {Γ₀ : Ctx W₀} {ϕ : W₁ ≤ W₀} {Γ₁ : Ctx W₁}
                         (γ : Γ₀ [ ϕ ]⤇ Γ₁)
                         (E₀ : Γ₀ ⊢Entry k)
                         (E₁ : Γ₁ ⊢Entry k) : 𝒰₀ where
    inductive ; eta-equality
    constructor _/_
    field fst : γ ⊢Sort fst E₀ ⤇ fst E₁
    field snd : γ ⊢Mod snd E₀ ⤇ snd E₁

  open _⊢Entry_⤇_

  private variable
    η : γ ⊢Entry E₀ ⤇ E₁

  data _⊢_⤇_∶_ {W₀} {W₁} : {Γ₀ : Ctx W₀} -> {ϕ : W₁ ≤ W₀} -> {Γ₁ : Ctx W₁}
                         -> (γ : Γ₀ [ ϕ ]⤇ Γ₁)
                         -> {E₀ : Γ₀ ⊢Entry k}
                         -> {E₁ : Γ₁ ⊢Entry k}
                         -> Γ₀ ⊢ E₀
                         -> Γ₁ ⊢ E₁
                         -> γ ⊢Entry E₀ ⤇ E₁
                         -> 𝒰₀

  data _[_]⤇_ {W₀} {W₁} where
    [] : [] [ ϕ ]⤇ []
    _,[_] : (Γ : Γ₀ [ ϕ ]⤇ Γ₁) -> Γ ⊢Entry E₀ ⤇ E₁
              -> (Γ₀ ,[ E₀ ]) [ ϕ ]⤇ (Γ₁ ,[ E₁ ])

  data _⊢Mod_⤇_ {W₀} {W₁} where
    Dep : ∀ (d : DepMod k) -> γ ⊢Mod Dep d ⤇ Dep d
    Com : γ ⊢Sort T₀ ⤇ T₁ -> γ ⊢Mod Com R T₀ ⤇ Com R T₁

  data _⊢Sort_⤇_ {W₀} {W₁} where
    Base : ∀(B : BaseType) -> γ ⊢Sort Base B ⤇ Base B
    _⊗_ : γ ⊢Sort S₀ ⤇ S₁ -> γ ⊢Sort T₀ ⤇ T₁
        -> γ ⊢Sort (S₀ ⊗ T₀) ⤇ (S₁ ⊗ T₁)

    ⨅ : (η : γ ⊢Entry E₀ ⤇ E₁) -> (γ ,[ η ] ⊢Sort S₀ ⤇ S₁) -> γ ⊢Sort ⨅ E₀ S₀ ⤇ ⨅ E₁ S₁

    _＠_ : γ ⊢Sort S₀ ⤇ S₁ -> (U : ⟨ P ⟩) -> γ ⊢Sort S₀ ＠ U ⤇ S₁ ＠ U

    Vect : γ ⊢Sort S₀ ⤇ S₁
         -> γ ⊢ t₀ ⤇ t₁ ∶ Base NN / Dep (local U)
         -> γ ⊢Sort Vect S₀ t₀ ⤇ Vect S₁ t₁

    -- ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    -- Ext : Γ ⊢ L ＠ V / Global -> (ϕ : U ≤ V) -> Γ ⊢Global
    -- Com : ⟨ P ⟩ -> Γ ⊢Global -> Γ ⊢Global
    -- End : Γ ⊢Com U
    -- [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / Global ] ⊢Com R) -> Γ ⊢Com R

  data _⊢_⤇_∶_ {W₀} {W₁} where
    b0 : γ ⊢ b0 ⤇ b0 ∶ Base BB / Dep (local U)
    b1 : γ ⊢ b1 ⤇ b1 ∶ Base BB / Dep (local U)
    n0 : γ ⊢ n0 ⤇ n0 ∶ Base NN / Dep (local U)

    loc : {γ : Γ₀ [ ϕ ]⤇ Γ₁}
         -> (σ : γ ⊢Sort S₀ ⤇ S₁)
         -> (t₀ : U ≤ W₀ -> (Γ₀ ⊢ S₀ / Local U))
         -> (t₁ : U ≤ W₁ -> (Γ₁ ⊢ S₁ / Local U))
         -> ∀{ψ : U ≤ W₁} -> γ ⊢ t₀ (ψ ⟡ ϕ) ⤇ t₁ ψ ∶ (σ / Dep (local U))
         -> γ ⊢ loc t₀ ⤇ loc t₁ ∶ σ ＠ U / Dep global

    -- lam : γ ,[ η ] ⊢ t₀ ⤇ t₁ ∶ σ₀
    -- Γ ,[ E ] ⊢ S / (Dep d)  -> Γ ⊢ ⨅ E S / (Dep d)
    -- app : Γ ⊢ ⨅ (T / (Dep d)) S / n -> (t : Γ ⊢ T / (Dep d)) -> Γ ⊢ su-Sort t S / n

    -- var : Γ ⊢Var E -> Γ ⊢ E
    -- [_]unloc : (ϕ : U ≤ V) -> Γ ⊢ (L ＠ U) / Global -> Γ ⊢ L / Local V
    -- fromext : {ϕ : V ≤ U} -> {val : Γ ⊢ L ＠ U / Global} -> Γ ⊢ Ext val ϕ / Global -> Γ ⊢ L ＠ V / Global
    -- π₁ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ T / m
    -- π₂ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ S / m
    -- _,_ : Γ ⊢ T / m -> Γ ⊢ S / m -> Γ ⊢ (T ⊗ S) / m
    -- _∋_ : (P : Γ ⊢Com R) -> Γ ⊢ P / Com R A -> Γ ⊢ Com R A / Global
    -- _►_ : {ϕ : R ≤ U₁} -> {ψ : U₁ ≤ U₀}
    --     -> ∀ {C}
    --     -> (val : Γ ⊢ L ＠ U₀ / Global)
    --     -> Γ ,[ Ext val ψ / Global ] ⊢ special-su-top (fromext (var zero) ) C / Com R (wk-Sort A)
    --     -> Γ ⊢ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) / Com R A

    -- ret : Γ ⊢ A / Global -> Γ ⊢ End / Com R A


{-
  restrict-Ctx : W₀ ≤ W₁ -> ∀ (Γ : Ctx W₁) -> Ctx W₀
  restrict-Ctx₊ : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> Γ ⊢Ctx₊ -> restrict-Ctx ϕ Γ ⊢Ctx₊
  restrict-Sort : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> (S : Γ ⊢Sort k) -> restrict-Ctx ϕ Γ ⊢Sort k
  restrict-Mod : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> (m : Γ ⊢Mod k) -> restrict-Ctx ϕ Γ ⊢Mod k
  restrict-Term : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> ∀{S : Γ ⊢Sort k} {m : Γ ⊢Mod k}
                  -> Γ ⊢ S / m
                  -> restrict-Ctx ϕ Γ ⊢ restrict-Sort ϕ S / restrict-Mod ϕ m

  restrict-Ctx ϕ [] = []
  restrict-Ctx ϕ (Γ ,[ A / m ]) = restrict-Ctx ϕ Γ ,[ restrict-Sort ϕ A / restrict-Mod ϕ m  ]

  restrict-Ctx₊ ϕ [] = []
  restrict-Ctx₊ ϕ (Δ ,[ x ]) = restrict-Ctx₊ ϕ Δ ,[ {!!} ]

  β-restrict,⋆ : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> {Δ : Γ ⊢Ctx₊} -> restrict-Ctx ϕ (Γ ⋆-Ctx₊ Δ) ≡ restrict-Ctx ϕ Γ ⋆-Ctx₊ restrict-Ctx₊ ϕ Δ
  β-restrict,⋆ = {!!}

  {-# REWRITE β-restrict,⋆ #-}

  β-restrict,Ctx₊ : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> ∀{E : Γ ⊢Entry k} {Δ}
                  -> (t : Γ ⊢ E)
                  -> su-Ctx₊ (restrict-Term ϕ t) (restrict-Ctx₊ ϕ Δ) ≡ restrict-Ctx₊ ϕ (su-Ctx₊ t Δ)
  β-restrict,Ctx₊ = {!!}

  {-# REWRITE β-restrict,Ctx₊ #-}


  β-restrict,su : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> ∀{E : Γ ⊢Entry k} {Δ} -> (S : Γ ,[ E ] ⋆-Ctx₊ Δ ⊢Sort k)
                  -> (t : Γ ⊢ E)
                  -> restrict-Sort ϕ (su-Sort,ind t Δ S) ≡ su-Sort,ind (restrict-Term ϕ t) (restrict-Ctx₊ ϕ Δ) (restrict-Sort ϕ S)
  β-restrict,su = {!!}

  restrict-Mod ϕ (Dep d) = Dep d
  restrict-Mod ϕ (Com R A) = Com R (restrict-Sort ϕ A)



  restrict-Sort ϕ (⨆ E S) = {!!}
  restrict-Sort ϕ (⨅ (S / m) T) = ⨅ (restrict-Sort ϕ S / restrict-Mod ϕ m) (restrict-Sort ϕ T)
  restrict-Sort ϕ (S ⊗ S₁) = {!!}
  restrict-Sort ϕ (Base x) = {!!}
  restrict-Sort ϕ (Vect L n) = {!!}
  restrict-Sort ϕ (L ＠ U) = restrict-Sort ϕ L ＠ U
  restrict-Sort ϕ (Ext x ϕ₁) = {!!}
  restrict-Sort ϕ (Com x x₁) = {!!}
  restrict-Sort ϕ End = {!!}
  restrict-Sort ϕ ([ L from U₀ to U₁ [ ϕ₁ ⨾ ψ ]on W ]► C) = {!!}


  restrict-Term ϕ (var x) = {!!}
  restrict-Term ϕ b0 = {!!}
  restrict-Term ϕ b1 = {!!}
  restrict-Term ϕ n0 = {!!}
  restrict-Term ϕ (loc x) = loc λ ψ -> restrict-Term ϕ (x (ψ ⟡ ϕ))
  restrict-Term ϕ ([ ϕ₁ ]unloc t) = {!!}
  restrict-Term ϕ (fromext t) = {!!}
  restrict-Term ϕ (lam t) = lam (restrict-Term ϕ t)
  restrict-Term ϕ (app t s) = let x = app (restrict-Term ϕ t) (restrict-Term ϕ s) in {!!}
  restrict-Term ϕ (π₁ t) = {!!}
  restrict-Term ϕ (π₂ t) = {!!}
  restrict-Term ϕ (t , t₁) = {!!}
  restrict-Term ϕ (P ∋ t) = {!!}
  restrict-Term ϕ (t ► t₁) = {!!}
  restrict-Term ϕ (ret t) = {!!}



-}






module Examples where

  PP : Space
  PP = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))

  uu vv : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  vv = ⦗ # 1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  all = uu ∨ vv

  ε : Ctx {PP} all
  ε = []

  T0 : ∀{Γ : Ctx {PP} all} -> Γ ⊢Global
  T0 = (Base NN ＠ uu) ⊗ (Base NN ＠ vv)

  t1 : ε ⊢ ⨅ (T0 / Global) (Base NN ＠ uu) / Global
  t1 = lam (π₁ (var zero))

  -- t2 : all ∣ ε ⊢ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / Global) → ((Base NN ⊗ Base NN) ＠ uu) / Global

  t2 : ε ⊢ ⨅ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / Global) ((Base NN ⊗ Base NN) ＠ uu) / Global
  t2 = {!!}
  -- t2 = lam (loc ((let x = π₂ (var zero) in [ {!!} ]unloc x) , {!!}))
  -- lam (loc ([ reflexive ]unloc (π₁ (var zero)) , [ reflexive ]unloc (π₁ (var zero))))

  f : (uu ∧ vv) ≤ vv
  f = π₁-∧

  t3 : ε ⊢ ⨅ (Base NN ＠ uu / Global) (Com (uu ∧ vv) (Base NN ＠ vv)) / Global
  t3 = {!!} -- lam (([ Base NN from uu to (uu ∧ vv) [ reflexive ⨾ π₀-∧ ]on all ]► End) ∋ (var zero ► ret (loc λ _ -> [ f ]unloc (fromext (var zero)))))
    
  +ₙ : ∀ {U} -> ε ⊢ ⨅ (Base NN / Local U) (⨅ (Base NN / Local U) (Base NN)) / Local U




{-
  restrict-Ctx : W₀ ≤ W₁ -> ∀ (Γ : Ctx W₁) -> Γ ⊢WFCtx -> Ctx W₀
  restrict-Sort : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> (ΓP : Γ ⊢WFCtx) -> (S : Γ ⊢Sort k) -> (m : Γ ⊢Mod k) -> Γ ⊢WFSort (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Sort k
  restrict-Mod : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> (ΓP : Γ ⊢WFCtx ) -> (m : Γ ⊢Mod k) -> Γ ⊢WFMod m -> restrict-Ctx ϕ Γ ΓP ⊢Mod k

  -- restrict-Entry : (ϕ : W₀ ≤ W₁) -> (ΓP : W₁ ∣ Γ ⊢WFCtx) -> W₁ ∣ Γ ⊢WFEntry (S / m) -> restrict-Ctx ϕ Γ ΓP ⊢Entry k
  -- restrict-Entry = {!!}

  restrict-Mod ϕ ΓP (Dep d) (Dep d) = Dep d
  restrict-Mod ϕ ΓP (Com R A) (Com Ap) = Com R (restrict-Sort ϕ ΓP A Global Ap)


  restrict-Ctx ϕ [] P = []
  restrict-Ctx ϕ (Γ ,[ S / m ]) (ΓP ,[ SP / mP ]) = restrict-Ctx ϕ Γ ΓP ,[ restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP  ]


  restrict-Sort ϕ ΓP (⨆ E S) m P = {!!}
  restrict-Sort ϕ ΓP (⨅ (S / m) T) (Dep d') (⨅ (SP / mP) TP) = ⨅ (restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP) (restrict-Sort ϕ (ΓP ,[ SP / mP ]) T (Dep d') TP)
  restrict-Sort ϕ ΓP (S ⊗ T) m (SP ⊗ TP) = restrict-Sort ϕ ΓP S m SP ⊗ restrict-Sort ϕ ΓP T m TP
  restrict-Sort ϕ ΓP (Base x) m Base = Base x
  restrict-Sort ϕ ΓP (L ＠ U) m (Loc P) = restrict-Sort ϕ ΓP L (Local U) P ＠ U
  restrict-Sort ϕ ΓP (Ext x ϕ₁) m P = {!!}
  restrict-Sort ϕ ΓP (Com x x₁) m P = {!!}
  restrict-Sort ϕ ΓP End m P = {!!}
  restrict-Sort ϕ ΓP ([ L from U₀ to U₁ [ ϕ₁ ⨾ ψ ]on W ]► C) m P = {!!}


  restrict-Term : (ϕ : W₀ ≤ W₁) -> {Γ : Ctx W₁} -> ∀{S : Γ ⊢Sort k} {m : Γ ⊢Mod k} -> (ΓP : Γ ⊢WFCtx) -> (SP : Γ ⊢WFSort (S / m)) -> (mP : Γ ⊢WFMod m)
                  -> Γ ⊢ S / m
                  -> restrict-Ctx ϕ Γ ΓP ⊢ restrict-Sort ϕ ΓP S m SP / restrict-Mod ϕ ΓP m mP
  restrict-Term ϕ ΓP SP mP (var x) = {!!}
  restrict-Term ϕ ΓP SP mP b0 = {!!}
  restrict-Term ϕ ΓP SP mP b1 = {!!}
  restrict-Term ϕ ΓP SP mP n0 = {!!}
  restrict-Term ϕ ΓP (Loc {U = U} SP) (Dep .global) (loc t) = loc λ ψ -> (restrict-Term ϕ ΓP SP (Dep (local U)) (t (ψ ⟡ ϕ)))
  restrict-Term ϕ ΓP SP mP ([ ϕ₁ ]unloc t) = {!!}
  restrict-Term ϕ ΓP SP mP (fromext t) = {!!}
  restrict-Term ϕ ΓP (⨅ TP SP) (Dep d) (lam t) = lam (restrict-Term ϕ (ΓP ,[ TP ]) SP (Dep d) t )
  restrict-Term ϕ ΓP SP (Dep d) (app t s) = let x = app (restrict-Term ϕ ΓP (⨅ {!!} {!!}) (Dep d) t) (restrict-Term ϕ (ΓP) {!!} (Dep {!!}) s) in {!!}
  restrict-Term ϕ ΓP SP mP (π₁ t) = {!!}
  restrict-Term ϕ ΓP SP mP (π₂ t) = {!!}
  restrict-Term ϕ ΓP SP mP (t , t₁) = {!!}
-}


