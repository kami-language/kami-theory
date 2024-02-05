
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiD.Dev.2024-01-20.Rules-OneSpace where

open import Agora.Conventions hiding (Σ ; Lift ; k ; m ; n)
open import Agora.Order.Preorder
open import Agora.Order.Lattice
open import Agora.Data.Power.Definition
open import Agora.Data.Sum.Definition
open import Agora.Data.Product.Definition
open import Data.Fin hiding (_-_ ; _+_ ; _≤_)
open import Data.Nat hiding (_! ; _+_ ; _≤_ ; _≰_ ; _/_)
open import Relation.Nullary.Decidable.Core

open import KamiD.Dev.2024-01-20.Core hiding (_＠_)
open import KamiD.Dev.2024-01-20.UniqueSortedList hiding (img)
open import KamiD.Dev.2024-01-20.Space
open import KamiD.Dev.2024-01-20.Sheaf
open import KamiD.Dev.2024-01-20.Open
open import KamiD.Dev.2024-01-20.StrictOrder.Base

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

  private variable
    U V W : ⟨ P ⟩
    U₀ U₁ : ⟨ P ⟩
    W₀ W₁ : ⟨ P ⟩
    R : ⟨ P ⟩

  data Ctx : 𝒰₀

  private variable
    Γ : Ctx

  -- setup of kinds for types and spaces
  data Kind : 𝒰₀ where
    type : Kind
    local : Kind
    com : ⟨ P ⟩ -> Kind

  private variable
    k l : Kind


  data _⊢Sort_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀

  private variable
    S : Γ ⊢Sort k
    T : Γ ⊢Sort l



  TypeSyntax : ∀ (Γ : Ctx) -> 𝒰 _
  TypeSyntax Γ = Γ ⊢Sort type

  syntax TypeSyntax Γ = Γ ⊢Type

  private variable
    A : Γ ⊢Type
    B : Γ ⊢Type

  LocalSyntax : ∀ (Γ : Ctx) -> 𝒰 _
  LocalSyntax Γ = Γ ⊢Sort local

  syntax LocalSyntax Γ = Γ ⊢Local

  private variable
    L : Γ ⊢Local
    M : Γ ⊢Local
    N : Γ ⊢Local

  ComSyntax : ∀ (Γ : Ctx) -> ⟨ P ⟩ -> 𝒰 _
  ComSyntax Γ U = Γ ⊢Sort com U

  syntax ComSyntax Γ U = Γ ⊢Com U

  private variable
    C : Γ ⊢Com U
    D : Γ ⊢Com V


  data _⊢ModBase_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀ where
    -- type : (W : ⟨ P ⟩) -> Γ ⊢Mod type -- W tells us for which locations this type is implemented
    -- local : (U W : ⟨ P ⟩) -> Γ ⊢Mod local -- W as above, U tells us at which location this value is located
    -- com : (R : ⟨ P ⟩) -> (A : Γ ⊢Type) -> (W : ⟨ P ⟩) -> Γ ⊢Mod (com R) -- W as above, A tells us the result type of the communication, R the "root"-location of the protocol

    type : Γ ⊢ModBase type -- W tells us for which locations this type is implemented
    local : (U : ⟨ P ⟩) -> Γ ⊢ModBase local -- W as above, U tells us at which location this value is located
    com : (R : ⟨ P ⟩) -> (A : Γ ⊢Type) -> Γ ⊢ModBase (com R) -- W as above, A tells us the result type of the communication, R the "root"-location of the protocol

  _⊢Mod_ : ∀ (Γ : Ctx) -> Kind -> 𝒰₀
  _⊢Mod_ Γ k = Γ ⊢ModBase k ×-𝒰 ⟨ P ⟩

    -- type : (W : ⟨ P ⟩) -> Γ ⊢Mod type -- W tells us for which locations this type is implemented
    -- local : (U W : ⟨ P ⟩) -> Γ ⊢Mod local -- W as above, U tells us at which location this value is located
    -- com : (R : ⟨ P ⟩) -> (A : Γ ⊢Type) -> (W : ⟨ P ⟩) -> Γ ⊢Mod (com R) -- W as above, A tells us the result type of the communication, R the "root"-location of the protocol


  private variable
    m : Γ ⊢Mod k
    n : Γ ⊢Mod l

    b : Γ ⊢ModBase k
    c : Γ ⊢ModBase l

  record _⊢Entry_ (Γ : Ctx) (k : Kind) : 𝒰₀ where
    inductive ; eta-equality
    constructor _/_
    field fst : Γ ⊢Sort k
    field snd : Γ ⊢Mod k

  infixl 25 _/_

  open _⊢Entry_ public

  private variable
    E F : Γ ⊢Entry k


  data Ctx where
    [] : Ctx
    _,[_] : ∀ (Γ : Ctx) -> (A : Γ ⊢Entry k) -> Ctx

  infixl 30 _,[_]


  data _⊢Var_ : ∀ Γ -> Γ ⊢Entry k -> 𝒰₀
  data _⊢_ : ∀ Γ -> Γ ⊢Entry k -> 𝒰₀

  private variable
    t : Γ ⊢ E
    s : Γ ⊢ F



  --------------------------------------------------------------
  -- Context setup

  data _⊢Ctx₊ : Ctx -> 𝒰₂

  _⋆-Ctx₊_ : ∀ (Γ : Ctx) -> Γ ⊢Ctx₊ -> Ctx

  data _⊢Ctx₊ where
    [] : Γ ⊢Ctx₊
    _,[_] : (E : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ E) ⊢Entry k -> Γ ⊢Ctx₊

  -- _⋆-Ctx₊₂_ : (Δ : Γ ⊢Ctx₊) -> (Γ ⋆-Ctx₊ Δ) ⊢Ctx₊ -> Γ ⊢Ctx₊

  -- assoc-⋆-Ctx₊ : ∀{Δ E} -> Γ ⋆-Ctx₊ (Δ ⋆-Ctx₊₂ E) ≣ Γ ⋆-Ctx₊ Δ ⋆-Ctx₊ E

  -- Δ ⋆-Ctx₊₂ [] = Δ
  -- Δ ⋆-Ctx₊₂ (E ,[ x ]) = (Δ ⋆-Ctx₊₂ E) ,[ transp-≣ (cong-≣ _⇂_⊢Type (sym-≣ assoc-⋆-Ctx₊)) x ]

  Γ ⋆-Ctx₊ [] = Γ
  Γ ⋆-Ctx₊ (E ,[ x ]) = (Γ ⋆-Ctx₊ E) ,[ x ]

  -- instance
  --   hasNotation-⋆:Ctx₊ : hasNotation-⋆ (Ctx) (_⊢Ctx₊) (λ _ _ -> Ctx)
  --   hasNotation-⋆:Ctx₊ = record { _⋆_ = λ Γ E -> Γ ⋆-Ctx₊ E }


  {-

  assoc-⋆-Ctx₊ {E = []} = refl-≣
  assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E ,[ x ]} =
    let p = sym-≣ (assoc-⋆-Ctx₊ {Γ = Γ} {Δ = Δ} {E = E})
    in J1 p _⊢Type _,[_] x

  {-# REWRITE assoc-⋆-Ctx₊ #-}
  -}



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
  special-su-top t T = {!!} -- su-Sort t (wk-Sort,ind ([] ,[ _ ]) T)





  data _⊢Sort_ where

    --------------------------------------------------------------
    -- Generic
    ⨆ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    ⨅ : (E : Γ ⊢Entry k) -> (Y : Γ ,[ E ] ⊢Sort k) -> Γ ⊢Sort k
    _⊗_ : (A B : Γ ⊢Sort k) -> Γ ⊢Sort k

    --------------------------------------------------------------
    -- Local

    Base : BaseType -> Γ ⊢Local

    Loc : (U : ⟨ P ⟩) -> Γ ⊢Local -> Γ ⊢Type

    -- NOTE, only well "modalized" if W is the current global
    -- modality
    Ext : Γ ⊢ Loc V L / type , W -> (ϕ : U ≤ V) -> Γ ⊢Type


    --------------------------------------------------------------
    -- Types
    Com : ⟨ P ⟩ -> Γ ⊢Type -> Γ ⊢Type

    --------------------------------------------------------------
    -- Com
    End : Γ ⊢Com U

    -- A single communication of a protocol with R participants.
    -- We are sending local data from location U₀ to be accessible
    -- at location U₁
    [_from_to_[_⨾_]on_]►_ : (L : Γ ⊢Local) -> ∀ U₀ U₁ -> (ϕ : R ≤ U₁) -> (ψ : U₁ ≤ U₀) -> ∀ W -> (C : Γ ,[ L ＠ U₁ / type , W ] ⊢Com R) -> Γ ⊢Com R



  -- infixr 40 _⇒_
  infixr 50 _⊗_

  syntax Loc U L = L ＠ U
  infixl 90 Loc


  data _⊢Var_ where
    zero : Γ ,[ E ] ⊢Var wk-Entry E
    suc : Γ ⊢Var E -> Γ ,[ F ] ⊢Var wk-Entry E





  ------------------------------------------------------------------------
  -- Weakening


  {-# TERMINATING #-}
  wk-Ctx₊ : (Δ : Γ ⊢Ctx₊) -> Γ ,[ E ] ⊢Ctx₊


  wk-ModBase,ind : ∀ Δ -> (m : Γ ⋆-Ctx₊ Δ ⊢ModBase k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢ModBase k

  wk-Sort,ind : ∀ Δ -> (S : Γ ⋆-Ctx₊ Δ ⊢Sort k) -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Sort k

  wk-Entry,ind : ∀ Δ -> (E : Γ ⋆-Ctx₊ Δ ⊢Entry k) -> Γ ,[ F ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Entry k
  wk-Entry,ind Δ (S / m , W) = wk-Sort,ind Δ S / wk-ModBase,ind Δ m , W

  wk-ModBase,ind Δ (type) = type
  wk-ModBase,ind Δ (local U) = local U
  wk-ModBase,ind Δ (com R A) = com R (wk-Sort,ind Δ A)


  wk-Term,ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Entry k} -> Γ ⋆-Ctx₊ Δ ⊢ AX -> Γ ,[ E ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢ wk-Entry,ind Δ AX

 --  wk-Term,ind [] t

  -- wk-Var-ind : ∀ Δ -> {AX : Γ ⋆-Ctx₊ Δ ⊢Sort k} -> Γ ⋆-Ctx₊ Δ ⊢Var AX -> Γ ,[ S ] ⋆-Ctx₊ wk-Ctx₊ Δ ⊢Var wk-Sort,ind Δ AX

  wk-Ctx₊ [] = []
  wk-Ctx₊ (Δ ,[ E ]) = wk-Ctx₊ Δ ,[ wk-Entry,ind Δ E ]


  wk-Sort,ind Δ (Base x) = Base x
  wk-Sort,ind Δ (⨆ A B) = {!!}
  wk-Sort,ind Δ (⨅ S B) = ⨅ (wk-Entry,ind Δ S) (wk-Sort,ind (Δ ,[ S ]) B)
  wk-Sort,ind Δ (Loc U x) = Loc U (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (Ext x ϕ) = Ext (wk-Term,ind Δ x) ϕ -- ϕ (wk-Sort,ind Δ x)
  wk-Sort,ind Δ (A ⊗ B) = wk-Sort,ind Δ A ⊗ wk-Sort,ind Δ B
  wk-Sort,ind Δ (Com x x₁) = {!!}
  wk-Sort,ind Δ End = End
  wk-Sort,ind Δ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► x) = {!!}

  wk-Sort S = wk-Sort,ind [] S
  wk-Mod (m , W) = wk-ModBase,ind [] m , W
  wk-Entry m = wk-Entry,ind [] m
  wk-Term t = wk-Term,ind [] t


  -- wk-Comm,ind : ∀ E -> (Z : Γ ⋆-Ctx₊ E ⊢Comm ) -> Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E ⊢Comm 
  -- wk-Comm,ind E (⟮ U ↝ V ⨾ ϕ ⟯[ A ] Z) = ⟮ U ↝ V ⨾ ϕ ⟯[ wk-Sort,ind E A ] wk-Comm,ind (E ,[ Fill _ _ ]) Z
  -- wk-Comm,ind E End = End
  -- wk-Comm,ind E (El-Comm x) = El-Comm (wk-Term-ind E x)

  -- wk-Sort : Γ ⊢Sort k -> Γ ,[ A ] ⊢Sort k
  -- wk-Sort AX = wk-Sort,ind [] AX -- [ wk-⇛♮ id-⇛♮ ]-Type

  -- wk-≤-Local,ind E (Base b {ϕ = ϕ}) = Base b {ϕ = ϕ}
  -- wk-≤-Local,ind E (Fam ϕ m n) = Fam ϕ (wk-Term-ind E m) (wk-Term-ind E n)


  -- wk-Term : {AX : Γ ⊢Sort k} -> Γ ⊢ AX -> Γ ,[ A ] ⊢ wk-Sort AX
  -- wk-Term t = ? -- wk-Term-ind [] t


  -- wk-⇛♮-ind : ∀{A} -> ∀ E -> (Γ ⋆-Ctx₊ E) ⇛♮ Δ -> (Γ ,[ A ] ⋆-Ctx₊ wk-Ctx₊ E) ⇛♮ Δ

  -- weakening over a whole context
  -- wks-Sort : (E : Γ ⊢Ctx₊) -> (A : Γ ⊢Sort k) -> Γ ⋆-Ctx₊ E ⊢Sort k
  -- wks-Sort [] A = A
  -- wks-Sort (E ,[ x ]) A = wk-Sort (wks-Sort E A)

  -- β-wk-Sort,ind,empty : ∀{A : Γ ⊢Sort k} -> wk-Sort,ind [] A ≣ A
  -- β-wk-Sort,ind,empty = ?



  -- End weakening
  ------------------------------------------------------------------------


  data _⊢_ where

    ---------------------------------------------
    -- Terms
    var : Γ ⊢Var E -> Γ ⊢ E

    b0 : Γ ⊢ Base BB / local U , W
    b1 : Γ ⊢ Base BB / local U , W
    n0 : Γ ⊢ Base NN / local U , W

    -- We only have to implement this term if our current location `U`
    -- Is part of the implemented locations `W`
    loc : (U ≤ W -> Γ ⊢ L / local U , W) -> Γ ⊢ (L ＠ U) / type , W

    -- Given a value of type L at location U, we can make it into a local
    -- value of type L at location V, as long as V is a location which can access U
    -- (ie, is a superset).
    [_]unloc : (ϕ : U ≤ V) -> Γ ⊢ (L ＠ U) / type , W -> Γ ⊢ L / local V , W



    fromext : {ϕ : V ≤ U} -> {val : Γ ⊢ L ＠ U / type , W} -> Γ ⊢ Ext val ϕ / type , W -> Γ ⊢ L ＠ V / type , W


    lam : Γ ,[ E ] ⊢ S / wk-Mod m  -> Γ ⊢ ⨅ E S / m
    app : Γ ⊢ ⨅ (T / m) S / m -> (t : Γ ⊢ T / m) -> Γ ⊢ su-Sort t S / m


    π₁ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ T / m
    π₂ : Γ ⊢ (T ⊗ S) / m -> Γ ⊢ S / m
    _,_ : Γ ⊢ T / m -> Γ ⊢ S / m -> Γ ⊢ (T ⊗ S) / m


    -------------------
    -- protocols
    _∋_ : (P : Γ ⊢Com R) -> Γ ⊢ P / com R A , W -> Γ ⊢ Com R A / type , W

    _►_ : {ϕ : R ≤ U₁} -> {ψ : U₁ ≤ U₀}
        -> ∀ {C}
        -> (val : Γ ⊢ L ＠ U₀ / type , W)
        -> Γ ,[ Ext val ψ / type , W ] ⊢ special-su-top (fromext (var zero) ) C / com R (wk-Sort A) , W
        -> Γ ⊢ ([ L from U₀ to U₁ [ ϕ ⨾ ψ ]on W ]► C) / com R A , W

    ret : Γ ⊢ A / type , W -> Γ ⊢ End / com R A , W







    -- elim-BB : Γ ⊢ A -> Γ ⊢ A -> Γ ⊢ Base BB ⇒ wk-Sort A

    -- lam : (t : Γ ,[ A over One ] ⊢ B) -> Γ ⊢ A ⇒ B
    -- app : (f : Γ ⊢ A ⇒ B) -> (t : Γ ⊢ A) -> Γ ⊢ su-Sort t B

    -- forget : List ((List (Γ ⊢Atom X) :& isUniqueSorted)) :& (IB.isIndependentBase λ a b -> a ≰ b ×-𝒰 b ≰ a) -> Γ ⊢ Forget X




{-


  ------------------------------------------------------------------------
  -- Substitution

  su-Ctx₊ : (Γ ⊢ T) -> Γ ,[ T ] ⊢Ctx₊ -> Γ ⊢Ctx₊

  su-Sort,ind : (t : Γ ⊢ T) -> ∀ E -> (S : Γ ,[ T ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
  -- su-≤-Local,ind : {Γ : Ctx}{A : Γ ⊢Sort k} -> ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Local U} {BY : Γ ⋆-Ctx₊ E ⇂ V ⊢Local} -> .{ϕ : V ≤ U} -> _ ⇂ ϕ ⊢ AX ≤-Local BY -> _ ⇂ ϕ ⊢ su-Sort,ind {A = A} E AX ≤-Local su-Sort,ind E BY
  -- su-Term-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢ AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢ su-Sort,ind E AX
  -- su-Var-ind : ∀ E -> {AX : Γ ⋆-Ctx₊ E ⊢Sort k} -> Γ ⋆-Ctx₊ E ⊢Var AX -> Γ ,[ A ] ⋆-Ctx₊ su-Ctx₊ E ⊢Var su-Sort,ind E AX

  su-Ctx₊ t [] = []
  su-Ctx₊ t (E ,[ x ]) = su-Ctx₊ t E ,[ su-Sort,ind t _ x ]

  su-Sort,ind t E (Base x) = Base x
  su-Sort,ind t E (⨆ A B) = {!!}
  su-Sort,ind t E (⨅ S B) = ⨅ (su-Sort,ind t E S) (su-Sort,ind t (E ,[ S ]) B)
  su-Sort,ind t E _ = {!!}


  su-Sort t T = su-Sort,ind t [] T


  -- su-Ctx₊ : (E : Γ ,[ A ] ⊢Ctx₊) -> (t : Γ ⊢ A) -> Γ ⊢Ctx₊

  -- su₂-Type,ind : ∀ E -> {A : Γ ⊢Sort k} -> (t : Γ ⋆-Ctx₊ E ⊢ wks-Sort E A) -> (Z : Γ ,[ A ] ⋆-Ctx₊ E ⊢Sort k) -> Γ ⋆-Ctx₊ su-Ctx₊ t E ⊢Sort k
  -- su₂-Type,ind E t Y = ?


  -- End Substitution
  ------------------------------------------------------------------------

  ------------------------------------------------------------------------
  -- Equality

  data _⊢_≡_ : ∀ Γ {A : Γ ⊢Type} -> (a b : Γ ⊢ A) -> 𝒰₀ where
    -- β-rest-lam : ∀{F : Γ ,[ X ] ,[ A ] ⊢Type} {u v} (ϕ : Γ ⊢ u ≼ v) -> (t : Γ ,[ su-Sort v A ] ⊢ su-Sort,ind v _ F) -> Γ ⊢ rest (⨅ A F) ϕ (lam t) ≡ lam {!!}


  -- End Equality
  ------------------------------------------------------------------------

-}

  ----------------------------------------------------------
  -- Meta theorems

  -- We can restrict terms to smaller locations (W)
  --

  restrict-Var : W₀ ≤ W₁ ->  Γ ⊢Var A / b , W₁ -> Γ ⊢Var A / b , W₀
  restrict-Var {Γ = _,[_] {k = k} Γ (S / m , Wx)} ϕ zero = {!zero!}
  restrict-Var {Γ = _,[_] {k = k} Γ E} ϕ (suc v) = {!!}

  restrict : W₀ ≤ W₁ ->  Γ ⊢ A / type , W₁ -> Γ ⊢ A / type , W₀
  restrict ϕ (var x) = {!var x!}
  restrict ϕ (loc x) = {!!}
  restrict ϕ (fromext t) = {!!}
  restrict ϕ (lam t) = {!!}
  restrict ϕ (app t t₁) = {!!}
  restrict ϕ (π₁ t) = {!!}
  restrict ϕ (π₂ t) = {!!}
  restrict ϕ (t , t₁) = {!!}
  restrict ϕ (P ∋ t) = {!!}



module Examples where

  PP : Space
  PP = 𝒪ᶠⁱⁿ⁻ʷᵏ (𝒫ᶠⁱⁿ (𝔽 2))

  uu vv : ⟨ PP ⟩
  uu = ⦗ # 0 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  vv = ⦗ # 1 ⦘ ∷ [] since (IB.[] IB.∷ IB.[])
  all = uu ∨ vv

  ε : Ctx {PP}
  ε = []

  T0 : ∀{Γ : Ctx {PP}} -> Γ ⊢Type
  T0 = (Base NN ＠ uu) ⊗ (Base NN ＠ vv)

  t1 : ε ⊢ ⨅ (T0 / type , all) (Base NN ＠ uu) / type , all
  t1 = lam (π₁ (var zero))

  t2 : ε ⊢ ⨅ ((Base NN ＠ uu) ⊗ (Base NN ＠ vv) / type , all) ((Base NN ⊗ Base NN) ＠ uu) / type , all
  t2 = lam (loc (λ _ -> [ reflexive ]unloc (π₁ (var zero)) , [ reflexive ]unloc (π₁ (var zero))))

  f : (uu ∧ vv) ≤ vv
  f = π₁-∧

  t3 : ε ⊢ ⨅ (Base NN ＠ uu / type , all) (Com (uu ∧ vv) (Base NN ＠ vv)) / type , all
  t3 = {!!} -- lam (([ Base NN from uu to (uu ∧ vv) [ reflexive ⨾ π₀-∧ ]on all ]► End) ∋ (var zero ► ret (loc λ _ -> [ f ]unloc (fromext (var zero)))))






