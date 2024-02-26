
{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module KamiTheory.Main.Dependent.Typed.Examples where

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

open import KamiTheory.Basics
open import KamiTheory.Order.Preorder.Instances
open import KamiTheory.Main.Dependent.Untyped.Definition
open import KamiTheory.Main.Dependent.Untyped.Instances
open import KamiTheory.Main.Dependent.Typed.Definition
open import KamiTheory.Main.Dependent.Typed.Instances


open import KamiTheory.Main.Generic.ModeSystem.2Cell.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Definition
open import KamiTheory.Main.Generic.ModeSystem.2Graph.Example
open import KamiTheory.Main.Generic.ModeSystem.ModeSystem.Definition
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
  singleton i = singletonVec false true i 

  M : ModeSystem _
  M = SendReceiveNarrow-ModeSystem.SRN-ModeSystem PP {{it}} {{{!!}}}


  open Judgements M

  open Typecheck M

  open SendReceiveNarrow-2Graph
  open 2CellDefinition (graph M)

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
  uuvv = true ∷ (true ∷ (false ∷ []))



  _⟶_ = _▹▹_

  private variable
    -- n m : Nat
    p q : Term M n
    t u : Term M n
    Γ  : Con (Entry M) n
    A B C : Term M n
    U V W R : P
    k l o r : Mode M
    μ : ModeHom M k l
    η : ModeHom M o r

  _⊢_≔_ : (Γ : Con (Entry M) n) → Entry M n → Term M n → Set
  Γ ⊢ E ≔ t = Γ ⊢ t ∶ E

  εε : Con (Entry M) zero
  εε = ε


  idM : (a : Mode M) -> ModeHom M a a
  idM a = id

  ---------------------------------------------
  -- small examples

  P0 : εε ∙ (NN / (`＠` uu ⨾ id)) ⊢ var zero (incl idT) ∶ NN / `＠` uu ⨾ id
  P0 = var zero idT

  P1 : εε ⊢ ((Modal NN (`＠` uu ⨾ id) / id) ▹▹[ _ ] Modal NN (`＠` uu ⨾ id)) / id
       ≔ _
  P1 = lamⱼ (Modalⱼ (NNⱼ )) (letunmodⱼ (var zero idT) (modⱼ ((var zero idT))))


  ---------------------------------------------
  -- manual examples

  Com : ∀ (U V : P) -> ModalityTrans M vis (_ ↝ _ ∋ `＠` U ⨾ id) (_ ↝ _ ∋ `＠` V ⨾ id)
  Com U V = _ ⇒ _ ∋ [ (incl
          ( incl (id ⌟[ send V ]⌞ `＠` U ⨾ id ⌟)
          ∷ incl (`＠` V ⨾ id ⌟[ recv U ]⌞ id ⌟)
          ∷ [])) ] --  {!id ⨾ base (send V)!} ◇ {!!}

  -- sync : Γ ⊢Entry A / μ -> Γ ⊢ Π 
  --      -> Γ ⊢ t ∶ A / μ
  -- sync = {!!}



{-

  RES : Term M 0
  RES = te'
    where
      te : Term M 0
      te = _

      com : εε ⊢ (Modal NN (`＠` uu ⨾ id) / id) ▹▹[ {!!} ] (Modal NN (`＠` uu ⨾ id)) / id
        ≔ te -- lam {!!} (mod (transform {!!} (letunmod (var zero {!!}))))
      com = lamⱼ (Modalⱼ (NNⱼ)) (letunmodⱼ ((var  zero idT))
                                                    (modⱼ (transformⱼ (Com uu uu) (var zero idT))) )

      te' = untransform-Term te


      -- SendVec-Term = lam (natrec Tr
      --                         end
      --                         (lam (lam ((NN / (`＠` uu ⨾ id) ⇒ (`＠` vv ⨾ id)) ≫ var zero)))
      --                         (unmod (var zero)))

      -- postulate
      SendVec-Term = _
      SendVec : εε ⊢ ((Modal NN (`＠` uuvv ⨾ id) / id) ▹▹[ _ ] Tr / id)

                  ≔ SendVec-Term

      SendVec = {!!} -- lamⱼ proof (letunmodⱼ (var zero idT)
                -- (natrecⱼ Trⱼ endⱼ (lamⱼ proof (lamⱼ Trⱼ (trⱼ (NNⱼ) (Com uu uuvv) ≫ⱼ var zero idT))) (var zero idT))
                -- )

-}

      -- sendvec2 : εε ∙ (
      --           Π (NN / `＠` (uuvv) ⨾ id) ▹
      --           Π (Vec NN (var zero (incl {!!})) / `＠` (uu) ⨾ id) ▹[ wk1 (wk1 (SendVec-Term)) ∘ var (suc zero) (incl idT) ]
      --           Vec NN (var (suc zero) (incl {!!})) / `＠` vv ⨾ id
      --           ) ⊢
      --           Π (NN / `＠` uu ⨾ id) ▹
      --           Π (Vec NN (var zero (incl idT)) / `＠` (uu) ⨾ id) ▹[ (NN / (_ ↝ _ ∋ `＠` uu ⨾ id) ⇒ (_ ↝ _ ∋ `＠` (uuvv) ⨾ id)) ≫ (wk1 (wk1 (wk1 (SendVec-Term))) ∘ var (suc zero) (incl {!!})) ]
      --           Vec NN (transform {!!} (var (suc zero) {!!})) / `＠` vv ⨾ id
      --           ≔ {!!}

      -- sendvec2 = {!lamⱼ ? ?!}
       -- lamⱼ {!!} (lamⱼ {!!} (castⱼ {!!} ((var {{ΓP = {!!}}} (suc (suc zero)) id ∘ⱼ transformⱼ {!!} (var {{ΓP = {!!}}} (suc zero) id)) ∘ⱼ {!!})))





{-
  ---------------------------------------------
  -- automatic derivation

  -------------------
  -- deriving variables in a context
  -- P0 : all ∣ εε ∙ (NN / `＠` uu ⨾ id) ⊢ var zero ∶ NN / `＠` uu ⨾ id
  -- P0 = proof

  -- P1 : all ∣ εε ∙ (NN / `＠` uu ⨾ id) ∙ (NN / `＠` vv ⨾ id) ⊢ var (suc zero) ∶ NN / `＠` uu ⨾ id
  -- P1 = proof

  -- P2 : all ∣ εε ∙ (NN / `＠` uu ⨾ id) ∙ (wk (liftn (step id) n0) NN / `＠` uu ⨾ id) ⊢ var (zero) ∶ NN [ zeroₜ ] / `＠` uu ⨾ id
  -- P2 = proof


  -- -------------------
  -- -- deriving functions
  -- PF0 : all ∣ εε ⊢ lam (var zero) ∶ (NN / `＠` uu ⨾ id) ▹▹ NN / `＠` uu ⨾ id
  -- PF0 = proof

  Com : ∀ (U V : P) -> ModeTrans (`＠` U ⨾ id) (`＠` V ⨾ id) vis
  Com U V = {!!} --  {!id ⨾ base (send V)!} ◇ {!!}


  ---------------------------------------------
  -- manual examples

  com : εε ⊢ (Modal NN (`＠` uu) / id) ▹▹[ {!!} ] (Modal NN (`＠` vv)) / id
     ≔ lam (mod (transform (unmod (var zero))))
  com = lamⱼ proof (modⱼ (transformⱼ (Com uu vv) (unmodⱼ (var zero id))))


  SendingVector : ℕ
  SendingVector = 1
    where

      SendVec-Term = lam (natrec Tr
                              end
                              (lam (lam ((NN / (`＠` uu ⨾ id) ⇒ (`＠` vv ⨾ id)) ≫ var zero)))
                              (unmod (var zero)))

      postulate
        SendVec : εε ⊢ ((Modal NN (`＠` uu) / id-◯) ▹▹ Tr / id-◯)

                  ≔ SendVec-Term

      -- SendVec = lamⱼ proof (natrecⱼ Trⱼ endⱼ (lamⱼ proof (lamⱼ Trⱼ (trⱼ NNⱼ (Com uu ((uu ∧ vv))) ≫ⱼ var zero id))) (unmodⱼ (var zero id)))


      -- sendvec1 : εε ⊢
      --           Π (NN / `＠` (uu ∧ vv) ⨾ id) ▹
      --           Π (Vec NN (var zero) / `＠` (uu) ⨾ id) ▹[ wk1 (wk1 (SendVec-Term)) ∘ var (suc zero) ]
      --           Vec NN (var (suc zero)) / `＠` vv ⨾ id
      --           ≔ {!!}
      -- sendvec1 = lamⱼ proof (lamⱼ (Vecⱼ NNⱼ (var zero {!!}))
      --            {!vecrecⱼ ? ? ? ? ?!}
      --            )

      sendvec2 : εε ∙ (
                Π (NN / `＠` (uu ∧ vv) ⨾ id) ▹
                Π (Vec NN (var zero) / `＠` (uu) ⨾ id) ▹[ wk1 (wk1 (SendVec-Term)) ∘ var (suc zero) ]
                Vec NN (var (suc zero)) / `＠` vv ⨾ id
                ) ⊢
                Π (NN / `＠` uu ⨾ id) ▹
                Π (Vec NN (var zero) / `＠` (uu) ⨾ id) ▹[ (NN / (`＠` uu ⨾ id) ⇒ (`＠` (uu ∧ vv) ⨾ id)) ≫ (wk1 (wk1 (wk1 (SendVec-Term))) ∘ var (suc zero)) ]
                Vec NN (transform (var (suc zero))) / `＠` vv ⨾ id
                ≔ {!!}
      sendvec2 = lamⱼ {!!} (lamⱼ {!!} (castⱼ {!!} ((var {{ΓP = {!!}}} (suc (suc zero)) id ∘ⱼ transformⱼ {!!} (var {{ΓP = {!!}}} (suc zero) id)) ∘ⱼ {!!})))




  -- sendvec1 = lamⱼ proof (lamⱼ proof (vecrecⱼ {U = uu} {V = vv} {μs = id} {ηs = id}
  --            ((Vecⱼ NNⱼ ((var (suc (zero)) proof)))) -- = G
  --            nilⱼ -- = z
  --            {!!} -- = s
  --            ((var (suc zero) proof)) -- = n
  --            (var zero proof))) -- = v



{-
  -- easy, a variable in a context:
  t0 : all ∣ εε ∙ (NN / `＠` U ⨾ id) ⊢ var zero ∶ NN / `＠` U ⨾ id
  t0 = var zero

  -- not so easy, sending from uu to vv
  t1 : all ∣ εε ⊢ (Modal NN (`＠` uu) / id) ▹▹ Modal NN (`＠` vv) / id
     ≔ lam (recv (mod (send (unmod (var zero)))))
  t1 = lamⱼ proof (recvⱼ uu (modⱼ (sendⱼ vv (unmodⱼ (var zero)))))

  +ₙ : all ∣ εε ⊢ lam (lam (natrec NN (var (suc zero)) _ _)) ∶ (NN /  `＠` U ⨾ id) ▹▹ ((NN /  `＠` U ⨾ id) ▹▹ NN) /  `＠` U ⨾ id
  +ₙ = lamⱼ NNⱼ (lamⱼ NNⱼ (natrecⱼ NNⱼ (var (suc zero)) (lamⱼ NNⱼ (lamⱼ NNⱼ (sucⱼ (var zero)))) (var zero)))

-}

{-
  zerov : all ∣ εε  ⊢ lam (natrec (Vec NN (var zero)) nilₜ (lam (lam (consₜ zeroₜ (var zero)))) (var zero)) ∶ Π (NN / `＠` uu ⨾ id) ▹ (Vec NN (var zero)) / `＠` uu ⨾ id
  zerov = lamⱼ NNⱼ (natrecⱼ (Vecⱼ NNⱼ (var zero)) nilⱼ ( (lamⱼ NNⱼ (lamⱼ                     -- now lets call this NNⱼ variable n
                                   (Vecⱼ NNⱼ (var zero))   -- and this vec variable vv (it has length n)
                                   (consⱼ -- we want to append to vv
                                          (zeroⱼ ) -- we want to append zero (ugh)
                                          (var zero)))) -- we want to append to vv, yes!
                                  ) (var zero))

  -}

  -- ttt = derive-Var (εε ∙ (NN / ▲ uu)) zero NN (▲ uu)



  -- +ₙ : all ∣ εε ⊢ lam (lam (natrec NN (var (suc zero)) _ _)) ∶ (NN / ▲ U) ▹▹ ((NN / ▲ U) ▹▹ NN) / ▲ U
  -- +ₙ {U = U} = lamⱼ NNⱼ (lamⱼ NNⱼ (natrecⱼ {G = NN} NNⱼ proof (lamⱼ NNⱼ (lamⱼ NNⱼ (sucⱼ (var zero)))) (var zero)))

{-
  -- zerov :  all ∣ εε  ⊢ _ ∶ Π (NN / ▲ U) ▹ (Vec NN (var zero)) / ▲ U
  -- zerov = lamⱼ NNⱼ (natrecⱼ                   -- lets call this NNⱼ variable l
  --                     {G = Vec NN (var zero)} -- we want to produce a Vec NN l
  --                     (Vecⱼ NNⱼ (var zero))   -- that is a valid type in (ε ∙ NNⱼ)
  --                     nilⱼ                    -- for l=0 we give empty vector
  --                     (lamⱼ NNⱼ (lamⱼ                     -- now lets call this NNⱼ variable n
  --                                 (Vecⱼ NNⱼ (var zero))   -- and this vec variable vv (it has length n)
  --                                 (consⱼ -- we want to append to vv
  --                                        {!zeroⱼ!} -- we want to append zero (ugh)
  --                                        {!(var zero)!}))) -- we want to append to vv, yes!
  --                     (var zero))             -- we recurse on l



  T0 : all ∣ εε ⊢Sort NN
  T0 = NNⱼ

  t0 : all ∣ εε ⊢ (NN / ▲ U) ▹▹ (NN ×× NN) / ▲ U
          ≔ lam (var zero ,ₜ var zero)

  t0 = lamⱼ NNⱼ (prodⱼ NN NN (var zero) (var zero))

  t1 : all ∣ ε ⊢ _ ∶ ((((NN ＠ U) / ◯) ×× (NN ＠ U)) / ◯) ▹▹ (NN ×× NN) / ▲ U
  t1 = lamⱼ (Σⱼ Locⱼ _ NNⱼ ▹ Locⱼ _ NNⱼ) (prodⱼ NN NN (unlocⱼ (fstⱼ (NN ＠ _) (NN ＠ _) (var zero))) ((unlocⱼ (sndⱼ (NN ＠ _) (NN ＠ _) (var zero)))))

  t2 : uu ∣ ε ⊢ _ ∶ NN ＠ vv / ◯
  t2 = locskipⱼ λ { (incl (take (incl (drop ())) ∷ a))}


  {-
  ---------------------------------------------
  -- communication

  -- We can send a value
  c0 : all ∣ ε ⊢ _ ∶ ((NN ＠ uu) / ◯ ⟶ Com all (NN ＠ (uu ∧ vv))) / ◯
  c0 = lamⱼ (Locⱼ _ NNⱼ) (comⱼ (Shareⱼ uu _ π₀-∧ NNⱼ) (shareⱼ NNⱼ (var zero) π₀-∧))

  -- We can join two communications
  c1 : all ∣ ε ⊢ _ ∶
       (
         (( (NN ＠ uu) / ◯ ⟶ Com R (NN ＠ vv)) / ◯)
      ⟶ (((((NN ＠ vv) / ◯ ⟶ Com R (NN ＠ ww)) / ◯)
      ⟶  ((NN ＠ uu) / ◯ ⟶ Com R (NN ＠ ww))))
       ) / ◯
  c1 = lamⱼ (Πⱼ Locⱼ _ NNⱼ ▹ Comⱼ (Locⱼ _ NNⱼ))
       (lamⱼ ((Πⱼ Locⱼ _ NNⱼ ▹ Comⱼ (Locⱼ _ NNⱼ)))
       (lamⱼ (Locⱼ _ NNⱼ)
      (comⱼ (Univ-Comⱼ (comtypeⱼ (Locⱼ _ NNⱼ) (var (suc (suc zero)) ∘ⱼ var zero))
        ≫ⱼ Univ-Comⱼ ((comtypeⱼ (Locⱼ _ NNⱼ) (var (suc (suc zero)) ∘ⱼ var zero ))))
      (comvalⱼ (Locⱼ _ NNⱼ) ((var (suc (suc zero)) ∘ⱼ var zero))
        >ⱼ comvalⱼ (Locⱼ _ NNⱼ) ((var (suc (suc zero)) ∘ⱼ var zero))) )))
  -}
-}
-}
