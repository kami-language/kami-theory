





{-
  {-


  {-


{-


{-
  send-vec : εε ∙
    (
      Π NN /▹
      Π (Π NN / ＠ uu ▹ UU) / ◻ ▹
      ⟨ x0 ∘[ ＠ uu ] zeroₜ ∣ ◻ ⟩ /▹▹
      ⟨ Π NN / ＠ uu ▹ (x1 ∘[ ＠ uu ] x0) /▹▹ (x1 ∘[ ＠ uu ] sucₜ x0)  ∣ ◻ ⟩ /▹▹
      ⟨ x0 ∘[ ＠ uu ] x1[ id ★ηᵈˢ★ ＠ uu ] ∣ ◻ ⟩ / ＠ uu
    )
  ⊢
    Π NN / ＠ uuvv ▹
    Π Vec BB (letunmod[ ＠ uuvv ] x0 by x0[ {!!} ]) / ＠ uu ▹
    ⟨ Vec BB (letunmod[ ＠ uuvv ] x0 by x0[ {!!} ]) ∣ ＠ vv ⟩ / id
    ≔ {!!}
  send-vec =
    lamⱼ NNⱼ ↦
    {!!}
    -}

{-
                 -}
  ---------------------------------------------
  -- manual examples

  -- Com : ∀ (U V : P) -> ModalityTrans M vis (_ ↝ _ ∋ `＠` U ⨾ id) (_ ↝ _ ∋ `＠` V ⨾ id)
  -- Com U V = _ ⇒ _ ∋ [ (incl
  --         ( incl (id ⌟[ send V ]⌞ `＠` U ⨾ id ⌟)
  --         ∷ incl (`＠` V ⨾ id ⌟[ recv U ]⌞ id ⌟)
  --         ∷ [])) ] --  {!id ⨾ base (send V)!} ◇ {!!}

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
-}
-}
-}
-}
