{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.indalg-prop

{-
    Configurations for proof repair across type equivalences,
    following PUMPKIN Pi (Ringer et al., PLDI 2021): a `Config` is a
    structured presentation of an equivalence between two inductive
    types — two h-initial algebras for a common signature. This file
    constructs the source algebra and the equivalence from a
    configuration (`configToEquiv`) and, conversely, a configuration
    from an h-initial algebra and an equivalence (`equivToConfig`,
    via `transportIndAlg`); the two are mutually inverse
    (`configEquiv`).
-}
module inductive-repair.config {ℓ : Level} where
    open Signature
    open _≃_

    {-
        Definition 2.2 (Configuration)
        A `Config`: two h-initial algebras for the common
        signature `sig`. `C` is typically the "old" type whose
        proofs need repair, `D` the "new" type they are lifted to.
    -}
    record Config (sig : Signature {ℓ}) (C D : Type ℓ) : Type (lsuc ℓ) where
      field
        indAlgC : IndAlg sig C
        indAlgD : IndAlg sig D

    {-
       Transporting an IndAlg along an equivalence,
       pull D-data back to C with `g eqv`, eliminate
       there, push forward with `f eqv`; the β-rule is recovered
       from the equivalence's coherence (`coh` and the g-side
       triangle `gtri` from `common`).
    -}

    -- Repackage a C-side IH tuple (motive precomposed with `f eqv`)
    -- as a D-side IH tuple at the `f`-mapped arguments.
    ihPre→ihMap : {C D : Type ℓ} (eqv : C ≃ D) (cs : ConstrArity {ℓ})
                  (P : D → Type ℓ) (args : Args cs C) →
                  IHs cs (λ c → P (f eqv c)) args →
                  IHs cs P (mapArgs cs (f eqv) args)
    ihPre→ihMap eqv Done         P _          _         = tt
    ihPre→ihMap eqv (Nonrec A k) P (a , args) ih        = ihPre→ihMap eqv (k a) P args ih
    ihPre→ihMap eqv (Rec Dom cs) P (r , args) (hh , ih) = (hh , ihPre→ihMap eqv cs P args ih)

    transportIndAlg : {sig : Signature} {C D : Type ℓ} →
                      IndAlg sig C → C ≃ D → IndAlg sig D
    transportIndAlg {sig} {C} {D} ialg eqv = record
      { algebra = algD ; ind = indD ; beta = betaD }
      where
        open IndAlg ialg renaming (algebra to algC; ind to indC; beta to betaC)
        ff = f eqv
        gg = g eqv

        algD : ConstrAlgebra sig D
        algD op aD = ff (algC op (mapArgs (arity sig op) gg aD))

        -- round trip on C-args, by direct recursion on the arity
        rtC : (cs : ConstrArity {ℓ}) (a : Args cs C) →
              mapArgs cs gg (mapArgs cs ff a) ≡ a
        rtC Done         _       = refl
        rtC (Nonrec A k) (x , a) = ap (λ a' → (x , a')) (rtC (k x) a)
        rtC (Rec Dom cs) (r , a) = ap2 _,_ (ext (λ d → η eqv (r d))) (rtC cs a)

        -- round trip on D-args, by direct recursion on the arity
        δ : (cs : ConstrArity {ℓ}) (aD : Args cs D) →
            mapArgs cs ff (mapArgs cs gg aD) ≡ aD
        δ Done         _        = refl
        δ (Nonrec A k) (x , aD) = ap (λ a' → (x , a')) (δ (k x) aD)
        δ (Rec Dom cs) (r , aD) = ap2 _,_ (ext (λ d → ε'' eqv (r d))) (δ cs aD)

        -- the gg-image of the D-round-trip is the C-round-trip; this is
        -- where the g-side triangle `gtri` is used (at recursive children).
        star-core : (cs : ConstrArity {ℓ}) (aD : Args cs D) →
                    rtC cs (mapArgs cs gg aD) ≡ ap (mapArgs cs gg) (δ cs aD)
        star-core Done aD = refl
        star-core (Nonrec A k) (x , aD) =
            ap (ap (λ a' → (x , a'))) (star-core (k x) aD)
          • ! (ap-∘ {f = λ a' → (x , a')} {g = mapArgs (k x) gg} (δ (k x) aD))
          • ap-∘ {f = mapArgs (Nonrec A k) gg} {g = λ a' → (x , a')} (δ (k x) aD)
        star-core (Rec Dom cs) (r , aD) =
            ap2-cong _,_ fst-eq (star-core cs aD)
          • ! (ap-ap2-pair (λ r' → gg ∘ r') (mapArgs cs gg)
                  (ext (λ d → ε'' eqv (r d))) (δ cs aD))
          where
            fst-eq : ext (λ d → η eqv (gg (r d)))
                       ≡ ap (λ r' → gg ∘ r') (ext (λ d → ε'' eqv (r d)))
            fst-eq = ap ext (ext (λ d → gtri eqv (r d)))
                   • ! (postcomp-ext gg (λ d → ε'' eqv (r d)))

        module _ (P : D → Type ℓ) (cs : Cases sig D algD P) where
          Q : C → Type ℓ
          Q c = P (ff c)

          φ : (op : Op sig) (aC : Args (arity sig op) C) →
              ff (algC op aC) ≡ algD op (mapArgs (arity sig op) ff aC)
          φ op aC = ! (ap (λ x → ff (algC op x)) (rtC (arity sig op) aC))

          csC : Cases sig C algC Q
          csC op aC ihC =
              tpt P (! (φ op aC))
                  (cs op (mapArgs (arity sig op) ff aC)
                         (ihPre→ihMap eqv (arity sig op) P aC ihC))

        indD : Induction sig algD
        indD P cs d = tpt P (ε'' eqv d) (indC (Q P cs) (csC P cs) (gg d))

        -- IH coherence: transporting the pulled-back C-side IH tuple
        -- along `δ` reproduces the D-side IH tuple.
        acoh-gen : (P : D → Type ℓ) (cs : Cases sig D algD P)
                   (ar : ConstrArity {ℓ}) (aD : Args ar D) →
                   tpt (IHs ar P) (δ ar aD)
                       (ihPre→ihMap eqv ar P (mapArgs ar gg aD)
                          (mkIHs ar (indC (Q P cs) (csC P cs)) (mapArgs ar gg aD)))
                     ≡ mkIHs ar (indD P cs) aD
        acoh-gen P cs Done aD = refl
        acoh-gen P cs (Nonrec A k) (x , aD) =
            tpt-ap (IHs (Nonrec A k) P) (λ a' → (x , a')) (δ (k x) aD) _
          • acoh-gen P cs (k x) aD
        acoh-gen P cs (Rec Dom cs') (r , aD) =
            tpt-×-ap2 (λ r' → (d : Dom) → P (r' d)) (λ a' → IHs cs' P a')
                      (ext (λ d → ε'' eqv (r d))) (δ cs' aD) _ _
          • ap2 _,_ recfun-eq (acoh-gen P cs cs' aD)
          where
            recfun-eq : tpt (λ r' → (d : Dom) → P (r' d))
                            (ext (λ d → ε'' eqv (r d)))
                            (λ d → indC (Q P cs) (csC P cs) (gg (r d)))
                          ≡ (λ d → indD P cs (r d))
            recfun-eq =
                tpt-pi-dom (ext (λ d → ε'' eqv (r d))) _
              • ext (λ d → ap (λ p → tpt P p (indC (Q P cs) (csC P cs) (gg (r d))))
                              (happlyExt (λ d → ε'' eqv (r d)) d))

        -- At a constructor, the transported C-case equals the supplied
        -- D-case applied to the D-side IHs.
        part2 : (P : D → Type ℓ) (cs : Cases sig D algD P)
                (op : Op sig) (aD : Args (arity sig op) D) →
                csC P cs op (mapArgs (arity sig op) gg aD)
                    (mkIHs (arity sig op) (indC (Q P cs) (csC P cs))
                           (mapArgs (arity sig op) gg aD))
                  ≡ cs op aD (mkIHs (arity sig op) (indD P cs) aD)
        part2 P cs op aD =
            ap (λ p → tpt P p w') star
          • tpt-ap P (algD op) δ' w'
          • tpt-app2 (cs op) δ' ih₁
          • ap (cs op aD) acoh
          where
            QQ   = Q P cs
            cscC = csC P cs
            aC   = mapArgs (arity sig op) gg aD
            ih₁  = ihPre→ihMap eqv (arity sig op) P aC
                     (mkIHs (arity sig op) (indC QQ cscC) aC)
            w'   = cs op (mapArgs (arity sig op) ff aC) ih₁
            δ'   = δ (arity sig op) aD
            star : ! (φ P cs op aC) ≡ ap (algD op) δ'
            star = !! (ap (λ x → ff (algC op x)) (rtC (arity sig op) aC))
                 • ap (ap (λ x → ff (algC op x))) (star-core (arity sig op) aD)
                 • ! (ap-∘ {f = λ x → ff (algC op x)}
                          {g = mapArgs (arity sig op) gg} δ')
            acoh : tpt (IHs (arity sig op) P) δ' ih₁
                     ≡ mkIHs (arity sig op) (indD P cs) aD
            acoh = acoh-gen P cs (arity sig op) aD

        betaD : BetaLaw sig indD
        betaD P cs op aD =
            ap (tpt P (ε'' eqv (ff X)))
               (p1 • ap (tpt QQ (! (η eqv X))) p2)
          • ap (tpt P (ε'' eqv (ff X))) (! (tpt-ap P ff (! (η eqv X)) w))
          • ! (tpt-• P (ap ff (! (η eqv X))) (ε'' eqv (ff X)) w)
          • ap (λ q → tpt P q w) collapse
          • part2 P cs op aD
          where
            QQ  = Q P cs
            cscC = csC P cs
            aC  = mapArgs (arity sig op) gg aD
            X   = algC op aC
            ihC₀ = mkIHs (arity sig op) (indC QQ cscC) aC
            w   = cscC op aC ihC₀

            p1 : indC QQ cscC (gg (ff X)) ≡ tpt QQ (! (η eqv X)) (indC QQ cscC X)
            p1 = flip-tpt QQ (η eqv X) (apd QQ (indC QQ cscC) (η eqv X))

            p2 : indC QQ cscC X ≡ w
            p2 = betaC QQ cscC op aC

            collapse : ap ff (! (η eqv X)) • ε'' eqv (ff X) ≡ refl
            collapse =
                ap (λ p → p • ε'' eqv (ff X)) (ap-! ff (η eqv X))
              • ap (λ p → ! p • ε'' eqv (ff X)) (coh eqv X)
              • •invl

    {-
        Lifting an equivalence to a configuration: the original
        h-initial algebra together with the transported one form a
        `Config sig C D`. This is the principal way a configuration
        is constructed in practice.
    -}
    equivToConfig : {sig : Signature} {C D : Type ℓ} →
                    IndAlg sig C → C ≃ D → Config sig C D
    equivToConfig hc eqv .Config.indAlgC = hc
    equivToConfig {sig} hc eqv .Config.indAlgD = transportIndAlg hc eqv

    {-
        A `Config sig C D` yields its source h-initial algebra
        together with an equivalence `C ≃ D`: the maps are the
        folds between the two h-initial algebras, and both
        composites are the identity by `fold-roundtrip`.
    -}
    configToEquiv : {sig : Signature} {C D : Type ℓ} →
                    Config sig C D → IndAlg sig C × (C ≃ D)
    configToEquiv {sig} {C} {D} cfg =
        Config.indAlgC cfg ,
        record {f = f' ; g = g' ; η = n' ; h = h' ; ε = e'}
      where
        open Config cfg
        open IndAlg indAlgC renaming (algebra to algC; fold to foldC)
        open IndAlg indAlgD renaming (algebra to algD; fold to foldD)

        f' : C → D
        f' = foldC algD

        g' : D → C
        g' = foldD algC

        n' : (x : C) → g' (f' x) ≡ x
        n' = fold-roundtrip indAlgC indAlgD

        h' : D → C
        h' = g'

        e' : (d : D) → f' (h' d) ≡ d
        e' = fold-roundtrip indAlgD indAlgC

    {-
        `equivToConfig` and `configToEquiv` are mutually inverse
        (`configEquiv` below): a configuration is *exactly* an
        h-initial algebra on the source together with an
        equivalence of carriers.

        Round trips: on the equivalence side, `f eqv` is an algebra
        homomorphism into the transported algebra, so it agrees
        with the fold that `configToEquiv` extracts (`fold-unique`),
        and equivalences with equal forward maps are equal
        (`≃-≡-intro`); on the configuration side, the transported
        algebra agrees with the target algebra (`fold-β` plus the
        fold round-trip), and `IndAlg`s with equal algebras are
        equal (`indAlg-≡-intro`).
    -}
    private
      module CE {sig : Signature} {C D : Type ℓ} where
        ceFwd : IndAlg sig C × (C ≃ D) → Config sig C D
        ceFwd p = equivToConfig (fst p) (snd p)

        ceBwd : Config sig C D → IndAlg sig C × (C ≃ D)
        ceBwd = configToEquiv

        private
          ceη-body : (p : IndAlg sig C × (C ≃ D)) → ceBwd (ceFwd p) ≡ p
          ceη-body (ia , eqv) =
              ap (λ z → (ia , z))
                 (≃-≡-intro (snd (configToEquiv (equivToConfig ia eqv))) eqv
                    (! (ext (λ x → fold-unique ia algD' (f eqv) hom x))))
            where
              algC : ConstrAlgebra sig C
              algC = IndAlg.algebra ia
              algD' : ConstrAlgebra sig D
              algD' = IndAlg.algebra (transportIndAlg ia eqv)
              -- `f eqv` is a homomorphism into the transported
              -- algebra: its constructor square is the args
              -- round-trip pushed through `algC`.
              hom : (c : Op sig) (args : Args (arity sig c) C) →
                    f eqv (algC c args)
                      ≡ algD' c (mapArgs (arity sig c) (f eqv) args)
              hom c args =
                  ap (λ z → f eqv (algC c z))
                     (! ( mapArgs-∘ (arity sig c) (f eqv) (g eqv) args
                        • mapArgs-id-pw (arity sig c) (λ x → g eqv (f eqv x)) args
                                        (mkIHs (arity sig c) (η eqv) args)))

          ceε-body : (cfg : Config sig C D) → ceFwd (ceBwd cfg) ≡ cfg
          ceε-body cfg =
              ap (λ z → record { indAlgC = Config.indAlgC cfg ; indAlgD = z })
                 (indAlg-≡-intro
                    (transportIndAlg (Config.indAlgC cfg) (snd (configToEquiv cfg)))
                    (Config.indAlgD cfg)
                    pa)
            where
              ff : C → D
              ff = f (snd (configToEquiv cfg))
              gg : D → C
              gg = g (snd (configToEquiv cfg))
              algC : ConstrAlgebra sig C
              algC = IndAlg.algebra (Config.indAlgC cfg)
              algD : ConstrAlgebra sig D
              algD = IndAlg.algebra (Config.indAlgD cfg)
              rt : (d : D) → ff (gg d) ≡ d
              rt = fold-roundtrip (Config.indAlgD cfg) (Config.indAlgC cfg)
              -- The transported algebra agrees with the target one:
              -- `fold-β`, then collapse the `D`-side round-trip.
              pa-pw : (c : Op sig) (aD : Args (arity sig c) D) →
                      ff (algC c (mapArgs (arity sig c) gg aD)) ≡ algD c aD
              pa-pw c aD =
                  IndAlg.fold-β (Config.indAlgC cfg) algD c
                                (mapArgs (arity sig c) gg aD)
                • ap (algD c)
                     ( mapArgs-∘ (arity sig c) gg ff aD
                     • mapArgs-id-pw (arity sig c) (λ d → ff (gg d)) aD
                                     (mkIHs (arity sig c) rt aD))
              pa : IndAlg.algebra
                     (transportIndAlg (Config.indAlgC cfg) (snd (configToEquiv cfg)))
                     ≡ algD
              pa = ext (λ c → ext (λ aD → pa-pw c aD))

        -- Thin `abstract` seals over the transparent bodies (cf. the
        -- `initToHalf`/`FAI` seals): the round-trip proofs are record
        -- fields below, so their bodies must not unfold during
        -- conversion checking.
        abstract
          ceη : (p : IndAlg sig C × (C ≃ D)) → ceBwd (ceFwd p) ≡ p
          ceη = ceη-body

          ceε : (cfg : Config sig C D) → ceFwd (ceBwd cfg) ≡ cfg
          ceε = ceε-body

    {-
        Proposition 2.3 (Configurations and Inductive Equivalences are Equivalent)
        The correspondence theorem: configurations are equivalent
        to pairs of an h-initial source algebra and a carrier
        equivalence.
    -}
    configEquiv : {sig : Signature} {C D : Type ℓ} →
                  (IndAlg sig C × (C ≃ D)) ≃ Config sig C D
    configEquiv = record
      { f = CE.ceFwd ; g = CE.ceBwd ; η = CE.ceη
      ; h = CE.ceBwd ; ε = CE.ceε }

