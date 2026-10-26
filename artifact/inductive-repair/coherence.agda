{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.config

{-
    Proposition 2.4
    PUMPKIN Pi coherence conditions derived from a `Config`:
    `constr_ok`, the per-side β-rules (`iota_ok`), and `elim_ok`
    are consequences of the two h-initial structures and the
    induced equivalence — none is postulated.
-}
module inductive-repair.coherence {ℓ : Level} where
    open Signature
    open _≃_

    {-
        Proposition 2.4 (Correctness Conditions)
        The coherence conditions over a configuration. The carrier
        equivalence `configToEquiv cfg` lifts to constructor
        arguments via `mapArgs-eqv`; `constr-ok` relates the two
        algebras across these (one step from `fold-β`), the
        per-side β-rules are the local `IndAlg.beta`, and
        `elim-ok` follows from `IndAlg.ind`.
    -}
    module Coherence {sig : Signature {ℓ}} {C D : Type ℓ} (cfg : Config sig C D) where
        open Config cfg
        open IndAlg indAlgC renaming (algebra to algC; ind to indC; beta to betaC; fold to foldC; fold-β to foldC-β)
        open IndAlg indAlgD renaming (algebra to algD; ind to indD; beta to betaD)

        carrier-eqv : C ≃ D
        carrier-eqv = snd (configToEquiv cfg)

        -- The carrier equivalence lifted to constructor arguments.
        args-eqv : (op : Op sig) → Args (arity sig op) C ≃ Args (arity sig op) D
        args-eqv op = mapArgs-eqv (arity sig op) carrier-eqv

        {-
            Proposition 2.4 (1)
            `constr_ok`: constructors preserve heterogeneous
            equality across the carrier and argument equivalences.
        -}
        constr-ok : (op : Op sig) {argsC : Args (arity sig op) C}
                                   {argsD : Args (arity sig op) D} →
                    argsC ≡[ args-eqv op ] argsD →
                    algC op argsC ≡[ carrier-eqv ] algD op argsD
        constr-ok op {argsC} p =
            foldC-β algD op argsC
          • ap (algD op) (! (mapArgs-eqv-f (arity sig op) carrier-eqv argsC) • p)

        {-
            Proposition 2.4 (2)
            `iota_ok` is per side: each carrier's own β-rule,
            exposed under the paper's vocabulary.
        -}
        beta-ok-C : BetaLaw sig indC
        beta-ok-C = betaC

        beta-ok-D : BetaLaw sig indD
        beta-ok-D = betaD

        {-
            Lift C-side inductive hypotheses to D-side ones at the
            `f`-mapped args. The types coincide on the nose, so no
            transport is needed.
        -}
        lift-ihs : {P : D → Type ℓ} (cs : ConstrArity {ℓ}) (argsC : Args cs C) →
                   IHs cs (P ∘ f carrier-eqv) argsC →
                   IHs cs P (mapArgs cs (f carrier-eqv) argsC)
        lift-ihs Done         _            _            = tt
        lift-ihs (Nonrec T k) (t , args)   ihs          = lift-ihs (k t) args ihs
        lift-ihs (Rec _ cs)   (r , args)   (ih-h , ih-t) = (ih-h , lift-ihs cs args ih-t)

        {-
            C-side cases derived from D-side cases: delegate to
            `casesD` on the lifted args and transport back along
            `foldC-β`.
        -}
        deriveCasesC : (PD : D → Type ℓ) (casesD : Cases sig D algD PD) →
                       Cases sig C algC (PD ∘ f carrier-eqv)
        deriveCasesC PD casesD op argsC ihsC =
            tpt PD (! (foldC-β algD op argsC))
                (casesD op (mapArgs (arity sig op) (f carrier-eqv) argsC)
                        (lift-ihs (arity sig op) argsC ihsC))

        {-
            Proposition 2.4 (3)
            `elim_ok`: cross-side eliminator coherence. Proof by
            induction on `c`, using `betaC`, `betaD`, and an IH
            coherence on the recursive children.
        -}
        elim-ok : (PD : D → Type ℓ) (casesD : Cases sig D algD PD) (c : C) →
                  indC (PD ∘ f carrier-eqv) (deriveCasesC PD casesD) c
                    ≡ indD PD casesD (f carrier-eqv c)
        elim-ok PD casesD = indC motive cases'
          where
            motive : C → Type ℓ
            motive c = indC (PD ∘ f carrier-eqv) (deriveCasesC PD casesD) c
                         ≡ indD PD casesD (f carrier-eqv c)

            ihs-coherence : (cs : ConstrArity {ℓ}) (argsC : Args cs C) →
                            (ih : IHs cs motive argsC) →
                            lift-ihs cs argsC
                                (mkIHs cs (indC (PD ∘ f carrier-eqv) (deriveCasesC PD casesD)) argsC)
                              ≡ mkIHs cs (indD PD casesD) (mapArgs cs (f carrier-eqv) argsC)
            ihs-coherence Done         _            _              = refl
            ihs-coherence (Nonrec T k) (t , args)   ih             =
                ihs-coherence (k t) args ih
            ihs-coherence (Rec _ cs)   (r , args)   (ih-h , ih-t)  =
                ap2 _,_ (ext ih-h) (ihs-coherence cs args ih-t)

            cases' : Cases sig C algC motive
            cases' op argsC ih =
                betaC (PD ∘ f carrier-eqv) (deriveCasesC PD casesD) op argsC
              • ap (λ X → tpt PD (! (foldC-β algD op argsC))
                              (casesD op (mapArgs (arity sig op) (f carrier-eqv) argsC) X))
                    (ihs-coherence (arity sig op) argsC ih)
              • ap (tpt PD (! (foldC-β algD op argsC)))
                    (! (betaD PD casesD op (mapArgs (arity sig op) (f carrier-eqv) argsC)))
              • apd PD (indD PD casesD) (! (foldC-β algD op argsC))
