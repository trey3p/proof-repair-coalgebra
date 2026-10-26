{-# OPTIONS --without-K --cubical-compatible #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.palg-config
open import inductive-repair.wtype-config hiding (A ; B)

{-
    Conversions between configurations over some signature
    (`SigConfig`) and algebra configurations over some polynomial
    (`PAlgConfig`), in both directions.
-}
module inductive-repair.conversion where
    {-
        A `SigConfig C D` is a `Config` on `C` and `D` for some
        signature.
    -}
    record SigConfig {l : Level} (C D : Type l) : Type (lsuc l) where
        field
            sig : Signature
            config : Config sig C D

    {-
        A `PAlgConfig C D` is an `AlgConfig` on `C` and `D` for some
        choice of polynomial functor `P`.
    -}
    record PAlgConfig {l : Level} (C D : Type l) : Type (lsuc l) where
        field
            A : Type l
            B : A → Type l
            algConfig : AlgConfig A B C D

    

    {-
        Proposition 3.14 (Algebra Config iff Configuration), (→)
        Given a `SigConfig C D`, we can construct a `PAlgConfig C D`.
    -}
    configToPalg : {l : Level} {C D : Type l} → (SigConfig C D) → (PAlgConfig C D)
    configToPalg record { sig = sig ; config = config } =
        record {A = A; B = B; algConfig = algConfig}
        where
            wtypeConfig = allConfigWTypeConfig config
            A = wtypeConfig .fst
            B = wtypeConfig .snd .fst
            algConfig = wToAlg A B (wtypeConfig .snd .snd)


    {-
        Proposition 3.14 (Algebra Config iff Configuration), (←)
        Given a `PAlgConfig C D`, we can construct a `WTypeConfig` on
        its packaged `A` and `B`.
    -}
    palgConfigToConfig : {ℓ : Level} {C D : Type ℓ}
                         → (pcfg : PAlgConfig {ℓ} C D)
                         → WTypeConfig {ℓ} (PAlgConfig.A pcfg)
                                            (PAlgConfig.B pcfg) C D
    palgConfigToConfig record { A = A ; B = B ; algConfig = algConfig } =
        record
        { indAlgC = initToHalf.initAlgToIndAlg A B (AlgConfig.initAlgC algConfig)
        ; indAlgD = initToHalf.initAlgToIndAlg A B (AlgConfig.initAlgD algConfig)
        }
