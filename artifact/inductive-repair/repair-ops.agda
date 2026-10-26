{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import inductive-repair.indspec
open import inductive-repair.config

{-
    Dependent repair operator across a full `Config`: lifts a theorem
    over `C` to a theorem ranging over `D` via the configuration's
    equivalence, with a one-step coherence proof.
-}
module inductive-repair.repair-ops {ℓ : Level} where
    open Signature
    open _≃_

    {-
        Dependent repair: lift a theorem `(c : C) → P c` to
        `(d : D) → P (g eqv d)` — the predicate stays on the C
        side; only the binder is replaced via the equivalence's
        inverse.
    -}
    repair-Π : {sig : Signature} {C D : Type ℓ} →
               (cfg : Config sig C D) →
               (P : C → Type ℓ) →
               ((c : C) → P c) →
               (d : D) → P (g (snd (configToEquiv cfg)) d)
    repair-Π cfg P pf d = pf (g (snd (configToEquiv cfg)) d)

    {- Coherence: transport along the round-trip `η` sends the
       repaired theorem back to the original — one `apd`. -}
    repair-Π-coh : {sig : Signature} {C D : Type ℓ} →
                   (cfg : Config sig C D) (P : C → Type ℓ) →
                   (pf : (c : C) → P c) (c : C) →
                   tpt P (η (snd (configToEquiv cfg)) c)
                       (repair-Π cfg P pf (f (snd (configToEquiv cfg)) c))
                     ≡ pf c
    repair-Π-coh cfg P pf c =
        apd P pf (η (snd (configToEquiv cfg)) c)
