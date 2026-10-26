{-# OPTIONS --without-K --cubical-compatible #-}

open import common
open import palg
open import inductive-repair.indspec
open import inductive-repair.config
open import inductive-repair.coherence
open import inductive-repair.wtype-config hiding (A ; B)
open import inductive-repair.palg-config

{-
   PUMPKIN Pi coherence conditions, derived directly from the
   *initial-algebra* structure.

   `inductive-repair.coherence` derives Ringer's `constr_ok`,
   `iota_ok`, and `elim_ok` from a `Config sig C D`.  This module
   shows the same three conditions arise from an `AlgConfig A B C D`
   — a pair of *initial* P-algebras for one polynomial — with no data
   beyond initiality:

     • `constr-ok-init` is, on the nose, the homomorphism square of
       the unique map `φ : C → D` that initiality of the source hands
       us (`algConfigToAlgEquiv`).  Nothing is proved: it is the
       `.snd` component of that homomorphism, read off by `happly`.

     • `iota_ok` and `elim_ok` are obtained by routing the two
       initial algebras through the bridge `initToHalf` (the
       "initial ⇒ has a dependent eliminator + β" direction of
       Awodey–Gambino–Sojakova), which manufactures, from each
       `InitAlgOn`, exactly the `IndAlg` a configuration carries.
       Feeding the resulting `Config` to the generic `Coherence`
       module yields the remaining two coherences.

   So the coherence conditions are a *consequence of initiality*, not
   extra data carried alongside it; the `Config`-level derivation of
   `inductive-repair.coherence` is recovered here as the special case
   where the two inductive algebras come from initial ones.
-}
module inductive-repair.palg-coherence {l : Level} (A : Type l) (B : A → Type l) where

  module AlgCoherence {C D : Type l} (acfg : AlgConfig A B C D) where
    open AlgConfig acfg

    {- The structure maps of the two initial algebras. -}
    σC : P A B C → C
    σC = InitAlgOn.sup initAlgC

    σD : P A B D → D
    σD = InitAlgOn.sup initAlgD

    {- The forward map: the unique homomorphism out of the initial
       source `(C , σC)` into `(D , σD)`, from initiality of the
       source. -}
    fwd : AlgHom (C , σC) (D , σD)
    fwd = fst (algConfigToAlgEquiv A B acfg)

    φ : C → D
    φ = fst fwd

    {- `constr_ok`, in pure algebra form: `φ` commutes with the
       structure maps.  This is *definitionally* the homomorphism
       witness `snd fwd` that initiality produced — not proved here,
       only read off pointwise with `happly`. -}
    constr-ok-init : (x : P A B C) → φ (σC x) ≡ σD (P-map φ x)
    constr-ok-init = happly (snd fwd)

    {- The W-type configuration determined by the two initial algebras
       and nothing else: each side's `IndAlg` is the dependent
       eliminator and β-law the bridge `initToHalf` extracts from
       initiality. -}
    cfg : Config (WTypeSignature {l} A B) C D
    cfg = record
      { indAlgC = initToHalf.initAlgToIndAlg A B initAlgC
      ; indAlgD = initToHalf.initAlgToIndAlg A B initAlgD }

    {- The full triple of PUMPKIN Pi coherences over `cfg` —
       `constr-ok`, `beta-ok-C`, `beta-ok-D`, and `elim-ok` — now
       sourced entirely from the initial-algebra structure. -}
    open Coherence cfg public
