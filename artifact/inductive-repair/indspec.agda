{-# OPTIONS --without-K  --cubical-compatible #-}

open import common

module inductive-repair.indspec where

open _≃_

private
  variable
    ℓ : Level

{-  
    Definition 2.1
    The syntactic shape of a single constructor's argument list — a
    telescope, where each step is either a non-recursive (`Nonrec`) or
    recursive (`Rec`) argument.

    `Done`              terminates the telescope.
    `Nonrec A k`        a non-recursive argument of type `A`;
                        the continuation `k` may depend on its value.
    `Rec D cs`          a recursive argument with domain `D`;
                        the continuation does NOT depend on its value
                        (so the signature is functorial in the carrier).
                        `D` may itself depend on prior nonrec values
                        because it is supplied at the call site.

    Nonrec and rec arguments may be freely interleaved.
-}
data ConstrArity {ℓ : Level} : Type (lsuc ℓ) where
  Done   : ConstrArity
  Nonrec : (A : Type ℓ) → (A → ConstrArity {ℓ}) → ConstrArity
  Rec    : (D : Type ℓ) → ConstrArity {ℓ} → ConstrArity

{- 
    Definition 2.1
    A signature for a single-sorted inductive type: one operation per
    constructor label, each tagged with its arity.
-}
record Signature : Type (lsuc ℓ) where
  field
    Op    : Type ℓ
    arity : Op → ConstrArity {ℓ}
open Signature

{-
    Definition 2.1
    The type of arguments to a constructor of the given arity, with `Ty`
    as the carrier for recursive positions. A Σ-chain reading off the
    arity: one Σ per Nonrec, one × per Rec.
-}
Args : ConstrArity {ℓ} → Type ℓ → Type ℓ
Args Done         _  = ⊤
Args (Nonrec A k) Ty = Σ A (λ a → Args (k a) Ty)
Args (Rec D cs)   Ty = (D → Ty) × Args cs Ty

{-
    Definition 2.1 (Constructor Algebra)
    An algebra for `sig` on the carrier `Ty`: an interpretation of each
    operation taking its arguments to a term of `Ty`.
-}
ConstrAlgebra : (sig : Signature {ℓ}) → (Ty : Type ℓ) → Type ℓ
ConstrAlgebra sig Ty = (c : Op sig) → Args (arity sig c) Ty → Ty

{-
    Functorial action of an arity: postcompose every recursive function
    with `f`, keeping nonrec data unchanged.
-}
mapArgs : (cs : ConstrArity {ℓ}) {Ty₁ Ty₂ : Type ℓ} →
    (Ty₁ → Ty₂) → Args cs Ty₁ → Args cs Ty₂
mapArgs Done         f _            = tt
mapArgs (Nonrec A k) f (a , args)   = (a , mapArgs (k a) f args)
mapArgs (Rec D cs)   f (r , args)   = (f ∘ r , mapArgs cs f args)

{-
    Functoriality: `mapArgs` respects composition.
-}
mapArgs-∘ : {Ty₁ Ty₂ Ty₃ : Type ℓ} (cs : ConstrArity {ℓ})
            (f : Ty₁ → Ty₂) (g : Ty₂ → Ty₃) (args : Args cs Ty₁) →
            mapArgs cs g (mapArgs cs f args) ≡ mapArgs cs (g ∘ f) args
mapArgs-∘ Done         f g _            = refl
mapArgs-∘ (Nonrec A k) f g (a , args)   = Σ-≡-intro refl (mapArgs-∘ (k a) f g args)
mapArgs-∘ (Rec D cs)   f g (r , args)   = Σ-≡-intro refl (mapArgs-∘ cs f g args)

{-
    Definition 2.2
    The type of inductive hypotheses at one constructor's arguments,
    given a motive on `Ty`. Walks the arity and emits a Π for each Rec.
-}
IHs : (cs : ConstrArity {ℓ}) {Ty : Type ℓ} →
    (motive : Ty → Type ℓ) → Args cs Ty → Type ℓ
IHs Done         motive _            = ⊤
IHs (Nonrec A k) motive (a , args)   = IHs (k a) motive args
IHs (Rec D cs)   motive (r , args)   = ((d : D) → motive (r d)) × IHs cs motive args

{-
    Definition 2.2
    The type of case branches for an induction principle: one branch
    per operation, taking its args and IHs, producing a term in the
    motive at the constructed value.
-}
Cases : (sig : Signature {ℓ}) → (Ty : Type ℓ) →
    ConstrAlgebra sig Ty → (motive : Ty → Type ℓ) → Type ℓ
Cases sig Ty algebra motive =
    (c : Op sig) → (args : Args (arity sig c) Ty) →
        (ih : IHs (arity sig c) motive args) → motive (algebra c args)

{-
    Definition 2.2
    An induction principle on `Ty`: given a motive and one case per
    operation, produce a term in the motive at every point of `Ty`.
-}
Induction : {Ty : Type ℓ} → (sig : Signature {ℓ}) →
    (algebra : ConstrAlgebra sig Ty) → Type (lsuc ℓ)
Induction {Ty = Ty} sig algebra = (motive : Ty → Type _) →
    Cases sig Ty algebra motive → (a : Ty) → motive a

{-
    Definition 2.2
    Given an eliminator `(a : Ty) → motive a`, build the IH tuple at
    one constructor's args by applying the eliminator to every
    recursive child.
-}
mkIHs : (cs : ConstrArity {ℓ}) {Ty : Type ℓ} {motive : Ty → Type ℓ} →
    (elim : (a : Ty) → motive a) → (args : Args cs Ty) →
    IHs cs motive args
mkIHs Done         elim _          = tt
mkIHs (Nonrec A k) elim (a , args) = mkIHs (k a) elim args
mkIHs (Rec D cs)   elim (r , args) = ((λ d → elim (r d)) , mkIHs cs elim args)

{-
    Definition 2.2
    Propositional β: the induction principle reduces (up to a path) on
    each constructor to the corresponding case applied to the IH tuple
    built from the eliminator itself.
-}
BetaLaw : {Ty : Type ℓ} → (sig : Signature {ℓ}) → {algebra : ConstrAlgebra sig Ty} →
    (induction : Induction sig algebra) → Type (lsuc ℓ)
BetaLaw {Ty = Ty} sig {algebra} induction =
    (motive : Ty → Type _) → (cases : Cases sig Ty algebra motive) →
    (c : Op sig) → (args : Args (arity sig c) Ty) →
    induction motive cases (algebra c args)
        ≡ cases c args (mkIHs (arity sig c) (induction motive cases) args)

{-
    Derivation of η
    Propositional η: every term is propositionally a constructor
    applied to some arguments. Stated as a Σ-existential.
-}
EtaLaw : {Ty : Type ℓ} (sig : Signature {ℓ}) →
    {algebra : ConstrAlgebra sig Ty} → (induction : Induction sig algebra) → Type ℓ
EtaLaw {Ty = Ty} sig {algebra} induction = (x : Ty) →
    Σ (Op sig) (λ c → Σ (Args (arity sig c) Ty) (λ args → algebra c args ≡ x))

{-
    Reassemble args at a new carrier: keep the nonrec data from `args`,
    but at each Rec position install the new recursive function from
    `ih` (with constant motive, each is just `D → Ty₂`).

    `setRec` and `mkIHs` are mutually inverse repackagings: see
    `setRec-mkIHs` below.
-}
setRec : (cs : ConstrArity {ℓ}) {Ty₁ Ty₂ : Type ℓ} →
    (args : Args cs Ty₁) → IHs cs (λ _ → Ty₂) args →
    Args cs Ty₂
setRec Done         _          _          = tt
setRec (Nonrec A k) (a , args) ih         = (a , setRec (k a) args ih)
setRec (Rec D cs)   (r , args) (r' , ih)  = (r' , setRec cs args ih)

{-
    `setRec` after `mkIHs` is `mapArgs`: replacing each Rec child with
    `f` applied to the original child agrees with postcomposing `f`.
    Only propositional because both sides recurse structurally on `cs`.
-}
setRec-mkIHs : {Ty₁ Ty₂ : Type ℓ} (cs : ConstrArity {ℓ})
               (f : Ty₁ → Ty₂) (args : Args cs Ty₁) →
               setRec cs args (mkIHs cs f args) ≡ mapArgs cs f args
setRec-mkIHs Done         f _            = refl
setRec-mkIHs (Nonrec A k) f (a , args)   = Σ-≡-intro refl (setRec-mkIHs (k a) f args)
setRec-mkIHs (Rec D cs)   f (r , args)   = Σ-≡-intro refl (setRec-mkIHs cs f args)

{-
    Definition 2.2
    An inductive algebra for `sig` on the carrier `C`: a constructor
    function packaged with its induction principle and propositional
    β-rule. Derives `fold` to any other algebra together with its
    β-rule, and the η-rule.
-}
record IndAlg (sig : Signature {ℓ}) (C : Type ℓ) : Type (lsuc ℓ) where
  field
    algebra : ConstrAlgebra sig C
    ind     : Induction sig algebra
    beta    : BetaLaw sig ind

  {-
      Used in the proof of Proposition 2.3.
      Catamorphism: the unique algebra morphism out of `C` into any
      target algebra `algD`.
  -}
  fold : {D : Type ℓ} → ConstrAlgebra sig D → C → D
  fold algD =
      ind (λ _ → _) λ c argsC ih → algD c (setRec (arity sig c) argsC ih)

  {-
      β-rule for `fold`: folding through a constructor commutes with
      the target algebra after mapping the recursive children through
      `fold`.
  -}
  fold-β : {D : Type ℓ} (algD : ConstrAlgebra sig D)
           (c : Op sig) (argsC : Args (arity sig c) C) →
           fold algD (algebra c argsC)
             ≡ algD c (mapArgs (arity sig c) (fold algD) argsC)
  fold-β algD c argsC =
      beta (λ _ → _) (λ c' args' ih → algD c' (setRec (arity sig c') args' ih)) c argsC
      • ap (algD c) (setRec-mkIHs (arity sig c) (fold algD) argsC)

  {-
      Section 2 (Eta is redundant): the η data of prior work is
      derivable from the fields above, so `IndAlg` does not carry it.
      η-rule: every term is propositionally a constructor applied to
      some arguments, witnessed by induction.
  -}
  eta : EtaLaw sig ind
  eta = ind _ (λ c args _ → c , args , refl)

{-
    If `f : Ty → Ty` is pointwise the identity on the values actually
    appearing in `args` (as witnessed by an IH-shaped predicate), then
    mapping `f` is the identity on `args`.
-}
mapArgs-id-pw : {Ty : Type ℓ} (cs : ConstrArity {ℓ}) (f : Ty → Ty) →
                (args : Args cs Ty) → IHs cs (λ x → f x ≡ x) args →
                mapArgs cs f args ≡ args
mapArgs-id-pw Done         f _              _              = refl
mapArgs-id-pw (Nonrec A k) f (a , args)     ih             =
    Σ-≡-intro refl (mapArgs-id-pw (k a) f args ih)
mapArgs-id-pw (Rec D cs)   f (r , args)     (ih-h , ih-t)  =
    Σ-≡-intro (ext ih-h) (tptConst (ext ih-h) _ • mapArgs-id-pw cs f args ih-t)

{-
    Pointwise congruence for `mapArgs`: if two maps agree at every
    recursive child of `args` (as an IH-shaped predicate), the mapped
    argument tuples are equal.
-}
mapArgs-cong-pw : {Ty₁ Ty₂ : Type ℓ} (cs : ConstrArity {ℓ}) (f₁ f₂ : Ty₁ → Ty₂)
                  (args : Args cs Ty₁) → IHs cs (λ x → f₁ x ≡ f₂ x) args →
                  mapArgs cs f₁ args ≡ mapArgs cs f₂ args
mapArgs-cong-pw Done         f₁ f₂ _          _              = refl
mapArgs-cong-pw (Nonrec A k) f₁ f₂ (a , args) ih             =
    Σ-≡-intro refl (mapArgs-cong-pw (k a) f₁ f₂ args ih)
mapArgs-cong-pw (Rec D cs)   f₁ f₂ (r , args) (ih-h , ih-t)  =
    ap2 _,_ (ext ih-h) (mapArgs-cong-pw cs f₁ f₂ args ih-t)

{-
    `Args cs` is functorial in the carrier and preserves equivalences:
    an equivalence `A ≃ B` between two carriers lifts to an equivalence
    `Args cs A ≃ Args cs B`. The forward map is `mapArgs cs (f eqv)`
    (definitionally), so this packages the existing `mapArgs` together
    with its componentwise inverse and the round-trip witnesses.
-}
mapArgs-eqv : (cs : ConstrArity {ℓ}) {A B : Type ℓ} →
              A ≃ B → Args cs A ≃ Args cs B
mapArgs-eqv Done         _   = id-eqv
mapArgs-eqv (Nonrec T k) eqv = Σ-eqv-snd (λ t → mapArgs-eqv (k t) eqv)
mapArgs-eqv (Rec D cs)   eqv = ×-eqv (→-eqv-r eqv) (mapArgs-eqv cs eqv)

{-
    The forward map of `mapArgs-eqv` agrees with `mapArgs` of the
    forward map, propositionally. (They are definitionally equal on
    canonical arities, but `cs` is generally a neutral term in
    downstream use, so we expose this as a propositional bridge.)
-}
mapArgs-eqv-f : (cs : ConstrArity {ℓ}) {A B : Type ℓ} (eqv : A ≃ B) (args : Args cs A) →
                f (mapArgs-eqv cs eqv) args ≡ mapArgs cs (f eqv) args
mapArgs-eqv-f Done         eqv _            = refl
mapArgs-eqv-f (Nonrec T k) eqv (t , args)   = ap (λ x → (t , x)) (mapArgs-eqv-f (k t) eqv args)
mapArgs-eqv-f (Rec D cs)   eqv (r , args)   = ap (λ x → (f eqv ∘ r , x)) (mapArgs-eqv-f cs eqv args)

{-
    `mapArgs` with the identity function is the identity on `args`.
    Special case of `mapArgs-id-pw` with trivial (pointwise-`refl`)
    IHs; we state it as a top-level lemma since downstream callers
    do not have the IH-tuple at hand. (`id ∘ r ≡ r` definitionally
    via function η, so the Rec case is just `ap (r ,_) ih`.)
-}
mapArgs-id : {Ty : Type ℓ} (cs : ConstrArity {ℓ}) (args : Args cs Ty) →
             mapArgs cs (λ x → x) args ≡ args
mapArgs-id Done         _            = refl
mapArgs-id (Nonrec A k) (a , args)   = ap (λ x → (a , x)) (mapArgs-id (k a) args)
mapArgs-id (Rec D cs)   (r , args)   = ap (λ x → (r , x)) (mapArgs-id cs args)

{-
    Round-trip lemma: between any two `IndAlg`s on `C` and `D`, the
    composite of folds going `C → D → C` is the identity. The unique
    algebra endomorphism of an h-initial algebra is `id`, witnessed by
    induction on the carrier.
-}
fold-roundtrip : {sig : Signature {ℓ}} {C D : Type ℓ} →
                 (A : IndAlg sig C) (B : IndAlg sig D) →
                 (x : C) → IndAlg.fold B (IndAlg.algebra A)
                              (IndAlg.fold A (IndAlg.algebra B) x) ≡ x
fold-roundtrip {sig = sig} A B = indA (λ x → foldB algA (foldA algB x) ≡ x)
  λ c args ih →
      ap (foldB algA) (foldA-β algB c args)
    • foldB-β algA c (mapArgs (arity sig c) (foldA algB) args)
    • ap (algA c) (mapArgs-∘ (arity sig c) (foldA algB) (foldB algA) args
                 • mapArgs-id-pw (arity sig c) (foldB algA ∘ foldA algB) args ih)
  where
    open IndAlg A renaming (algebra to algA; ind to indA; fold to foldA; fold-β to foldA-β)
    open IndAlg B renaming (algebra to algB; fold to foldB; fold-β to foldB-β)

{-
    Uniqueness of the fold: any map commuting with the constructor
    algebras — an algebra homomorphism on the carriers — agrees
    pointwise with `fold`. Witnessed by induction on the carrier: at
    a constructor, the homomorphism square and `fold-β` rewrite both
    sides to the target algebra applied to argument tuples that agree
    on the recursive children by the inductive hypothesis.
-}
fold-unique : {sig : Signature {ℓ}} {C D : Type ℓ} (ialg : IndAlg sig C)
              (algD : ConstrAlgebra sig D) (h : C → D) →
              ((c : Op sig) (args : Args (arity sig c) C) →
                  h (IndAlg.algebra ialg c args)
                    ≡ algD c (mapArgs (arity sig c) h args)) →
              (x : C) → h x ≡ IndAlg.fold ialg algD x
fold-unique {sig = sig} ialg algD h hom =
    ind (λ x → h x ≡ fold algD x)
        (λ c args ih →
            hom c args
          • ap (algD c) (mapArgs-cong-pw (arity sig c) h (fold algD) args ih)
          • ! (fold-β algD c args))
  where open IndAlg ialg

{-
    Congruence for `mkIHs`: if two eliminators agree on every
    recursive child of `args`, they build equal IH tuples. Used to
    feed the inductive hypothesis into the β-rules when proving
    uniqueness of the eliminator.
-}
mkIHs-cong : {Ty : Type ℓ} {motive : Ty → Type ℓ} (cs : ConstrArity {ℓ})
             (e1 e2 : (a : Ty) → motive a) (args : Args cs Ty) →
             IHs cs (λ x → e1 x ≡ e2 x) args →
             mkIHs cs e1 args ≡ mkIHs cs e2 args
mkIHs-cong Done         e1 e2 _          _              = refl
mkIHs-cong (Nonrec A k) e1 e2 (a , args) ih             =
    mkIHs-cong (k a) e1 e2 args ih
mkIHs-cong (Rec D cs)   e1 e2 (r , args) (ih-h , ih-t)  =
    ap2 _,_ (ext ih-h) (mkIHs-cong cs e1 e2 args ih-t)

{-
    Uniqueness of the dependent eliminator. The `ind` of an
    h-initial algebra is the *only* eliminator satisfying a
    β-rule: any other induction principle `i'` for the same
    `algebra`, together with its own β-rule `b'`, agrees with
    `ind` pointwise.

    Proved by induction on the carrier: at a constructor the two
    β-rules rewrite both sides to the same case applied to IH
    tuples, which agree by the inductive hypothesis through
    `mkIHs-cong`. (The β-rules are only propositional, so this is
    a statement about the *values* of the eliminators — the
    accompanying coherence of the β-rules themselves is a strictly
    higher 2-cell, not implied by this lemma.)
-}
ind-unique : {sig : Signature {ℓ}} {C : Type ℓ} (ialg : IndAlg sig C)
             (i' : Induction sig (IndAlg.algebra ialg)) → BetaLaw sig i' →
             (motive : C → Type ℓ)
             (cases : Cases sig C (IndAlg.algebra ialg) motive) →
             (a : C) → IndAlg.ind ialg motive cases a ≡ i' motive cases a
ind-unique {sig = sig} ialg i' b' motive cases =
    IndAlg.ind ialg
      (λ a → IndAlg.ind ialg motive cases a ≡ i' motive cases a)
      (λ c args ih →
          IndAlg.beta ialg motive cases c args
        • ap (cases c args)
             (mkIHs-cong (arity sig c)
                         (IndAlg.ind ialg motive cases)
                         (i' motive cases) args ih)
        • ! (b' motive cases c args))
