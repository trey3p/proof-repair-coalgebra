{-# OPTIONS --without-K  --cubical-compatible #-}

open import common
open import inductive-repair.indspec

{-
    Uniqueness of inductive structure over a fixed algebra: for any
    signature, two `(ind, beta)` pairs on the same constructor
    algebra are equal (`indAlgStr-≡`) — the general-signature
    analogue of the Sojakova β-coherence 2-cell that
    `inductive-repair.bridge` proves for the W-type signature. The
    payoff is `indAlg-≡-intro`: two `IndAlg`s on one carrier are
    equal as soon as their algebras are.

    The `ind` components agree pointwise by `ind-unique`; the 2-cell
    for `beta` reduces (by J and a level-polymorphic `tpt-path`) to

        ! (ap L ip) • β₁ p • ap R ip  ≡  β₂ p

    where `L i = i m cs (alg c args)`, `R i = cs c args (mkIHs …)`,
    and `ip` is the triple-funext of `ind-unique`. `ap L ip` peels
    to `ind-unique`'s value at the constructor, whose own β-rule
    (`ec-β`) rewrites it to `β₁ • ap (cs c args) (mkIHs-cong …) • ! β₂`;
    `ap R ip` peels to the same middle factor via `mkIHs-ext`, and
    the composite collapses by path algebra.
-}
module inductive-repair.indalg-prop where
  open Signature

  private
    -- Level-polymorphic `tpt-path` (the source lives at `lsuc ℓ`,
    -- the target at `ℓ`).
    tpt-path-lvl : {l₁ l₂ : Level} {A : Type l₁} {B : Type l₂}
                   (L R : A → B) {a a' : A} (q : a ≡ a') (e : L a ≡ R a) →
                   tpt (λ x → L x ≡ R x) q e ≡ ! (ap L q) • e • ap R q
    tpt-path-lvl L R refl e = ! •unitr • ! •unitl

    -- `ap` of a (non-dependent) pairing splits into `ap2` of the
    -- components.
    ap-pair : {l₁ l₂ l₃ : Level} {X : Type l₁} {A : Type l₂} {B : Type l₃}
              (F : X → A) (G : X → B) {x y : X} (p : x ≡ y) →
              ap (λ z → (F z , G z)) p ≡ ap2 _,_ (ap F p) (ap G p)
    ap-pair F G refl = refl

    -- Dependent precomposition by `_∘ i` (same template as
    -- `common.precomp-ext`, dependent codomain).
    precomp-ext-dep :
        {l : Level} {A B : Type l} {P : B → Type l}
        {f g : (b : B) → P b}
        (i : A → B) (e : (b : B) → f b ≡ g b) →
        ap (λ k → λ a → k (i a)) (ext e)
          ≡ ext (λ a → e (i a))
    precomp-ext-dep {A = A} {B} {P} {f} {g} i e =
          extHapply (ap (λ k → λ a → k (i a)) (ext e))
        • ap ext (ext pw)
      where
        pw : (x : A) →
             happly (ap (λ k → λ a → k (i a)) (ext e)) x ≡ e (i x)
        pw x =
            happly-ap (ap (λ k → λ a → k (i a)) (ext e)) x
          • ! (ap-∘ {f = λ (h : (a : A) → P (i a)) → h x}
                    {g = λ k → λ a → k (i a)} (ext e))
          • ! (happly-ap (ext e) (i x))
          • happlyExt e (i x)

    -- `ap` of `mkIHs` on a funext cell is `mkIHs-cong` at the
    -- IH-shaped tuple of the pointwise paths. By induction on the
    -- arity.
    mkIHs-ext : {ℓ : Level} {C : Type ℓ} {m : C → Type ℓ}
                (ar : ConstrArity {ℓ})
                {e₁ e₂ : (a : C) → m a} (e : (a : C) → e₁ a ≡ e₂ a)
                (args : Args ar C) →
                ap (λ el → mkIHs ar el args) (ext e)
                  ≡ mkIHs-cong ar e₁ e₂ args (mkIHs ar e args)
    mkIHs-ext Done         e args       = ap-const (ext e)
    mkIHs-ext (Nonrec A k) e (a , args) = mkIHs-ext (k a) e args
    mkIHs-ext (Rec D ar)   e (r , args) =
        ap-pair (λ el d → el (r d)) (λ el → mkIHs ar el args) (ext e)
      • ap2-cong _,_ (precomp-ext-dep r e) (mkIHs-ext ar e args)

    -- Pointwise reduction of `tpt` across all four Π's of
    -- `BetaLaw` at once, by J.
    tpt-betalaw-pw :
        {ℓ : Level} {sig : Signature {ℓ}} {C : Type ℓ}
        {alg : ConstrAlgebra sig C}
        {ind₁ ind₂ : Induction sig alg}
        (ip : ind₁ ≡ ind₂)
        (β : BetaLaw sig ind₁)
        (m : C → Type ℓ) (cs : Cases sig C alg m)
        (c : Op sig) (args : Args (arity sig c) C) →
        tpt (λ i → BetaLaw sig i) ip β m cs c args
          ≡ tpt (λ i → i m cs (alg c args)
                       ≡ cs c args (mkIHs (arity sig c) (i m cs) args))
                ip (β m cs c args)
    tpt-betalaw-pw refl β m cs c args = refl

    -- The path-algebra discharge of the 2-cell. (Four base points:
    -- `q`'s source is a distinct point, so all three paths J away.)
    collapse : {l : Level} {A : Type l} {w x y z : A}
               (p : w ≡ x) (k : x ≡ y) (q : z ≡ y) →
               ! (p • k • ! q) • p • k ≡ q
    collapse refl refl refl = refl

  module _ {ℓ : Level} {sig : Signature {ℓ}} {C : Type ℓ}
           {alg : ConstrAlgebra sig C}
           (i₁ : Induction sig alg) (b₁ : BetaLaw sig i₁)
           (i₂ : Induction sig alg) (b₂ : BetaLaw sig i₂) where
    private
      ia₁ : IndAlg sig C
      ia₁ = record { algebra = alg ; ind = i₁ ; beta = b₁ }

      -- The pointwise agreement of the two eliminators, and its
      -- triple funext.
      ec : (m : C → Type ℓ) (cs : Cases sig C alg m) (a : C) →
           i₁ m cs a ≡ i₂ m cs a
      ec = λ m cs a → ind-unique ia₁ i₂ b₂ m cs a

      ip : i₁ ≡ i₂
      ip = ext (λ m → ext (λ cs → ext (λ a → ec m cs a)))

      -- The "L" and "R" sides of the β-cell.
      Lfn : (m : C → Type ℓ) (cs : Cases sig C alg m)
            (c : Op sig) (args : Args (arity sig c) C) →
            Induction sig alg → m (alg c args)
      Lfn m cs c args i = i m cs (alg c args)

      Rfn : (m : C → Type ℓ) (cs : Cases sig C alg m)
            (c : Op sig) (args : Args (arity sig c) C) →
            Induction sig alg → m (alg c args)
      Rfn m cs c args i = cs c args (mkIHs (arity sig c) (i m cs) args)

      -- `ap Lfn` on the triple funext collapses via three
      -- `happlyExt`s to `ec` at the constructor.
      apL-collapse : (m : C → Type ℓ) (cs : Cases sig C alg m)
                     (c : Op sig) (args : Args (arity sig c) C) →
                     ap (Lfn m cs c args) ip ≡ ec m cs (alg c args)
      apL-collapse m cs c args =
          ap-∘ {f = withCsAtArg} {g = atM} ip
        • ap (ap withCsAtArg)
             ( ! (happly-ap ip m)
             • happlyExt (λ m' → ext (λ cs' → ext (λ a' → ec m' cs' a'))) m)
        • ap-∘ {f = withAtArg} {g = atCs} e2
        • ap (ap withAtArg)
             ( ! (happly-ap e2 cs)
             • happlyExt (λ cs' → ext (λ a' → ec m cs' a')) cs)
        • ! (happly-ap e1 (alg c args))
        • happlyExt (λ a' → ec m cs a') (alg c args)
        where
          e2 = ext (λ cs' → ext (λ a' → ec m cs' a'))
          e1 = ext (λ a' → ec m cs a')
          atM = λ (i : Induction sig alg) → i m
          atCs = λ (k : Cases sig C alg m → (a : C) → m a) → k cs
          withCsAtArg = λ (y : Cases sig C alg m → (a : C) → m a) →
                          y cs (alg c args)
          withAtArg = λ (y : (a : C) → m a) → y (alg c args)

      -- `ap Rfn` collapses to `ap (cs c args)` of `mkIHs-cong`
      -- at the tuple of pointwise paths.
      apR-collapse : (m : C → Type ℓ) (cs : Cases sig C alg m)
                     (c : Op sig) (args : Args (arity sig c) C) →
                     ap (Rfn m cs c args) ip
                       ≡ ap (cs c args)
                            (mkIHs-cong (arity sig c) (i₁ m cs) (i₂ m cs) args
                                        (mkIHs (arity sig c) (ec m cs) args))
      apR-collapse m cs c args =
          ap-∘ {f = mkAtCs} {g = atM} ip
        • ap (ap mkAtCs)
             ( ! (happly-ap ip m)
             • happlyExt (λ m' → ext (λ cs' → ext (λ a' → ec m' cs' a'))) m)
        • ap-∘ {f = mkOnly} {g = atCs} e2
        • ap (ap mkOnly)
             ( ! (happly-ap e2 cs)
             • happlyExt (λ cs' → ext (λ a' → ec m cs' a')) cs)
        • ap-∘ {f = cs c args} {g = mkArgsAt} e1
        • ap (ap (cs c args)) (mkIHs-ext (arity sig c) (λ a' → ec m cs a') args)
        where
          e2 = ext (λ cs' → ext (λ a' → ec m cs' a'))
          e1 = ext (λ a' → ec m cs a')
          atM = λ (i : Induction sig alg) → i m
          atCs = λ (k : Cases sig C alg m → (a : C) → m a) → k cs
          mkArgsAt = λ (el : (a : C) → m a) → mkIHs (arity sig c) el args
          mkOnly = λ (el : (a : C) → m a) →
                     cs c args (mkIHs (arity sig c) el args)
          mkAtCs = λ (k : Cases sig C alg m → (a : C) → m a) →
                     cs c args (mkIHs (arity sig c) (k cs) args)

      -- The β-rule of `i₁` on the path motive used inside
      -- `ind-unique`: exposes `ec`'s value at a constructor.
      ec-β : (m : C → Type ℓ) (cs : Cases sig C alg m)
             (c : Op sig) (args : Args (arity sig c) C) →
             ec m cs (alg c args)
               ≡ b₁ m cs c args
               • ap (cs c args)
                    (mkIHs-cong (arity sig c) (i₁ m cs) (i₂ m cs) args
                                (mkIHs (arity sig c) (ec m cs) args))
               • ! (b₂ m cs c args)
      ec-β m cs c args = b₁ motive' cases' c args
        where
          motive' : C → Type ℓ
          motive' a = i₁ m cs a ≡ i₂ m cs a
          cases' : Cases sig C alg motive'
          cases' c' args' ih =
              b₁ m cs c' args'
            • ap (cs c' args')
                 (mkIHs-cong (arity sig c') (i₁ m cs) (i₂ m cs) args' ih)
            • ! (b₂ m cs c' args')

      core : (m : C → Type ℓ) (cs : Cases sig C alg m)
             (c : Op sig) (args : Args (arity sig c) C) →
             ! (ap (Lfn m cs c args) ip)
               • b₁ m cs c args
               • ap (Rfn m cs c args) ip
               ≡ b₂ m cs c args
      core m cs c args =
          ap (λ z → ! z • b₁ m cs c args • ap (Rfn m cs c args) ip)
             (apL-collapse m cs c args)
        • ap (λ z → ! (ec m cs (alg c args)) • b₁ m cs c args • z)
             (apR-collapse m cs c args)
        • ap (λ z → ! z • b₁ m cs c args • K)
             (ec-β m cs c args)
        • collapse (b₁ m cs c args) K (b₂ m cs c args)
        where
          K = ap (cs c args)
                 (mkIHs-cong (arity sig c) (i₁ m cs) (i₂ m cs) args
                             (mkIHs (arity sig c) (ec m cs) args))

      indbeta-pw : (m : C → Type ℓ) (cs : Cases sig C alg m)
                   (c : Op sig) (args : Args (arity sig c) C) →
                   tpt (λ i → BetaLaw sig i) ip b₁ m cs c args
                     ≡ b₂ m cs c args
      indbeta-pw m cs c args =
          tpt-betalaw-pw ip b₁ m cs c args
        • tpt-path-lvl (Lfn m cs c args) (Rfn m cs c args) ip (b₁ m cs c args)
        • core m cs c args

      indbeta : tpt (λ i → BetaLaw sig i) ip b₁ ≡ b₂
      indbeta = ext (λ m → ext (λ cs → ext (λ c →
                  ext (λ args → indbeta-pw m cs c args))))

    indAlgStr-≡ : _≡_ {X = Σ (Induction sig alg) (λ i → BetaLaw sig i)}
                      (i₁ , b₁) (i₂ , b₂)
    indAlgStr-≡ = Σ-≡-intro ip indbeta

  private
    mkIndAlg : {ℓ : Level} {sig : Signature {ℓ}} {C : Type ℓ}
               (alg : ConstrAlgebra sig C) →
               Σ (Induction sig alg) (λ i → BetaLaw sig i) → IndAlg sig C
    mkIndAlg alg s = record { algebra = alg ; ind = fst s ; beta = snd s }

    indAlg-≡-helper : {ℓ : Level} {sig : Signature {ℓ}} {C : Type ℓ}
                      (alg₁ alg₂ : ConstrAlgebra sig C) (pa : alg₁ ≡ alg₂)
                      (s₁ : Σ (Induction sig alg₁) (λ i → BetaLaw sig i))
                      (s₂ : Σ (Induction sig alg₂) (λ i → BetaLaw sig i)) →
                      mkIndAlg alg₁ s₁ ≡ mkIndAlg alg₂ s₂
    indAlg-≡-helper alg .alg refl s₁ s₂ =
        ap (mkIndAlg alg) (indAlgStr-≡ (fst s₁) (snd s₁) (fst s₂) (snd s₂))

  {-
      Two `IndAlg`s on the same carrier are equal as soon as their
      algebras are — the inductive structure over a fixed algebra
      is unique.
  -}
  indAlg-≡-intro : {ℓ : Level} {sig : Signature {ℓ}} {C : Type ℓ}
                   (x y : IndAlg sig C) →
                   IndAlg.algebra x ≡ IndAlg.algebra y → x ≡ y
  indAlg-≡-intro x y pa =
      indAlg-≡-helper (IndAlg.algebra x) (IndAlg.algebra y) pa
        (IndAlg.ind x , IndAlg.beta x) (IndAlg.ind y , IndAlg.beta y)
