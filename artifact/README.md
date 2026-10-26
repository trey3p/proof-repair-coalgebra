# Artifact: Proof Repair and (Co)algebra Equivalences

This artifact is the Agda formalization accompanying the paper. Every
numbered definition, example, proposition, lemma, and theorem in the
paper is mapped below to the Agda declaration that formalizes it, with
its file and line number. Formalization claims made in the prose (outside
numbered environments) are listed as well. The same references are the
blue checkmarks in the paper, which link to rendered HTML at
<https://prt-ema.pages.dev/agda/>.

In the Agda sources, each declaration listed in the tables carries a
comment directly above it naming the paper item, e.g.
`-- Theorem 3.11 (W-type Configurations are Unique Algebra Equivalences)`.

The artifact is released under the BSD 3-Clause license (see `LICENSE`).

## Contents

1. [Getting started](#getting-started)
2. [Axioms and trusted base](#axioms-and-trusted-base)
3. [Layout](#layout)
4. [Checking a claim](#checking-a-claim)
5. [Section 1: Introduction](#section-1-introduction)
6. [Section 2: Configurations](#section-2-proof-repair-via-configurations)
7. [Section 3: Inductive types and initial algebras](#section-3-algebraic-foundations-for-proof-repair)
8. [Section 4: Coinductive types and final coalgebras](#section-4-coinductive-types-and-final-coalgebras)
9. [What is not formalized, and other notes](#what-is-not-formalized-and-other-notes)
10. [Names in the paper's listings vs. Agda names](#names-in-the-papers-listings-vs-agda-names)

## Getting started

**Requirements.** Agda **2.7.0.1**.

### Installing Agda

Installing Agda 2.7.0.1 is all that is needed.

The quickest route is the **pre-built Agda 2.7.0.1 release** from
GitHub (described under Option 1 https://agda.readthedocs.io/en/latest/getting-started/installation.html), available for Windows (x86-64), macOS (Apple Silicon) and Linux
(x86-64). There is no pre-built 2.7.0.1 for Intel Macs or arm64 Linux; on
those, [build from source](#building-from-source-macos-and-linux) instead.

Each block below downloads and unpacks Agda into the current directory
and makes it available **in the current terminal**. The 2.7.0.1 binaries
need two settings: `bin/` on the `PATH`, and the environment variable
`Agda_datadir` pointing at the unpacked `data/` directory (without it,
`agda` stops with "The lib directory ... does not exist").

#### Pre-built binary: macOS (Apple Silicon)

```
curl -LO https://github.com/agda/agda/releases/download/v2.7.0.1/Agda-v2.7.0.1-macOS.tar.xz
tar xJf Agda-v2.7.0.1-macOS.tar.xz
chmod -R u+w Agda-v2.7.0.1/lib
xattr -rc Agda-v2.7.0.1/bin Agda-v2.7.0.1/lib
export PATH="$PWD/Agda-v2.7.0.1/bin:$PATH"
export Agda_datadir="$PWD/Agda-v2.7.0.1/data"
agda --version
```

The `xattr -rc` line removes macOS's download quarantine. The binary is
not notarized, so if the archive was downloaded with a web browser, macOS
otherwise refuses to run it.

#### Pre-built binary: Linux (x86-64)

```
curl -LO https://github.com/agda/agda/releases/download/v2.7.0.1/Agda-v2.7.0.1-linux.tar.xz
tar xJf Agda-v2.7.0.1-linux.tar.xz
export PATH="$PWD/Agda-v2.7.0.1/bin:$PATH"
export Agda_datadir="$PWD/Agda-v2.7.0.1/data"
agda --version
```

The binary is statically linked and needs no other libraries
(`xz-utils` is needed to unpack the archive).

#### Pre-built binary: Windows (x86-64)

In PowerShell:

```
Invoke-WebRequest https://github.com/agda/agda/releases/download/v2.7.0.1/Agda-v2.7.0.1-win64.zip -OutFile Agda-v2.7.0.1-win64.zip
Expand-Archive Agda-v2.7.0.1-win64.zip -DestinationPath .
$env:Path = "$PWD\Agda-v2.7.0.1\bin;$env:Path"
$env:Agda_datadir = "$PWD\Agda-v2.7.0.1\data"
chcp 65001
agda --version
```

`chcp 65001` switches the console to UTF-8, since Agda's messages contain
Unicode (`≃`, `Σ`, `ℓ`, …); run it in every new PowerShell window.

Each block should end by printing `Agda version 2.7.0.1` (on macOS and
Windows followed by a commit hash and build flags).

**In a new terminal**, the two settings are gone. Either repeat the two
`export` (or `$env:`) lines, using the absolute path of the unpacked
`Agda-v2.7.0.1` directory, or add them to your shell profile
(`~/.zshrc`, `~/.bashrc`, or your PowerShell `$PROFILE`).

#### Building from source: macOS and Linux

Use this if no pre-built binary fits your machine (Intel Macs, arm64
Linux), or if the binary does not run. It compiles Agda, which takes
roughly 10–30 minutes. We tested these steps, exactly as written, on
macOS 15 (Apple Silicon) and on clean Ubuntu 24.04 (x86-64 and arm64).

1. **Install GHC and cabal** with [GHCup](https://www.haskell.org/ghcup/):

   ```
   curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
   source ~/.ghcup/env
   ghcup install ghc 9.6.7
   ghcup set ghc 9.6.7
   ghcup install cabal 3.12.1.0
   ghcup set cabal 3.12.1.0
   ```

   On Linux, GHC needs a few system libraries first (on Debian/Ubuntu:
   `sudo apt install build-essential curl libffi-dev libgmp-dev
   libncurses-dev zlib1g-dev`). On macOS you need the Xcode command-line
   tools (`xcode-select --install`).

2. **Build and install Agda 2.7.0.1** from Hackage. This compiles Agda
   from source:

   ```
   cabal update
   cabal install Agda-2.7.0.1
   ```

   The `agda` executable is installed into `~/.cabal/bin`, which
   `source ~/.ghcup/env` (step 1) puts on your `PATH`. In a new terminal,
   run `source ~/.ghcup/env` again (or accept the installer's offer to add
   it to your shell profile).

3. **Check the installation:**

   ```
   agda --version
   ```

   should print `Agda version 2.7.0.1`.

#### Building from source: Windows

These steps use GHCup's Windows installer from PowerShell. We tested them
on a clean GitHub Actions `windows-latest` runner (Windows Server).

1. **Install GHCup.** Open PowerShell as a normal user (not as
   Administrator) and run the installer command given on the
   [GHCup install page](https://www.haskell.org/ghcup/install/):

   ```
   Set-ExecutionPolicy Bypass -Scope Process -Force;[System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; try { & ([ScriptBlock]::Create((Invoke-WebRequest https://www.haskell.org/ghcup/sh/bootstrap-haskell.ps1 -UseBasicParsing))) -Interactive -DisableCurl } catch { Write-Error $_ }
   ```

   Accept the defaults. This installs GHCup (by default under `C:\ghcup`)
   together with an MSYS2 environment that GHC and cabal use to compile C
   code, and adds the necessary directories to your user `PATH`. When it
   finishes, **close PowerShell and open a new window** so the new `PATH`
   takes effect.

2. **Install GHC and cabal** (in the new PowerShell window):

   ```
   ghcup install ghc 9.6.7
   ghcup set ghc 9.6.7
   ghcup install cabal 3.12.1.0
   ghcup set cabal 3.12.1.0
   ```

3. **Build and install Agda 2.7.0.1:**

   ```
   cabal update
   cabal install Agda-2.7.0.1
   ```

   With GHCup's defaults, `agda.exe` is installed into `C:\cabal\bin`,
   which the GHCup installer already put on your `PATH`. Open a new
   PowerShell window and run `agda --version`; it should print
   `Agda version 2.7.0.1`. If the command is not found, add the directory
   named in the last lines of the `cabal install` output to your user
   `PATH` (Start → "Edit environment variables for your account" →
   `Path` → New), then open a new window.

4. **Use a UTF-8 console.** Agda's messages for this artifact contain
   Unicode (`≃`, `Σ`, `ℓ`, …). Windows consoles often default to a legacy
   code page, in which GHC programs can fail when printing such
   characters, with an error like `hPutChar: invalid argument`. As a
   precaution, switch the console to UTF-8 before running Agda:

   ```
   chcp 65001
   ```

Then type-check the artifact as below (`agda everything.agda` from inside
this directory works the same in PowerShell).

If the Agda build fails with errors about file paths being too long,
enable long path support in Windows (search for "Enable Win32 long
paths" / the `LongPathsEnabled` registry setting) and run the
`cabal install` command again.

#### Notes for all platforms

Pre-built packages (Homebrew, apt, Nix) are also fine **if** they provide
exactly version 2.7.0.1; check with `agda --version`. Distribution
packages are often a different version.

An existing `~/.agda/libraries` or `~/.agda/defaults` (for example one
registering the standard library) does no harm: `prt-artifact.agda-lib`
declares no dependencies.

### Evaluating/Type-checking the artifact

**Type-check everything.** From inside this directory:

```
agda everything.agda
```

`everything.agda` imports every module. A clean check (no `_build/`
cache) took about 20 seconds on our machine and finishes with no errors
and no warnings. Run it from inside this directory, so that
`prt-artifact.agda-lib` is the library file in scope.

**Browse.** To regenerate the HTML rendering locally:

```
agda --html --html-dir=html everything.agda
```

then open `html/everything.html`.

## Axioms and trusted base

* **Inductive development** (`common.agda`, `palg.agda`,
  `inductive-repair/`). Checked with `--without-K --cubical-compatible`,
  i.e. intensional Martin-Löf type theory with no K and no univalence. Its
  only postulates are function extensionality and its two coherence
  rules, the computation rule on `happly` and the uniqueness rule, in
  [common.agda:186-191](common.agda#L186).
  These are the axioms named in the paper's "Type Theory, Notation, and
  Conventions" paragraph (Section 1) and in Section 3.4 ("Repair without
  Univalence").
* **Coinductive development** (`coinductive-repair/`). Every file is
  checked with `--cubical --guardedness --safe`.
* There are no `TERMINATING`, `NO_POSITIVITY_CHECK`, `REWRITE`, or other
  unsafe pragmas anywhere.
* The two example files `inductive-repair/examples/{nat,finvec}.agda`
  pass `-WnoUnsupportedIndexedMatch`, which only silences a warning
  about cubical-compatible matching on `Fin`/`Vec` indices.

### Soundness checks

Run these from inside this directory. The expected output is shown
below each command.

1. **Everything type-checks.** `agda everything.agda` (see
   [Evaluating/Type-checking the artifact](#evaluatingtype-checking-the-artifact))
   finishes with exit code 0. This also rules out unfinished proofs:
   Agda refuses to import a module that still contains an open hole
   (`{! !}` or `?`) or an unsolved metavariable.

2. **The only postulates are the three funext axioms.**

   ```
   grep -rnw 'postulate' --include='*.agda' .
   ```

   ```
   ./common.agda:186:postulate
   ./coinductive-repair/coherence.agda:324:            postulate — the head-cell wall and the
   ```

   (The two lines may appear in either order.) The first is the block declaring `ext`, `happlyExt` and
   `extHapply` ([common.agda:186-191](common.agda#L186)); the second is
   inside a comment (`{- … -}`), not a declaration.

3. **No unsafe pragmas or options** (termination/positivity checking
   switched off, rewrite rules, `--type-in-type`, unsolved metas
   allowed, …). This prints nothing:

   ```
   grep -rnE 'TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|POLARITY|INJECTIVE|REWRITE|type-in-type|allow-unsolved-metas|allow-incomplete-matches|no-termination-check|no-positivity-check|rewriting|omega-in-omega' --include='*.agda' .
   ```

4. **No open holes.** This prints nothing:

   ```
   grep -rn '{!' --include='*.agda' .
   ```

5. **The coinductive development is `--safe`.** Agda's `--safe` flag
   itself rejects postulates and unsafe pragmas, so these eight files are
   checked by Agda, not only by `grep`:

   ```
   grep -rlE 'OPTIONS.*--safe' --include='*.agda' .
   ```

   lists all eight files in `coinductive-repair/` (including
   `examples/stream.agda`). The inductive files cannot use `--safe`
   because they import the funext postulates from `common.agda`.

On Windows (PowerShell), the same checks can be run with `Select-String`
(we have not tested these PowerShell versions):

```
Get-ChildItem -Recurse -Filter *.agda | Select-String -Pattern '\bpostulate\b'
Get-ChildItem -Recurse -Filter *.agda | Select-String -Pattern 'TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|POLARITY|INJECTIVE|REWRITE|type-in-type|allow-unsolved-metas|allow-incomplete-matches|no-termination-check|no-positivity-check|rewriting|omega-in-omega'
Get-ChildItem -Recurse -Filter *.agda | Select-String -SimpleMatch '{!'
Get-ChildItem -Recurse -Filter *.agda | Select-String -Pattern 'OPTIONS.*--safe' -List
```

## Layout

| Path | Contents |
|------|----------|
| `LICENSE` | BSD 3-Clause license. |
| `everything.agda` | Imports every module; the type-checking entry point. |
| `common.agda` | Base types, path algebra, transport lemmas, funext postulates, bi-invertible equivalences `_≃_`. |
| `palg.agda` | Polynomial functors, P-algebras, homomorphisms, algebra equivalences, homotopy-initiality (§3.1). |
| `inductive-repair/indspec.agda` | Constructor arities, signatures, constructor algebras, induction principles, `IndAlg` (§2). |
| `inductive-repair/config.agda` | Configurations and Proposition 2.3. |
| `inductive-repair/coherence.agda` | PUMPKIN Pi correctness conditions (Proposition 2.4). |
| `inductive-repair/indalg-prop.agda` | Uniqueness of the induction structure on a fixed algebra (used by `config.agda`). |
| `inductive-repair/repair-ops.agda` | `repair-Π`: transferring a theorem across a configuration. |
| `inductive-repair/wtype-config.agda` | W-type configurations (Definition 3.9, Lemma 3.10). |
| `inductive-repair/palg-config.agda` | Algebra configurations, `foldSwap` (Definition 3.13, Proposition 3.15). |
| `inductive-repair/palg-coherence.agda` | Correctness conditions derived from initiality alone (§3.3). |
| `inductive-repair/bridge.agda` | Carrier-level bridge `WTypeIndAlg A B C ≃ InitAlgOn A B C` (Awodey–Gambino–Sojakova). |
| `inductive-repair/alg-iso.agda` | Algebra-equivalence lemmas, uniqueness of repair. |
| `inductive-repair/conversion.agda` | Proposition 3.14. |
| `inductive-repair/config-alg-equiv.agda` | Theorem 3.11. |
| `inductive-repair/examples/nat.agda` | Running example `Nat`/`Bin` (Introduction, Examples 3.3, 3.5, 3.8, 3.12). |
| `inductive-repair/examples/finvec.agda` | `Vec A n` vs. `Fin n → A` case study (§2). |
| `coinductive-repair/cubical-common.agda` | Cubical basics: paths, h-levels, `_≃_`, `_↔_`. |
| `coinductive-repair/mtype.agda` | The coinductive record `M A B` and its corecursor. |
| `coinductive-repair/coalg.agda` | Coalgebras, finality, bisimulation, M-rules, Theorem 4.21 (§4.1, §4.3–4.4). |
| `coinductive-repair/config.agda` | Destructor algebras, coinductive configurations, derived (2-D) coinduction (§4.3). |
| `coinductive-repair/coherence.agda` | Coinductive correctness conditions (Proposition 4.19). |
| `coinductive-repair/mtype-config.agda` | M-type configurations (Lemma 4.23). |
| `coinductive-repair/coconfig-coalg-equiv.agda` | Coalgebra configurations, coalgebra equivalences, Theorem 4.24. |
| `coinductive-repair/examples/stream.agda` | Running example `Stream`/`Stream'` (Examples 4.2–4.20). |

In the tables below, paths are relative to this directory and line
numbers point at the line holding the declaration's name.

## Checking a claim

The tables in the next four sections list, for each claim in the paper,
the Agda declaration that formalizes it. To check a claim:

1. Type-check the artifact as described in
   [Evaluating/Type-checking the artifact](#evaluatingtype-checking-the-artifact).
   A successful run means every declaration below is proven: Agda
   rejects any module with an unfinished proof (an open `{! !}` hole or
   unsolved metavariable), and the only assumptions are those listed in
   [Axioms and trusted base](#axioms-and-trusted-base).
2. Open the listed `file:line` (or follow the link) and compare the
   declaration's type with the statement in the paper. The comment
   directly above it names the paper item, e.g. `-- Theorem 3.11 (...)`.
   Where the Agda statement differs in form from the paper, the table
   says how (for example, heterogeneous equality in Proposition 2.4, or
   the Agda name of an object written differently in the paper).

## Section 1: Introduction

| Paper | Agda | Location |
|-------|------|----------|
| Motivating example `Nat`/`Bin` | module `inductive-repair.examples.nat` | [inductive-repair/examples/nat.agda](inductive-repair/examples/nat.agda) |
| | `Bin` (with `Pos`) | [inductive-repair/examples/nat.agda:64](inductive-repair/examples/nat.agda#L64) |
| | `isZeroN`, `isZeroB` (pattern-matching versions) | [inductive-repair/examples/nat.agda:467](inductive-repair/examples/nat.agda#L467), [:471](inductive-repair/examples/nat.agda#L471) |
| | `zUnit` (named `zero-is-unit`) | [inductive-repair/examples/nat.agda:496](inductive-repair/examples/nat.agda#L496) |
| | `zUnitB-nat b = zUnit (toNat b)` (named `zero-is-unit-Bin`, via `repair-Π`) | [inductive-repair/examples/nat.agda:503](inductive-repair/examples/nat.agda#L503), [inductive-repair/repair-ops.agda:22](inductive-repair/repair-ops.agda#L22) |
| Conventions: only axioms are funext + its two rules | see [Axioms](#axioms-and-trusted-base) | [common.agda:186](common.agda#L186) |

## Section 2: Proof Repair via Configurations

| Paper | Agda | Location |
|-------|------|----------|
| **Definition 2.1** (Constructor Algebra) | `ConstrArity` (`Done`/`Nonrec`/`Rec`) | [inductive-repair/indspec.agda:30](inductive-repair/indspec.agda#L30) |
| | `Signature` (record with `Op`, `arity`) | [inductive-repair/indspec.agda:40](inductive-repair/indspec.agda#L40) |
| | `Args` | [inductive-repair/indspec.agda:52](inductive-repair/indspec.agda#L52) |
| | `ConstrAlgebra` | [inductive-repair/indspec.agda:62](inductive-repair/indspec.agda#L62) |
| `mapArgs` and its functoriality (text after Def. 2.1) | `mapArgs` | [inductive-repair/indspec.agda:69](inductive-repair/indspec.agda#L69) |
| | preserves composition: `mapArgs-∘` | [inductive-repair/indspec.agda:78](inductive-repair/indspec.agda#L78) |
| | preserves identities: `mapArgs-id` | [inductive-repair/indspec.agda:286](inductive-repair/indspec.agda#L286) |
| | carries `X ≃ Y` to `Args cs X ≃ Args cs Y`: `mapArgs-eqv` | [inductive-repair/indspec.agda:261](inductive-repair/indspec.agda#L261) |
| **Definition 2.2** (Configuration) | `IH` (named `IHs`) | [inductive-repair/indspec.agda:90](inductive-repair/indspec.agda#L90) |
| | cases of an eliminator: `Cases` | [inductive-repair/indspec.agda:102](inductive-repair/indspec.agda#L102) |
| | `Ind` (named `Induction`) | [inductive-repair/indspec.agda:113](inductive-repair/indspec.agda#L113) |
| | canonical IHs `ih̄`: `mkIHs` | [inductive-repair/indspec.agda:124](inductive-repair/indspec.agda#L124) |
| | β law (named `BetaLaw`) | [inductive-repair/indspec.agda:137](inductive-repair/indspec.agda#L137) |
| | `IndAlg` (fields `algebra`, `ind`, `beta`) | [inductive-repair/indspec.agda:189](inductive-repair/indspec.agda#L189) |
| | `Config` (fields `indAlgC`, `indAlgD`) | [inductive-repair/config.agda:28](inductive-repair/config.agda#L28) |
| **Proposition 2.3** (Configurations and Inductive Equivalences are Equivalent) | `configEquiv : (IndAlg sig C × (C ≃ D)) ≃ Config sig C D` | [inductive-repair/config.agda:336](inductive-repair/config.agda#L336) |
| | the two maps: `equivToConfig`, `configToEquiv` | [inductive-repair/config.agda:203](inductive-repair/config.agda#L203), [:214](inductive-repair/config.agda#L214) |
| | proof sketch: `fold`, its β rule `fold-β`, uniqueness `fold-unique` | [inductive-repair/indspec.agda:200](inductive-repair/indspec.agda#L200), [:209](inductive-repair/indspec.agda#L209), [:320](inductive-repair/indspec.agda#L320) |
| **Proposition 2.4** (Correctness Conditions) | module `Coherence cfg` | [inductive-repair/coherence.agda:27](inductive-repair/coherence.agda#L27) |
| | (1) `constr_ok`: `constr-ok` (the heterogeneous form noted in the paper) | [inductive-repair/coherence.agda:44](inductive-repair/coherence.agda#L44) |
| | (2) `iota_ok`: `beta-ok-C`, `beta-ok-D` | [inductive-repair/coherence.agda:57](inductive-repair/coherence.agda#L57), [:60](inductive-repair/coherence.agda#L60) |
| | (3) `elim_ok`: `elim-ok`; the transported cases `φ* cs_D` are `deriveCasesC` | [inductive-repair/coherence.agda:93](inductive-repair/coherence.agda#L93), [:80](inductive-repair/coherence.agda#L80) |
| `Eta` data of prior work is redundant (footnote; conjecture of Viola et al.) | `IndAlg.eta` derives `EtaLaw` from the other fields | [inductive-repair/indspec.agda:223](inductive-repair/indspec.agda#L223), [:150](inductive-repair/indspec.agda#L150) |
| `Vec A n` vs. `Fin n → A` case study, repaired index by index | `finVecConfig : (n : ℕ) → Config (sig n) (Vec A n) (FinSet n A)` | [inductive-repair/examples/finvec.agda:156](inductive-repair/examples/finvec.agda#L156) |
| | correctness conditions at each `n`: `CoherenceFV` | [inductive-repair/examples/finvec.agda:226](inductive-repair/examples/finvec.agda#L226) |

## Section 3: Algebraic Foundations for Proof Repair

| Paper | Agda | Location |
|-------|------|----------|
| **Definition 3.1** (Polynomial Endofunctor) | `P` | [palg.agda:17](palg.agda#L17) |
| | `P-map`, functor laws `P-∘`, `P-id` | [palg.agda:22](palg.agda#L22), [:28](palg.agda#L28), [:37](palg.agda#L37) |
| **Definition 3.2** (P-algebra) | `P-Alg` | [palg.agda:70](palg.agda#L70) |
| **Example 3.3** (Nat Algebra) | `1 + X` is the polynomial `(Bool, PolyB)` | [inductive-repair/examples/nat.agda:160](inductive-repair/examples/nat.agda#L160) |
| | `Nat` algebra: `supℕ` (W-type form) / `pointEndo zero succ` | [inductive-repair/examples/nat.agda:168](inductive-repair/examples/nat.agda#L168), [:287](inductive-repair/examples/nat.agda#L287) |
| | `Bin` algebra `[bzero, binSucc]`: `supBin` | [inductive-repair/examples/nat.agda:203](inductive-repair/examples/nat.agda#L203) |
| **Definition 3.4** (Algebra Homomorphism) | `isAlgHom` | [palg.agda:85](palg.agda#L85) |
| | `AlgHom` | [palg.agda:96](palg.agda#L96) |
| | composition `AlgHom-∘`, identity `id-hom` | [palg.agda:103](palg.agda#L103), [:148](palg.agda#L148) |
| **Example 3.5** (Nat Homomorphism) | `fromNat-hom` | [inductive-repair/examples/nat.agda:317](inductive-repair/examples/nat.agda#L317) |
| **Definition 3.6** (Algebra Equivalence) | `isAlgEquiv` | [palg.agda:157](palg.agda#L157) |
| | `AlgEquiv` | [palg.agda:166](palg.agda#L166) |
| | "the carrier maps form a type equivalence": `algEquivToTypeEquiv` | [inductive-repair/config-alg-equiv.agda:40](inductive-repair/config-alg-equiv.agda#L40) |
| **Definition 3.7** (Homotopy-initial Algebra) | `isInitAlg` | [palg.agda:123](palg.agda#L123) |
| **Example 3.8** (Motivating Example with Initial Algebras) | `NatInit`: `ℕ-InitAlgOn` | [inductive-repair/examples/nat.agda:196](inductive-repair/examples/nat.agda#L196) |
| | `BinInit`: `Bin-InitAlgOn`, `Bin-InitAlg` | [inductive-repair/examples/nat.agda:223](inductive-repair/examples/nat.agda#L223), [:232](inductive-repair/examples/nat.agda#L232) |
| | `recNat`, `recNat-zero`, `recNat-succ` | [inductive-repair/examples/nat.agda:292](inductive-repair/examples/nat.agda#L292), [:297](inductive-repair/examples/nat.agda#L297), [:303](inductive-repair/examples/nat.agda#L303) |
| | `indNat` (named `indNatIndAlg`), `indNat-zero`, `indNat-succ` | [inductive-repair/examples/nat.agda:335](inductive-repair/examples/nat.agda#L335), [:340](inductive-repair/examples/nat.agda#L340), [:346](inductive-repair/examples/nat.agda#L346) |
| | `isZeroN` (named `isZeroNAlg`), `+` (named `_+N_`), `zUnit` (named `zero-is-unitAlg`) | [inductive-repair/examples/nat.agda:354](inductive-repair/examples/nat.agda#L354), [:357](inductive-repair/examples/nat.agda#L357), [:362](inductive-repair/examples/nat.agda#L362) |
| | repaired: `recBin`, `recBin-zero`, `recBin-succ` | [inductive-repair/examples/nat.agda:404](inductive-repair/examples/nat.agda#L404), [:407](inductive-repair/examples/nat.agda#L407), [:413](inductive-repair/examples/nat.agda#L413) |
| | repaired: `indBin`, `isZeroB` (named `isZeroBinAlg`), `zUnitB` | [inductive-repair/examples/nat.agda:419](inductive-repair/examples/nat.agda#L419), [:428](inductive-repair/examples/nat.agda#L428), [:434](inductive-repair/examples/nat.agda#L434) |
| **Definition 3.9** (W-type Configurations) | `WTypeArity` | [inductive-repair/wtype-config.agda:20](inductive-repair/wtype-config.agda#L20) |
| | `WTypeSignature`, `WTypeIndAlg` | [inductive-repair/wtype-config.agda:23](inductive-repair/wtype-config.agda#L23), [:27](inductive-repair/wtype-config.agda#L27) |
| | `WTypeConfig` | [inductive-repair/wtype-config.agda:31](inductive-repair/wtype-config.agda#L31) |
| **Lemma 3.10** (Configurations Faithfully Embed into W-type Configurations) | the polynomial: `A`, `B` (using `recPos`) | [inductive-repair/wtype-config.agda:277](inductive-repair/wtype-config.agda#L277), [:280](inductive-repair/wtype-config.agda#L280), [:44](inductive-repair/wtype-config.agda#L44) |
| | the embedding `Config sig C D → Σ A Σ B WTypeConfig A B C D`: `allConfigWTypeConfig` | [inductive-repair/wtype-config.agda:421](inductive-repair/wtype-config.agda#L421) |
| | faithfulness `φ_W = φ`, `ψ_W = ψ`: `wtypeConfigEquivAgree-f`, `wtypeConfigEquivAgree-g` | [inductive-repair/wtype-config.agda:433](inductive-repair/wtype-config.agda#L433), [:438](inductive-repair/wtype-config.agda#L438) |
| **Theorem 3.11** (W-type Configurations are Unique Algebra Equivalences) | `wtypeConfigEqv : WTypeConfig A B C D ≃ AlgInitEquiv A B C D` | [inductive-repair/config-alg-equiv.agda:260](inductive-repair/config-alg-equiv.agda#L260) |
| | right-hand side `Σ σ_C Σ σ_D (AlgEquiv … × isInitAlg …)`: `AlgInitEquiv` | [inductive-repair/config-alg-equiv.agda:115](inductive-repair/config-alg-equiv.agda#L115) |
| | proof sketch: carrier-level bridge `bridgeEqv`; pairs of initial algebras vs. one initial algebra plus an iso, `fullAlgIso` | [inductive-repair/bridge.agda:476](inductive-repair/bridge.agda#L476), [inductive-repair/config-alg-equiv.agda:166](inductive-repair/config-alg-equiv.agda#L166) |
| | uniqueness: `isContr-AlgEquiv` (via `isProp-AlgEquiv`) | [inductive-repair/alg-iso.agda:304](inductive-repair/alg-iso.agda#L304), [:258](inductive-repair/alg-iso.agda#L258) |
| **Example 3.12** (Motivating Example with Algebra Equivalence) | `toNat/fromNat : Nat ≃ Bin`: `nat-bin-eqv` (homomorphism: `fromNat-hom`) | [inductive-repair/examples/nat.agda:142](inductive-repair/examples/nat.agda#L142) |
| | `recNatSwap` | [inductive-repair/examples/nat.agda:447](inductive-repair/examples/nat.agda#L447) |
| | `isZeroCoh` | [inductive-repair/examples/nat.agda:460](inductive-repair/examples/nat.agda#L460) |
| | `zUnitB-nat : (b : Bin) → toNat b + zero ≡ toNat b` (named `zero-is-unit-Bin`) | [inductive-repair/examples/nat.agda:503](inductive-repair/examples/nat.agda#L503) |
| | `zUnitCoh` (named `zero-is-unit-Bin-coh`) | [inductive-repair/examples/nat.agda:513](inductive-repair/examples/nat.agda#L513) |
| **Definition 3.13** (Algebra Configuration) | `InitAlgOn` (record with `sup`, `isInit`) | [palg.agda:141](palg.agda#L141) |
| | `AlgConfig` | [inductive-repair/palg-config.agda:23](inductive-repair/palg-config.agda#L23) |
| The repair map of an algebra configuration is an algebra isomorphism (§3.3) | `algConfigToAlgEquiv` | [inductive-repair/palg-config.agda:234](inductive-repair/palg-config.agda#L234) |
| All three correctness conditions follow from the two initial algebras alone (§3.3) | module `AlgCoherence`; `constr_ok` is `constr-ok-init` | [inductive-repair/palg-coherence.agda:41](inductive-repair/palg-coherence.agda#L41), [:64](inductive-repair/palg-coherence.agda#L64) |
| **Proposition 3.14** (Algebra Config iff Configuration) | (→) `configToPalg` | [inductive-repair/conversion.agda:40](inductive-repair/conversion.agda#L40) |
| | (←) `palgConfigToConfig`, which lands on a W-type signature as the proof sketch says | [inductive-repair/conversion.agda:55](inductive-repair/conversion.agda#L55) |
| **Proposition 3.15** (Repair by Instantiation) | `foldSwap` | [inductive-repair/palg-config.agda:272](inductive-repair/palg-config.agda#L272) |
| Induction is a fold into the total-space algebra (§3.3, after Prop. 3.15) | `bridgeBwd` (= `initToHalf.initAlgToIndAlg`) | [inductive-repair/bridge.agda:36](inductive-repair/bridge.agda#L36) |
| §3.4 Repair without Univalence | the whole inductive development; see [Axioms](#axioms-and-trusted-base) | [common.agda:186](common.agda#L186) |

## Section 4: Coinductive Types and Final Coalgebras

The coinductive files redefine `P` and its action (`P-mor`, the paper's
`P-map`) at [coinductive-repair/coalg.agda:49](coinductive-repair/coalg.agda#L49)
and [:52](coinductive-repair/coalg.agda#L52), for Cubical Agda.

| Paper | Agda | Location |
|-------|------|----------|
| `Stream`, `cons`, `streamComp`, `Stream'` (§4 opening listings) | `Stream`, `cons`, `streamComp`, `Stream'` | [coinductive-repair/examples/stream.agda:59](coinductive-repair/examples/stream.agda#L59), [:72](coinductive-repair/examples/stream.agda#L72), [:79](coinductive-repair/examples/stream.agda#L79), [:66](coinductive-repair/examples/stream.agda#L66) |
| **Definition 4.1** (Coalgebra) | `P-Coalg` | [coinductive-repair/coalg.agda:57](coinductive-repair/coalg.agda#L57) |
| **Example 4.2** (Stream Coalgebra) | `outStream`, `StreamCoalg` (positions `Obs = λ _ → ⊤`) | [coinductive-repair/examples/stream.agda:91](coinductive-repair/examples/stream.agda#L91), [:97](coinductive-repair/examples/stream.agda#L97), [:56](coinductive-repair/examples/stream.agda#L56) |
| **Remark 4.3** | stated and proven in the paper (immediate from `P A B X = Σ A (λ a → B a → X)`) | — |
| **Definition 4.4** (Coalgebra Homomorphism) | `isCoalgHom` | [coinductive-repair/coalg.agda:68](coinductive-repair/coalg.agda#L68) |
| | `CoalgHom` | [coinductive-repair/coalg.agda:78](coinductive-repair/coalg.agda#L78) |
| **Example 4.5** (Stream Homomorphism) | `Stream-corec-isHom`, `toStream'-hom` | [coinductive-repair/examples/stream.agda:207](coinductive-repair/examples/stream.agda#L207), [:312](coinductive-repair/examples/stream.agda#L312) |
| **Definition 4.6** (Final Coalgebra) | `isFinal` | [coinductive-repair/coalg.agda:148](coinductive-repair/coalg.agda#L148) |
| **Definition 4.7** (Homotopy-Final Coalgebra) | `isHFinal` | [coinductive-repair/coalg.agda:534](coinductive-repair/coalg.agda#L534) |
| **Example 4.8** (Final Stream Coalgebra) | `outStream`, `Stream-corec` | [coinductive-repair/examples/stream.agda:91](coinductive-repair/examples/stream.agda#L91), [:107](coinductive-repair/examples/stream.agda#L107) |
| | "a homomorphism definitionally": `Stream-corec-isHom` (`= refl`) | [coinductive-repair/examples/stream.agda:207](coinductive-repair/examples/stream.agda#L207) |
| | "the unique such function": `Stream-isFinal` | [coinductive-repair/examples/stream.agda:248](coinductive-repair/examples/stream.agda#L248) |
| **Definition 4.9** (Bisimulation) | `Bisim` (fields `b-shape`, `b-pos`; positions related over a `PathP` along `b-shape`) | [coinductive-repair/coalg.agda:176](coinductive-repair/coalg.agda#L176) |
| | `isBisim` | [coinductive-repair/coalg.agda:191](coinductive-repair/coalg.agda#L191) |
| **Proposition 4.10** (Coinduction Principle for Final Coalgebra) | `coind-from-isFinal` | [coinductive-repair/coalg.agda:333](coinductive-repair/coalg.agda#L333) |
| Bisimulation is the weakest one-step condition supporting Rutten's construction (text after Prop. 4.10) | `Bisim-weakest` | [coinductive-repair/coalg.agda:319](coinductive-repair/coalg.agda#L319) |
| | `Bisim` supports the construction: `isBisim→isRuttenBisim` | [coinductive-repair/coalg.agda:245](coinductive-repair/coalg.agda#L245) |
| | any condition supporting it implies `Bisim`: `isRuttenBisim→isBisim` | [coinductive-repair/coalg.agda:303](coinductive-repair/coalg.agda#L303) |
| **Example 4.11** (Bisimulation on Streams) | `StreamBis`, `Stream-coind` | [coinductive-repair/examples/stream.agda:146](coinductive-repair/examples/stream.agda#L146), [:154](coinductive-repair/examples/stream.agda#L154) |
| **Definition 4.12** ((Homotopy) Coalgebra Configuration) | `FinalCoalgOn` | [coinductive-repair/coconfig-coalg-equiv.agda:124](coinductive-repair/coconfig-coalg-equiv.agda#L124) |
| | `CoalgConfig A B C D = FinalCoalgOn A B C × FinalCoalgOn A B D` | [coinductive-repair/coconfig-coalg-equiv.agda:128](coinductive-repair/coconfig-coalg-equiv.agda#L128) |
| | homotopy version: `FinalCoalgOnˢ`, `HCoalgConfig` | [coinductive-repair/coconfig-coalg-equiv.agda:489](coinductive-repair/coconfig-coalg-equiv.agda#L489), [:493](coinductive-repair/coconfig-coalg-equiv.agda#L493) |
| | "determines a coalgebra isomorphism": `coalgConfigToCoalgEquiv` (via `coalgEquivFromFinals`) | [coinductive-repair/coconfig-coalg-equiv.agda:288](coinductive-repair/coconfig-coalg-equiv.agda#L288), [:220](coinductive-repair/coconfig-coalg-equiv.agda#L220) |
| | homotopy version: `coalgEquivˢFromFinals` | [coinductive-repair/coconfig-coalg-equiv.agda:438](coinductive-repair/coconfig-coalg-equiv.agda#L438) |
| **Example 4.13** (Coalgebraic Repair with Stream and Stream') | `consSeed`, `cons-M`, `cons'-M` | [coinductive-repair/examples/stream.agda:126](coinductive-repair/examples/stream.agda#L126), [:134](coinductive-repair/examples/stream.agda#L134), [:137](coinductive-repair/examples/stream.agda#L137) |
| | `etaR`, `etaStep`, `streamComp-M`, `streamComp'-M` | [coinductive-repair/examples/stream.agda:182](coinductive-repair/examples/stream.agda#L182), [:185](coinductive-repair/examples/stream.agda#L185), [:189](coinductive-repair/examples/stream.agda#L189), [:200](coinductive-repair/examples/stream.agda#L200) |
| **Definition 4.14** (M-Types) | `HasMRules` (fields `rec` = paper's `corec`, `β-shape`, `β-pos`, `η`) | [coinductive-repair/coalg.agda:203](coinductive-repair/coalg.agda#L203) |
| | `coind` is derivable, not a rule: `HasMRules-coind` | [coinductive-repair/coalg.agda:411](coinductive-repair/coalg.agda#L411) |
| Native M-types satisfy the rules (§4.3 listing) | record `M`, `corec` | [coinductive-repair/mtype.agda:26](coinductive-repair/mtype.agda#L26), [:41](coinductive-repair/mtype.agda#L41) |
| | `M-isFinal`, `M-HasMRules` | [coinductive-repair/coalg.agda:156](coinductive-repair/coalg.agda#L156), [:404](coinductive-repair/coalg.agda#L404) |
| **Definition 4.15** (Homotopy M-Types) | `HasHMRules` (field `η-Σ`) | [coinductive-repair/coalg.agda:1160](coinductive-repair/coalg.agda#L1160) |
| `Stream` is a set when its element type is (§4.3, after Def. 4.15) | `isSet-Stream`, `isSet-Stream'` | [coinductive-repair/examples/stream.agda:542](coinductive-repair/examples/stream.agda#L542), [:577](coinductive-repair/examples/stream.agda#L577) |
| | hence homotopy-final: `Stream-isHFinal`, `Stream'-isHFinal` | [coinductive-repair/examples/stream.agda:556](coinductive-repair/examples/stream.agda#L556), [:588](coinductive-repair/examples/stream.agda#L588) |
| **Definition 4.16** (Destructor Algebra) | `DestrArity`, `Outputs` | [coinductive-repair/config.agda:46](coinductive-repair/config.agda#L46), [:56](coinductive-repair/config.agda#L56) |
| | functoriality: `mapOutputs`, `mapOutputs-id`, `mapOutputs-∘` | [coinductive-repair/config.agda:65](coinductive-repair/config.agda#L65), [:72](coinductive-repair/config.agda#L72), [:79](coinductive-repair/config.agda#L79) |
| | `CoSignature`, `DestrAlgebra` | [coinductive-repair/config.agda:98](coinductive-repair/config.agda#L98), [:111](coinductive-repair/config.agda#L111) |
| **Definition 4.17** (Coinductive Configuration) | `CoindCoalg` (fields `destr`, `corec`, `corec-β`, `corec-η`) | [coinductive-repair/config.agda:128](coinductive-repair/config.agda#L128) |
| | `coind` derivable from the fields: `deriveCoind` | [coinductive-repair/config.agda:314](coinductive-repair/config.agda#L314) |
| | `CoConfig` | [coinductive-repair/config.agda:1088](coinductive-repair/config.agda#L1088) |
| **Definition 4.18** (Homotopy Coinductive Configuration) | `HCoindCoalg` (field `corec-uniq-Σ`) | [coinductive-repair/config.agda:704](coinductive-repair/config.agda#L704) |
| | `HCoConfig` | [coinductive-repair/config.agda:1100](coinductive-repair/config.agda#L1100) |
| **Proposition 4.19** (Correctness Conditions) | module `CoCoherence cfg` (parts 1–3) | [coinductive-repair/coherence.agda:89](coinductive-repair/coherence.agda#L89) |
| | (1) `destr_ok`: `destr-ok` | [coinductive-repair/coherence.agda:108](coinductive-repair/coherence.agda#L108) |
| | (2) `iota_ok`: `beta-ok-C`, `beta-ok-D` | [coinductive-repair/coherence.agda:119](coinductive-repair/coherence.agda#L119), [:127](coinductive-repair/coherence.agda#L127) |
| | (3) `corec_ok`: `corec-ok` | [coinductive-repair/coherence.agda:161](coinductive-repair/coherence.agda#L161) |
| | (4) `coind_ok`, over `HCoConfig`: module `HCoCoherence`, `coind-ok-strict` | [coinductive-repair/coherence.agda:240](coinductive-repair/coherence.agda#L240), [:593](coinductive-repair/coherence.agda#L593) |
| | proof sketch: 2-D coinduction derived from `corec-uniq-Σ`, `deriveCoind2D` | [coinductive-repair/config.agda:1072](coinductive-repair/config.agda#L1072) |
| | (also: `coind_ok` directly when `D` is a set, `coind-ok-strict-isSet`) | [coinductive-repair/coherence.agda:611](coinductive-repair/coherence.agda#L611) |
| `corec_ok` for streams (text after Prop. 4.19) | `corecSwap'` | [coinductive-repair/examples/stream.agda:347](coinductive-repair/examples/stream.agda#L347) |
| Streams over an h-set form an `HCoConfig` (text after Prop. 4.19) | `streamHCoConfig` | [coinductive-repair/examples/stream.agda:610](coinductive-repair/examples/stream.agda#L610) |
| **Example 4.20** (Stream and Stream' Repair via Configurations) | `StreamSig` | [coinductive-repair/examples/stream.agda:379](coinductive-repair/examples/stream.agda#L379) |
| | `streamCoindCoalg`, `stream'CoindCoalg`, `streamCoConfig` | [coinductive-repair/examples/stream.agda:384](coinductive-repair/examples/stream.agda#L384), [:387](coinductive-repair/examples/stream.agda#L387), [:391](coinductive-repair/examples/stream.agda#L391) |
| | `unfold` | [coinductive-repair/examples/stream.agda:401](coinductive-repair/examples/stream.agda#L401) |
| | `consVia`, `consCfg`, `consCfg'` | [coinductive-repair/examples/stream.agda:437](coinductive-repair/examples/stream.agda#L437), [:445](coinductive-repair/examples/stream.agda#L445), [:447](coinductive-repair/examples/stream.agda#L447) |
| | `streamCompCfg`, `streamCompCfg'` | [coinductive-repair/examples/stream.agda:465](coinductive-repair/examples/stream.agda#L465), [:477](coinductive-repair/examples/stream.agda#L477) |
| | "each equation holds definitionally": `consCfg'-head`, `consCfg'-next` (both `= refl`) | [coinductive-repair/examples/stream.agda:492](coinductive-repair/examples/stream.agda#L492), [:496](coinductive-repair/examples/stream.agda#L496) |
| **Theorem 4.21** ((Homotopy) M-Types are (Homotopy) Final Coalgebras) | (1) `HasMRules-≃-isFinal` | [coinductive-repair/coalg.agda:425](coinductive-repair/coalg.agda#L425) |
| | (2) `HasHMRules-≃-isHFinal` | [coinductive-repair/coalg.agda:1278](coinductive-repair/coalg.agda#L1278) |
| **Definition 4.22** (M-type Configuration) | `MTypeArity` | [coinductive-repair/coconfig-coalg-equiv.agda:34](coinductive-repair/coconfig-coalg-equiv.agda#L34) |
| | `MTypeSignature` | [coinductive-repair/coconfig-coalg-equiv.agda:38](coinductive-repair/coconfig-coalg-equiv.agda#L38) |
| | `MTypeCoindCoalg A B C = CoindCoalg (MTypeSignature A B) C` | [coinductive-repair/coconfig-coalg-equiv.agda:43](coinductive-repair/coconfig-coalg-equiv.agda#L43) |
| | `MTypeCoConfig A B C D = CoConfig (MTypeSignature A B) C D` | [coinductive-repair/coconfig-coalg-equiv.agda:47](coinductive-repair/coconfig-coalg-equiv.agda#L47) |
| Coalgebra equivalence `CoalgEquiv` (§4.4, before Lemma 4.23) | `CoalgEquiv` | [coinductive-repair/coconfig-coalg-equiv.agda:104](coinductive-repair/coconfig-coalg-equiv.agda#L104) |
| Homotopy version `CoalgEquiv^H` | `CoalgEquivˢ` | [coinductive-repair/coconfig-coalg-equiv.agda:400](coinductive-repair/coconfig-coalg-equiv.agda#L400) |
| **Lemma 4.23** (Coinductive Configurations Faithfully Embed into M-type Configurations) | the polynomial: `A`, `B` (using `recPos`) | [coinductive-repair/mtype-config.agda:177](coinductive-repair/mtype-config.agda#L177), [:180](coinductive-repair/mtype-config.agda#L180), [:69](coinductive-repair/mtype-config.agda#L69) |
| | the embedding `CoConfig sig C D → Σ A Σ B MTypeCoConfig A B C D`: `allCoConfigMTypeCoConfig` | [coinductive-repair/mtype-config.agda:301](coinductive-repair/mtype-config.agda#L301) |
| | faithfulness: `mtypeCoConfigEquivAgree-f`, `mtypeCoConfigEquivAgree-g` | [coinductive-repair/mtype-config.agda:316](coinductive-repair/mtype-config.agda#L316), [:325](coinductive-repair/mtype-config.agda#L325) |
| **Theorem 4.24** (Coinductive Configurations are Coalgebra Isomorphisms) | (1) `mtypeCoConfig↔ : MTypeCoConfig A B C D ↔ CoCoalgIsoData A B C D` | [coinductive-repair/coconfig-coalg-equiv.agda:336](coinductive-repair/coconfig-coalg-equiv.agda#L336) |
| | right-hand side of (1): `CoCoalgIsoData` | [coinductive-repair/coconfig-coalg-equiv.agda:309](coinductive-repair/coconfig-coalg-equiv.agda#L309) |
| | (2) `hcoConfigEqvˢ : HCoConfig (MTypeSignature A B) C D ≃ CoCoalgIsoDataˢ A B C D` | [coinductive-repair/coconfig-coalg-equiv.agda:712](coinductive-repair/coconfig-coalg-equiv.agda#L712) |
| | right-hand side of (2): `CoCoalgIsoDataˢ` | [coinductive-repair/coconfig-coalg-equiv.agda:652](coinductive-repair/coconfig-coalg-equiv.agda#L652) |
| | proof sketch: carrier-level bridges `coalgBridgeFwd`/`coalgBridgeBwd` (final) and `bridgeˢ` (homotopy-final); `fullCoalgIsoˢ : HCoalgConfig A B C D ≃ CoCoalgIsoDataˢ A B C D` | [coinductive-repair/coconfig-coalg-equiv.agda:135](coinductive-repair/coconfig-coalg-equiv.agda#L135), [:164](coinductive-repair/coconfig-coalg-equiv.agda#L164), [:641](coinductive-repair/coconfig-coalg-equiv.agda#L641), [:661](coinductive-repair/coconfig-coalg-equiv.agda#L661) |
| Uniqueness of coinductive repair (text after Thm. 4.24) | `isProp-CoalgEquivˢ` | [coinductive-repair/coconfig-coalg-equiv.agda:459](coinductive-repair/coconfig-coalg-equiv.agda#L459) |

## What is not formalized, and other notes

* **Remark 4.3** is proven in the paper only. It is immediate from the
  definition of `P` as a Σ-type.
* "The bisimulation and the path type are equivalent in Cubical Agda"
  (§4.2) is cited from Vezzosi et al., not proved here.
* As the paper says (§4.3), the artifact does not prove that the
  native `M` record is a homotopy M-type (`HasHMRules`) in general. It
  proves `HasMRules` for `M` (`M-HasMRules`), homotopy-finality for
  streams over an h-set (`Stream-isHFinal`), and one direction relating
  `isHFinal` for `M` to 2-D coinduction (`isHFinal→M-Coind-2D`,
  [coinductive-repair/coalg.agda:1069](coinductive-repair/coalg.agda#L1069)).
* Theorem 4.24 (1) and Proposition 3.14 are logical equivalences
  (`_↔_` and a pair of maps), exactly as stated in the paper. All other
  "≃" results are genuine bi-invertible equivalences (`_≃_`).
* The paper leaves the polynomial `(A, B)` implicit in `MTypeCoindCoalg C`
  and `MTypeCoConfig C D`. In Agda they take it explicitly:
  `MTypeCoindCoalg A B C`, `MTypeCoConfig A B C D`.


## Names in the paper's listings vs. Agda names

The paper's code listings use short names. Where the Agda name differs:

| Paper | Agda | Location |
|-------|------|----------|
| `Nat`, `zero`, `succ`, `+` | `ℕ`, `zero`, `succ`, `_+_` | [common.agda](common.agda) |
| `NatInit`, `BinInit` | `ℕ-InitAlgOn`, `Bin-InitAlgOn` | [inductive-repair/examples/nat.agda:196](inductive-repair/examples/nat.agda#L196), [:223](inductive-repair/examples/nat.agda#L223) |
| `indNat` (Ex. 3.8) | `indNatIndAlg` | [inductive-repair/examples/nat.agda:335](inductive-repair/examples/nat.agda#L335) |
| `isZeroN`, `isZeroB` (Ex. 3.8) | `isZeroNAlg`, `isZeroBinAlg` | [inductive-repair/examples/nat.agda:354](inductive-repair/examples/nat.agda#L354), [:428](inductive-repair/examples/nat.agda#L428) |
| `zUnit` (Ex. 3.8) | `zero-is-unitAlg` | [inductive-repair/examples/nat.agda:362](inductive-repair/examples/nat.agda#L362) |
| `zUnitB` (Ex. 3.8, native on `Bin`) | `zUnitB` | [inductive-repair/examples/nat.agda:434](inductive-repair/examples/nat.agda#L434) |
| `zUnitB-nat` (Ex. 3.12 and Intro, over `toNat b`) | `zero-is-unit-Bin` | [inductive-repair/examples/nat.agda:503](inductive-repair/examples/nat.agda#L503) |
| `zUnitCoh` (Ex. 3.12) | `zero-is-unit-Bin-coh` | [inductive-repair/examples/nat.agda:513](inductive-repair/examples/nat.agda#L513) |
| `toNatFromNat` (Ex. 3.12) | `toNat-fromNat` (the `η` of `nat-bin-eqv`) | [inductive-repair/examples/nat.agda](inductive-repair/examples/nat.agda) |
| `IH`, `Ind`, `Beta` (Def. 2.2) | `IHs`, `Induction`, `BetaLaw` | [inductive-repair/indspec.agda](inductive-repair/indspec.agda) |
| `corec` of an M-type (Def. 4.14, Fig. 1) | field `rec` of `HasMRules` / `HasHMRules` | [coinductive-repair/coalg.agda:203](coinductive-repair/coalg.agda#L203) |
| `P-map` (§4) | `P-mor` | [coinductive-repair/coalg.agda:52](coinductive-repair/coalg.agda#L52) |
| `isFinal→HasMRules M-isFinal` (§4.3 listing) | `isFinal→HasMRules`, `M-isFinal` | [coinductive-repair/coalg.agda](coinductive-repair/coalg.agda) |
| `CoalgEquiv^H` | `CoalgEquivˢ` | [coinductive-repair/coconfig-coalg-equiv.agda:400](coinductive-repair/coconfig-coalg-equiv.agda#L400) |
| `P X ⊤` positions in stream listings | `P X Obs`, with `Obs _ = ⊤` | [coinductive-repair/examples/stream.agda:56](coinductive-repair/examples/stream.agda#L56) |
