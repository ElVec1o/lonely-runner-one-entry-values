# Exact loneliness values of dilated one-entry replacements of {1,...,N}, and the failure of Kravitz's original spectrum conjecture

Pre-release draft of 25 November 2026 (private repository). Author: Vico Bonfioli. License: CC-BY-4.0 (`LICENSE.md`). Not peer reviewed. No DOI yet.
Paper: `paper/paperA1.pdf` (source `paper/paperA1.tex`). Companion drafts (not released): the other two papers of the series; dependency diagram `paper/dependency.pdf`.

## Abstract

For a finite set V of positive integers (runner speeds) let ML(V) = max_t min_{v in V} dist(tv, Z), where dist is the distance to the nearest integer. The Lonely Runner Conjecture of Wills and Cusick says that ML(V) >= 1/(N+1) for every set V of N speeds, with equality for [N] = {1,...,N}; a set with equality is called tight.
The paper determines ML exactly when one entry r > N/2 of [N] is replaced by a multiple mr with m >= 2: it equals max(1/(N+1), m/(mr+beta)), where beta is the least integer b >= N+1-r coprime to r (Theorem 1.1); the set is tight iff m(N+1-r) <= beta, which is the criterion of Goddyn and Wong, here with the value. Consequently Kravitz's original Loneliness Spectrum Conjecture, which says that every value of ML below 1/N for N speeds has the form sigma/(N sigma + 1), fails for N = 13, 19, 25, 31, 37, ...; for example ML(1,...,11,13,36) = 3/41 at N = 13 (Corollary 1.2). Fan and Sun had already refuted the conjecture at N = 4 and amended it; the amended form is not contradicted.

## Idea of the proof

Fix a time t and a threshold tau >= 1/(N+1) and suppose every speed of ([N] minus {r}) plus {mr} is farther than tau from an integer at t. Dirichlet's theorem gives a speed q <= N within 1/(N+1) of an integer; it cannot be retained, so q = r. Writing rt = c + eta with eta small, c is a unit modulo r and exactly one retained speed x is about to reach an integer, which forces eta < (1 - r tau)/x with x >= beta. The new speed mr sees the magnified offset m eta and is within tau of an integer as soon as eta < tau/m. The retained speeds close the window of admissible eta before the new speed opens it exactly when tau >= m/(mr+beta). This is a quantitative form of the Goddyn-Wong argument (they use the window at tau = 1/(N+1) to decide tightness; here tau is kept free).

## Main results

Numbers are those of the PDF of this version. "Lean" means: the declarations named are in the Lean repository `lonely-runner-near-tight-lean`, the saved build logs of the author's development tree end with `Build completed successfully`, no `sorryAx` occurs and only the three standard axioms are printed; no clean-checkout build has been run. The status of every statement of the paper (Lean, hand, computed, conjecture) is the table "Status per statement" in the paper; where the entry below says mixed, that table decides.

| paper | statement (short; the paper has the full statement) | label |
|---|---|---|
| Theorem 1.1 | `ML` of `[N]` with `r > N/2` replaced by `mr`, `m >= 2`: `max(1/(N+1), m/(mr+beta))`; tight iff `m(N+1-r) <= beta` | Lean (`Gap.theoremV`, `theoremV_tight_iff`); the gcd form of the criterion and the identity for the excess over `1/(N+1)` are by hand |
| Corollary 1.2 | `g_N <= G(N)`, `g_N <= 2/(2N+1)`, `N = r+1` with `6` dividing `r` and `5` not dividing `r`: `g_N <= 3/(3N+2)`; instances `g_13 <= 3/41`, `g_31 <= 4/127` | Lean for (a), (b), (c) and the listed instances; other table rows computed |
| Theorem 1.3 | primorial family: exact value, `liminf N^2 (g_N - 1/(N+1)) = 0`, no `c/N^2` lower bound | Lean; the rate `(2+o(1))/log N` is a classical import, by hand |
| Theorem 1.4 | `N >= 14`, `1 <= r <= N/2`, `w > N`: `ML >= 1/N`; the threshold 14 is sharp (`ML([13]\{6} u {69}) = 3/40`) | Lean for `N >= 14` (`Gap.OE_low_unconditional`); sharpness computed (two engines) |
| Theorem 1.5 | values below `1/N` of one-entry replacements have the shape `sigma/(N sigma + kappa)` | Lean (`FS1_shape_unconditional`) |
| Proposition 1.6, Conjecture 1.7 | the family minimum `G(N)`; `g_N = G(N)` for `N != 6` | bounds and limsup forms Lean; density and liminf by hand; Conjecture 1.7 is a CONJECTURE (evidence: exhaustive box searches, computed) |
| Proposition 1.8, Theorem 1.9 | two-sided bound for every `w >= 4N`; exact value for `D0 | w`, `w >= 2N^2` (hand proofs are in paper A2) | mixed: see the paper's status table |
| Theorem 1.10, Proposition 1.11 | the unit-window family; the thresholds `N_0(k)`: `N_0(1) = 14`, `N_0(2) = 21`, `N_0(phi(r)) >= 3r + ell*(r) + 1` | mostly Lean (`Gap.thmX_*`, `n0ge_phi`); `N_0(2) = 21` as an equality, the rate of `N_0(k)` and the lower bounds `N_0(4)`, `N_0(8)`, `N_0(16)` are not Lean (computed or by hand) |

Companions: A1 uses A2 for the hand proofs of Proposition 1.8 and Theorem 1.9 and B (Theorem 1.5) for `N >= 222` and the finiteness of `N_0(k)`; Theorems 1.1 to 1.5 need neither companion.

## Where the evidence is

* Lean: `Gap/Value`, `Cor`, `CThm`, `GFam`, `GAsym`, `Witness`, `OneOverR`, `OEFin*`, `OELow*`, `FinalCore`, `FS1`, `FS1Final`, `OneRL2Val`, `OneRG`, `ThmX*` (rows 1 to 7, 9 to 11, 22, 23, 24, 28 of `repro/MAP.md` in the Lean repository). Saved `#print axioms` lines: `repro/expected_output/` of the Lean repository (names as cited in the paper's Lean section); verdict script `repro/judge_axioms.sh`.
* Computed: `code/` (value formula, box searches, one-entry engine, `G(N)` tables and density, unit-window family, `N_0(2)` engine, hunts). See `code/README.md`: which program supports which statement is the packager's identification, not re-run; a list of computed statements with no identified program is at its end.
* By hand: the arguments of the paper marked "hand"; the ones marked "reviewed" were re-derived by a second pass of an AI system that did not write them. No human referee has read the paper.

## Not done yet

Blind reads by independent readers of the current text, the talk and the FAQ of the release rules, a refresh of the prior-art search (searches of 25 November 2026 are described in the paper and expire), a clean-checkout build of the Lean repository, and a reproduction script for the computed tables.

## Build the paper

`pdflatex` on `paper/paperA1.tex`, three rounds (the three drafts read each other's `.aux` files through `xr-hyper`; the companion `.aux` files of this version are in `paper/`; a companion number prints as `??` if they are missing). Compile the companions to regenerate them.

## Files

| path | content |
|---|---|
| `paper/` | `paperA1.tex`, `paperA1.pdf`, companion `.aux` files, `dependency.tex`, `dependency.pdf` |
| `code/` | the programs cited as "computed" (Rust, C), `build.sh`, `tools/launch_lite.sh`, `README.md` |
| `CHECKSUMS.sha256` | sha256 of every file of this repository except itself; check: `shasum -a 256 -c CHECKSUMS.sha256 | grep -vc ': OK'` prints `0` |
| `CITATION.cff`, `LICENSE.md`, `.gitignore` | citation data, license |

## Use of AI

The mathematical ideas, proofs, computations, Lean code and text of this work were produced with substantial assistance from AI systems (Anthropic's Claude models), working under the direction of the author, V. Bonfioli, who selected the problems, set the standards of verification, reviewed the results and takes responsibility for the contents. Every statement marked Lean-verified is checked by the Lean kernel and the printed axiom lists, not by the author or the AI systems; computed statements come from the programs in the paper repositories; statements labelled by hand are not machine-checked. The arguments marked reviewed were re-derived by a second pass of an AI system that did not write them; no human referee has read them. The arguments have not been refereed.

## Prior art and credit

* Goddyn and Wong (tight instances; the acceleration and the numerical criterion), Kravitz (barely lonely runners; the lemmas on one added speed and Theorem 5.1), Liu (the value of the one-deletion set; survey), Zhang (one-entry modifications and tight instances; Lemma 5.3, Question 8.1), Peng (unrefereed record 24363090), Fan and Sun (amended spectrum conjecture), Jain and Kravitz (relative spectra), Giri and Kravitz (structure of spectra), Yi, Gill and Bu (four runners; the height method), Cordella (six and seven speeds), and the unrefereed repository of 1337isnot1337. Full references and the exact attribution of each result are in the papers (sections "Attribution" and "Prior art").
