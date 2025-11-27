# Polychromatic Colourings - Lean Formalization

This directory contains a Lean 4 formalization of polychromatic colourings of integers.

## Overview

Given a finite set `S` of integers, a colouring of the integers is called **S-polychromatic**
if every translate of `S` contains an element of each colour class. The primary goal of
this formalization is to prove that for any set `S` of size 4, there exists an S-polychromatic
colouring in 3 colours.

## Building

### Prerequisites

- [elan](https://github.com/leanprover/elan) (Lean version manager)
- The correct Lean version will be automatically installed based on `lean-toolchain`

### Build Commands

```bash
# Download mathlib cache (CRITICAL - saves 1+ hour of build time)
lake exe cache get

# Build the project
lake build
```

## Project Structure

### Core Files

| File | Description |
|------|-------------|
| `Polychromatic.lean` | Root module that imports all components |
| `Polychromatic/Colouring.lean` | Core definitions: `IsPolychrom`, `HasPolychromColouring` |
| `Polychromatic/PolychromNumber.lean` | The polychromatic number `polychromNumber S` |
| `Polychromatic/Main.lean` | Main theorem (work in progress) |

### Probability and Local Lemma

| File | Description |
|------|-------------|
| `Polychromatic/LocalLemma.lean` | The Lovász Local Lemma formalization |
| `Polychromatic/Existence.lean` | Existence proofs using probabilistic methods |
| `Polychromatic/DiscreteProbability.lean` | Markov and Chebyshev inequalities |

### Supporting Infrastructure

| File | Description |
|------|-------------|
| `Polychromatic/Compactness.lean` | Rado selection principle and de Bruijn–Erdős theorem |
| `Polychromatic/LovaszFunction.lean` | The Strauss function and asymptotic bounds |
| `Polychromatic/ForMathlib/Misc.lean` | Auxiliary lemmas for potential mathlib contributions |

### Computational Verification (FourThree/)

| File | Description |
|------|-------------|
| `Polychromatic/FourThree/Theory.lean` | Theoretical framework reducing to finite cases |
| `Polychromatic/FourThree/FourThree.lean` | Metaprogramming for proof generation |
| `Polychromatic/FourThree/Compute.lean` | Computational proof for `c < 289` |

## Key Definitions

### `IsPolychrom S χ`

A colouring `χ : G → K` is S-polychromatic if for every `n : G` and every colour `k : K`,
there exists `a ∈ S` such that `χ(n + a) = k`.

### `HasPolychromColouring K S`

There exists a K-valued S-polychromatic colouring.

### `polychromNumber S`

The maximum `n` such that there exists a `Fin n`-valued S-polychromatic colouring.

## Main Results

- **`IsPolychrom.card_le`**: The number of colours is at most `|S|`
- **`polychromNumber_le_card`**: `polychromNumber S ≤ |S|`
- **`localLemma`**: The general Lovász Local Lemma
- **`symmetricLocalLemma`**: Symmetric version with `e · p · (d+1) ≤ 1` condition
- **`deBruijn_erdos`**: De Bruijn–Erdős theorem for graph colouring
- **`allC_289`**: All quadruples with `c < 289` have 3-polychromatic colourings

## Dependencies

- **Mathlib**: The Lean mathematical library (version specified in `lakefile.toml`)

## References

- Lovász, L. (1975). "Problems and results on 3-chromatic hypergraphs"
- de Bruijn, N. G.; Erdős, P. (1951). "A colour problem for infinite graphs"
- Rado, R. (1949). "Axiomatic treatment of rank in infinite sets"

## License

See the repository root for license information.
