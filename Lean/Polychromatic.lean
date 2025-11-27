import Polychromatic.Colouring
import Polychromatic.Compactness
import Polychromatic.DiscreteProbability
import Polychromatic.Existence
import Polychromatic.ForMathlib.Misc
import Polychromatic.FourThree.Compute
import Polychromatic.FourThree.FourThree
import Polychromatic.FourThree.Theory
import Polychromatic.LocalLemma
import Polychromatic.LovaszFunction
import Polychromatic.Main
import Polychromatic.PolychromNumber

/-!
# Polychromatic Colourings

This is the main entry point for the polychromatic colourings formalization.
A colouring of the integers is called `S`-polychromatic if every translate of the finite set `S`
contains an element of each colour class.

## Main results

The primary target of this formalization is to prove that for any set `S` of size 4,
there exists an `S`-polychromatic colouring in 3 colours.

## Structure

The modules in this library are organized as follows:

- `Colouring`: Core definitions of `IsPolychrom` and `HasPolychromColouring`
- `PolychromNumber`: The polychromatic number of a set
- `Existence`: Existence results for polychromatic colourings using the Lovász Local Lemma
- `LocalLemma`: The Lovász Local Lemma formalization
- `LovaszFunction`: The Strauss function and its bounds
- `Compactness`: Compactness arguments for infinite colourings (Rado selection principle)
- `DiscreteProbability`: Markov and Chebyshev inequalities for discrete probability
- `Main`: The main theorem (work in progress)
- `FourThree/`: Computational proof that all quadruples with `c < 289` have 3-polychromatic
  colourings

## References

See the README for more information on the mathematical background.
-/
