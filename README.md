# Polychromatic Colourings in Lean

A formalisation of polychromatic colourings of integers in the Lean theorem prover

This repository aims to formalise results related to polychromatic colourings of integers. Given a
finite set `S` of integers, a colouring of the integers is called `S`-polychromatic if every
translate of `S` contains an element of each colour class.
A primary target is to show that for any set `S` of size 4, there is an `S`-polychromatic colouring
in 3 colours.

The repository structure is as follows:
- `Generation`: C++, Python and Z3 code which generates explicit colourings for certain sets
- `Lean`: Lean formal proofs of the results
- `Verso`: Lean code to generate the website
- `site`: A partial Jekyll website, which completed by the code in `Verso`