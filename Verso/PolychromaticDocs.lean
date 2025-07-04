/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Patrick Massot
-/

import VersoManual

-- import VerboseManual.TacticReference

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

-- open VerboseManual

set_option pp.rawOnError true

-- This is the source of code examples to be shown in the document. It should be relative to the
-- current Lake workspace. One good way to set up the files is in a Git repository that contains one
-- Lake package for example code and another for the docs, as sibling directories.
set_option verso.exampleProject "../examples"

-- This is the module that will be consulted for example code. It can be overridden using the
-- `(module := ...)` argument to most elements that show code.
set_option verso.exampleModule "VerboseDemo.Examples"




#doc (Manual) "Verbose Lean" =>
%%%
authors := ["Patrick Massot"]
%%%

# Overview

Verbose Lean is a mathematics teaching library for Lean. It is designed for courses whose primary
goal is to teach mathematical reasonning rather than Lean itself.
See the {ref "sec-pedagogical-goals"}[pedagogical goals section] for more information about things
you can hope to teach with this tool.
The description below assumes some familiarity with Lean.
It doesn’t assume any expertise, but if you have never used Lean at all and never saw anyone using
Lean then you should first read the {ref "sec-lean-beginners"}[Backgroung for Lean beginners]
section, and then come back here.

This library has two main aspects. It provides a controlled natural language input language and
customizable automation and help.

The goal of the natural language input is *not* to make Lean code easier to write. The goal is to
make it easier for students to transfer their new skills from Lean to paper. Indeed it is not so
hard to teach students when they need to write
```
rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩
```
but then it’s much harder to make sure they write the corresponding line on paper which could be
something like:

Since f is continuous at x₀ and ε > 0 we get δ such that δ > 0 and
∀ x, |x - x₀| ≤ δ ⇒ |f(x) - f(x₀)| ≤ ε.

Verbose Lean allows to write the above sentence in Lean.
It actually offers several styles of sentences including the above one.
And it features a translation framework only to add new languages.
Currently everything in available in French and some version of English.

Customizable automation and help aim to emulate the detail requirements we would have on paper.
For instance, assume a proof features three natural numbers $`n`, $`N₁`, $`N₂` and an assumption that
$`n ≥ max(N₁, N₂)`. The teacher may decide here that going from $`n ≥ max(N₁, N₂)` to $`n ≥ N₁` does not
require any justification. Verbose Lean can be configured to automatically justify this step.
By contrast, Verbose Lean does not expose Lean’s most powerful tactics that would make many
exercises completely trivial.

The customizable help system is meant to mitigate the technological barrier and allow to benefit
from what Lean offers without too much non-mathematical work.
The first level of assistance is the `help` tactic that analyses the shape of the current goal
and explains the syntax of the tactics allowing to start a proof.
For instance if the goal is
```
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ ⇒ |f x  - f x₀| ≤ ε
```
then, assuming the default configuration is used, `help` will say
```
The goal starts with “∀ ε > 0”
Hence a direct proof starts with:
Fix ε > 0
```
and the last line can be clicked to insert the `Fix ε > 0` tactic in place of the `help` call.
One can similarly ask for help about ways to use an assumption.

The next level of assistance is provided by specialized Lean widgets that allow to write
most proof steps by clicking on elements of the tactic state and choosing between a couple
of action proposals.
For instance, assuming the default configuration is used, if the local context contains an
assumption saying `f is continuous at x₀` and a real number `ε`, then
clicking on both will propose to insert in the proof either

`Since f is continuous at x₀ and ε > 0 we get δ such that δ > 0 and ∀ x, |x - x₀| ≤ δ ⇒ |f x  - f x₀| ≤ ε`

or

`Since f is continuous at x₀ and ε/2 > 0 we get δ such that δ > 0 and ∀ x, |x - x₀| ≤ δ ⇒ |f x  - f x₀| ≤ ε/2`

or

`Since f is continuous at x₀ and ε + 1 > 0 we get δ such that δ > 0 and ∀ x, |x - x₀| ≤ δ ⇒ |f x  - f x₀| ≤ ε + 1`.

All those help features can be switched off or configured to fit the teacher’s goals and
constraints.

You can go to the {ref "sec-examples"}[examples section] to get a sample of proofs written in
different styles supported by Verbose Lean, with different levels of automation.

You can also take a look at what a full course using Verbose Lean can look like by browsing
the [Proofs with Lean repository](https://github.com/PatrickMassot/proofs_with_lean).
That course is an English translation of course given in Orsay in 2025, so it has been tested on
actual students.
Solutions to all exercises as well as extras exercises are available upon requests to
Patrick Massot if you are a teacher.
Those solutions should not be made available broadly so that instructors can set those exercises as
homework.

You should feel free to fork that repository and modify the exercises and the Verbose Lean
configuration to fit your goals and local teaching context, as long as you mention the original
source.

If you want to start from scratch building a Lean project using Verbose Lean, then the next step is
to read the {ref "sec-getting-started"}[getting started section].



# Pedagogical goals
%%%
tag := "sec-pedagogical-goals"
%%%

The first main goal is to train students to have a clear view of the
current state of the proof:
what is currently being proven, what are the current assumptions, which
mathematical objects are fixed.
The next pedagogical goal is to train students to automatically perform proof
steps depending of the syntactic structure of the current goal.
For instance, a direct proof of a universally
quantified statement starts with fixing an object of the relevant type.

A basic requirement here is to make sure that every statement has a clear
status: is it something that is known to be true? Something that we assume?
Something that will be proven soon?
We claim that this goal is much easier to achieve if there is a clear
separation between stating, proving and using.
For any given logical operator or quantifier, there are syntactic rules that
explain how to form a mathematical statement using it together with
some previously existing statements.
For instance, given statements $`P` and $`Q`, one can form the new statement
$`P \implies Q` using the implication operator.
Then there are rules that explain how to prove such a statement.
In the case of a direct proof of an implication, one should assume the left hand
side and try to derive the right hand side.
Finally there are rules about how to use such a statement.
In the implication case the rule says that knowing that $`P` implies $`Q` and that
$`P` allows to deduce $`Q`.
This distinction seems obvious, but in practice it is very blurred, both
by students and by professional mathematicians.
Of course the difference is that mathematicians know what they are doing even
when they are very sloppy about this distinction.
We think that enforcing a clear distinction is very useful for beginners,
although it can feel pedantic to more advanced people.
One of the most frequent cases is failing to distinguish between stating the
existence of a mathematical object satisfying some condition and fixing a
witness.
An example would be to say or write “since $`f` is continuous and $`\varepsilon`
is positive, there exists $`\delta` such that…” and then refer to some $`\delta` on the
following line.
The other very common one is more tied to using symbols instead of text.
It uses the implication symbol as an abbreviation of the word “hence” or
“therefore”, and more generally mixing using an implication and stating one.
An example would be writing on a blackboard “$`f` is polynomial $`\implies` $`f` is
continuous” instead of “$`f` is polynomial hence continuous”.
This misuse of a symbol is extremely problematic for beginners since this
alternative meaning of the symbol turns every legitimate use into nonsense,
and beginners lack the expertise required to understand which meaning is used.
For instance reading the definition of convergence of a function $`f` towards a
number $`l` at some point $`x_0` with this
interpretation for the implication symbol gives “for every positive
$`\varepsilon`, there exists some positive $`\delta` such that for every $`x`,
$`|x - x_0| < \delta` hence $`|f(x) - l| < \varepsilon`”.
A less ubiquitous but still common example is a confusion between stating a
claim starting with a universal quantifier and beginning a proof of such a
statement.
An example would start a continuity proof with “For all positive $`\varepsilon`, we
know that…” whose start suggests stating a universally quantified result rather
than proving one.

All those logical errors (or at least sloppy writing) also impact achieving a
third pedagogical goal which is to train students to make a clear distinction
between bound and free variables.
This is very related to keeping track of what is fixed in the current
state of the proof, but with the additional twist that some variable name can
appear simultaneously as the name of a free variable and as a bound variable in
some assumption or in the current target statement.

The next teaching goal that we want to achieve with this technology is
to train students to classify proof steps into safe reversible steps that
require no initiative and risky irreversible steps that require some creativity.
Here irreversible means it can lead to a goal that is not provable.
An example in the first category is fixing a positive number at the beginning of a
proof using the definition of continuity, or extracting a witness out of an
existential assumption.
An example in the second category would be announcing an existential witness or
specializing a universally quantified assumption to a unique object.
The alternation between routine safe steps and risky creative steps
is a crucial aspect of mathematical proof creation. This is not necessarily
emphasized when presenting a proof on a blackboard.

On top of that there is a final goal which is to learn how to choose indirect
strategies instead of simply following the syntax of the current target.
Those includes stating and proving an intermediate fact, using a lemma instead
of reproving everything, and the use of the excluded middle
axiom, e.g. through proofs by contradiction or contraposition.


# Examples

%%%
tag := "sec-examples"
%%%

```anchor ContinuitySequentialContLean
example (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
    (hf : continuous_function_at f x₀) (hu : sequence_tendsto u x₀) :
    sequence_tendsto (f ∘ u) (f x₀) := by
  intro ε ε_pos
  rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩
  rcases hu δ δ_pos with ⟨N, hN⟩
  use N
  intro n n_ge
  apply hδ
  apply hN
  exact n_ge
```

With Verbose Lean, it can look like this:

```anchor ContinuitySequentialCont
Exercise "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Fix ε > 0
  By hf applied to ε using ε_pos we get δ such that δ_pos and Hf
  By hu applied to δ using δ_pos we get N such that Hu
  Let's prove that N works
  Fix n ≥ N
  We apply Hf
  We apply Hu
  We conclude by n_ge
QED
```

For instance, the line

```anchorTerm ContinuitySequentialCont
By hf applied to ε using ε_pos we get δ such that δ_pos and Hf
```

corresponds to

```anchorTerm ContinuitySequentialContLean
rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩
```

# Getting started

%%%
tag := "sec-getting-started"
%%%

This section explains how to create a new Lean project that uses Verbose Lean.
Creating a series of exercises in Lean is a lot of work, and Verbose Lean does not change that.
If you would rather modify an existing series of exercises, you can clone the
[Proofs with Lean project](https://github.com/PatrickMassot/proofs_with_lean).

We assume you already installed Lean.
See the Lean [https://lean-lang.org/lean4/doc/quickstart.html](quickstart page)
if you need help doing that.

In order to use Verbose Lean in your teaching, you need to create a Lean
project. You can do that from the VSCode Lean menu or type in a terminal
`lake new VerboseDemo lib` to create a `VerboseDemo` folder with a Lean project layout
(do not use any fancy character in the name of your folder).

Then you need to require the library in your lake file.
This means adding at the end of `lakefile.toml` in your project:
```
[[require]]
name = "verbose"
git = "https://github.com/PatrickMassot/verbose-lean4.git"
rev = "master"
```

Important note in case you had an existing project:
Verbose Lean will require Mathlib for you, so your `lakefile.toml` should *not*
mention Mathlib, otherwise you could be creating version
conflicts.

After adding the above `require`, you need to run `lake update verbose`
from your project folder.
This will update your `lake-manifest.json` file and download Verbose Lean with
all its dependencies.
This is large download since it includes a compiled Mathlib.

Assuming you use the `VerboseDemo` name, your `VerboseDemo` folder now contains a
`VerboseDemo` folder where all your Lean files go. It also contains a
`VerboseDemo.lean` file which should import all files from the `VerboseDemo` folder that
you want `lake build` to build (this typically means all files except for throw
away test files). Beware that Lean file whose name start with a number only
create pain.

You now need to create at least one teacher file that imports Verbose, configures it and
contains definitions you want to work with. Then you can create student files
with explanations and exercises.

For instance you can create in the `VerboseDemo` folder a file `Math101.lean`
containing:
```anchor Math101 (module := VerboseDemo.Math101)
import Mathlib.Topology.Instances.Real.Defs
import Verbose.English.All

open Verbose English

-- Let’s define mathematical notions here

def continuous_function_at (f : ℝ → ℝ) (x₀ : ℝ) :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

def sequence_tendsto (u : ℕ → ℝ) (l : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

-- and some nice notation

notation3:50 f:80 " is continuous at " x₀ => continuous_function_at f x₀
notation3:50 u:80 " converges to " l => sequence_tendsto u l

-- Now configure Verbose Lean
-- (those configuration commands are explained elsewhere)

configureUnfoldableDefs continuous_function_at sequence_tendsto

useDefaultDataProviders

useDefaultSuggestionProviders
```

and a `HomeWork1.lean` file containing:

```anchor HomeWork1 (module := VerboseDemo.GettingStarted)
import VerboseDemo.Math101

Example "Continuity implies sequential continuity"
  Given: (f : ℝ → ℝ) (u : ℕ → ℝ) (x₀ : ℝ)
  Assume: (hu : u converges to x₀) (hf : f is continuous at x₀)
  Conclusion: (f ∘ u) converges to f x₀
Proof:
  Let's prove that ∀ ε > 0, ∃ N, ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix ε > 0
  Since f is continuous at x₀ and ε > 0 we get δ such that
    (δ_pos : δ > 0) and (Hf : ∀ x, |x - x₀| ≤ δ ⇒ |f x - f x₀| ≤ ε)
  Since u converges to x₀ and δ > 0 we get N such that Hu : ∀ n ≥ N, |u n - x₀| ≤ δ
  Let's prove that N works : ∀ n ≥ N, |f (u n) - f x₀| ≤ ε
  Fix n ≥ N
  Since ∀ n ≥ N, |u n - x₀| ≤ δ and n ≥ N we get h : |u n - x₀| ≤ δ
  Since ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε and |u n - x₀| ≤ δ we conclude that |f (u n) - f x₀| ≤ ε
QED
```

Assuming the installation process succeeded, Lean should be happy to process
those files. You can then learn more about this library.


# Minimal Lean background

%%%
tag := "sec-lean-beginners"
%%%

This section is intended for readers who are interested in using a proof assistant for teaching but
have never used Lean at all.

To be written…


# Using an Index

{index}[index]
The index should contain an entry for “lorem ipsum”.
{index}[lorem ipsum] foo
{index subterm:="of lorem"}[ipsum]
{index subterm:="per se"}[ipsum]
{index}[ipsum]
Lorem ipsum dolor {index}[dolor] sit amet, consectetur adipiscing elit, sed {index}[sed] do eiusmod tempor incididunt ut labore et dolore magna aliqua. Ut enim ad minim veniam, quis nostrud exercitation ullamco laboris {index}[laboris] {see "lorem ipsum"}[laboris] {seeAlso "dolor"}[laboris] nisi ut aliquip ex ea commodo consequat. Duis aute irure dolor in reprehenderit in voluptate velit esse cillum dolore eu fugiat nulla pariatur. Excepteur sint occaecat cupidatat non proident, sunt in culpa qui officia deserunt mollit anim id est laborum.

This is done using the `{index}[term]` syntax. Sub-terms {index subterm:="sub-term"}[entry] can be added using the `subterm` parameter to `index`.

Multiple index {index}[index] targets for a term also work.

{ref "index"}[Index link]


# Index
%%%
number := false
tag := "index"
%%%

{theIndex}
