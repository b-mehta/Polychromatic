import Polychromatic.FourThree.FourThree

set_option linter.all false

-- set_option trace.debug true

-- set_option trace.profiler true
-- set_option trace.profiler.threshold 2

-- set_option trace.Elab.definition.body true

-- should be 289 and 900000, temporarily downgraded to check CI
lemma allC_289 : allC 289 := by
  prove_allC 900000
