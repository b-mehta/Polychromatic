import Polychromatic.FourThree

set_option linter.all false

set_option trace.debug true

-- should be 289 and 900000, temporarily downgraded to check CI
lemma allC_289 : allC 30 := by
  prove_allC 9000
