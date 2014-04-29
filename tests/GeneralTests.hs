import Test.Tasty
import Test.Tasty.QuickCheck

import General

tests = testGroup "GeneralTests"
    [ testProperty "alphaEq"    prop_alphaEq
    , testProperty "notAlphaEq" prop_notAlphaEq
    , testProperty "freeVars"   prop_freeVars
    , testProperty "allVars"    prop_allVars
    ]

main = defaultMain tests

