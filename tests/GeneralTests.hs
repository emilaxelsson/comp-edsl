import Test.Tasty
import Test.Tasty.QuickCheck

import General

tests = testGroup "GeneralTests"
    [ testProperty "alphaEqRefl"      prop_alphaEqRefl
    , testProperty "notAlphaEq"       prop_notAlphaEq
    , testProperty "freeVars"         prop_freeVars
    , testProperty "usedVars"         prop_usedVars
    , testProperty "allVars"          prop_allVars
    , testProperty "freshVars"        prop_freshVars
    , testProperty "freshVarsCompact" prop_freshVarsCompact
    , testProperty "renameUnique"     prop_renameUnique
    , testProperty "renameUniqueFree" prop_renameUniqueFree
    , testProperty "subst"            prop_subst
    , testProperty "matchRefl"        prop_matchRefl
    , testProperty "matchRename"      prop_matchRename
    , testProperty "noMatch"          prop_noMatch
    ]

main = defaultMain tests

