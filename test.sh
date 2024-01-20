#!/bin/sh
#
# Tests for the snarrow command
#

# Original narrowing vending machine
VENDING_MACHINE="./snarrow.py tests/narrowing-vending-machine.maude"
# Two vending machines in the same term (for testing matchrew and rewriting conditions)
TWO_MACHINES="./snarrow.py --module TWO-VENDING-MACHINES tests/narrowing-vending-machine.maude"
# Strategy definition on vending machines (for testing strategy definitions)
VENDING_STRAT="./snarrow.py --module VENDING-STRAT tests/narrowing-vending-machine.maude"
# Folding narrowing vending machine of the manual
FOLDING_MACHINE="./snarrow.py tests/folding-narrowing-vending-machine.maude"
# EqLog example of the JLAMP paper
EQLOG="./snarrow.py tests/evalLog-system-narrowing.maude"
# Prolog examples
PROLOG="./snarrow.py tests/prolog-examples.maude"
# apppend with Prolog
PROLOG_APPEND="./snarrow.py tests/prolog-append.maude"

$VENDING_MACHINE '< M q >' 'buy-a[M <- $]'
$VENDING_MACHINE '< M q >' 'buy-a ; buy-c ; buy-c'
$VENDING_MACHINE '< M q >' 'buy-a +' --max-sols 3
$VENDING_MACHINE '< M q >' 'buy-x'
$VENDING_MACHINE '< M q a >' 'buy-x'
$VENDING_MACHINE '< M q >' 'idle'
$VENDING_MACHINE '< M q >' 'match < $ q >' --no-unify-tests
$VENDING_MACHINE '< M q >' 'match < $ q >'
$VENDING_MACHINE '< M q >' 'match < $ >' # unifies because of equation
$VENDING_MACHINE '< M q >' 'match < empty >'
$VENDING_MACHINE '< M q >' 'amatch q'
$VENDING_MACHINE '< M q >' 'matchrew S:State by S:State using buy-a'
$VENDING_MACHINE '< M q >' 'buy-a ? buy-c : buy-c'
$VENDING_MACHINE '< M q >' 'match < $ q > ? buy-a : buy-c' --no-unify-tests
$VENDING_MACHINE '< M q >' 'match < $ q > ? buy-a : buy-c'

$TWO_MACHINES '< M:Marking $ >' 'buy-a[M <- $]'
$TWO_MACHINES '{< M:Marking q > | < M:Marking $ >}' 'matchrew {L | R} by L using buy-a, R using buy-c'

$TWO_MACHINES '{< M:Marking q > | < N:Marking $ >}' 'left{buy-a}'
$TWO_MACHINES '{< M:Marking q > | < N:Marking $ >}' 'pair{buy-a, buy-c}'
$TWO_MACHINES '{< M:Marking q > | < N:Marking $ >}' 'chain{buy-a, buy-c}'
$TWO_MACHINES '{< M:Marking q > | < M:Marking $ >}' 'pair{buy-a, buy-c}'

$TWO_MACHINES 'P:Pair' 'matchrew {< q > | < M >} by M using idle' --no-unify-matchrew
$TWO_MACHINES 'P:Pair' 'matchrew {< q > | < M >} by M using idle'
$TWO_MACHINES 'P:Pair' 'matchrew {< q M > | < M >} by M using idle'
$TWO_MACHINES 'P:Pair' 'matchrew {< q M > | < N:Marking >} by M using idle, N:Marking using idle'
$TWO_MACHINES '{< M:Marking q > | < M:Marking $ >}' 'matchrew {L | R} by L using buy-a, R using buy-c'
$TWO_MACHINES '{< M:Marking q > | < N:Marking $ >}' 'matchrew {L | L} by L using buy-a'

$VENDING_STRAT '< M q >' 'buy-many-a(10)'

$FOLDING_MACHINE '< M:Marking a c >' 'buy-a ; buy-c ; match < empty >' --no-unify-test
$FOLDING_MACHINE '< M:Marking a c >' 'buy-a ; buy-c ; match < empty >'
$FOLDING_MACHINE '< M:Marking a c >' 'buy-a ; buy-c[M <- empty]'
$FOLDING_MACHINE '< M:Marking a c >' 'all'

$EQLOG "< 'sibling('sally,'erica),nil >" "sibling"
$EQLOG "< 'sibling('sally,'erica),nil >" "(sibling | father | fact) * ; match < nil >"
$EQLOG "< 'sibling('sally,'erica),nil >" "sibling ; father[Y <- 'sally] ; fact ; father[Y <- 'erica] ; fact"
$EQLOG "< 'sibling(X,'erica),nil >" "sibling ; father[X <- 'tom, Y <- 'sally] ; fact ; father ; fact"
$EQLOG "< 'sibling(X,'erica),nil >" "(sibling | father | fact) * ; match < nil >"
$EQLOG "< 'sibling(X,'erica),nil >" "(sibling | mother | fact) * ; match < nil >"
$EQLOG "< 'sibling(X,Y),nil >" "(sibling | mother | fact) * ; match < nil >"
$EQLOG "< 'sibling(X,Y),nil >" "(sibling | father | fact) * ; match < nil >"
$EQLOG "< 'sibling(X,Y),nil >" "(sibling | father | mother | fact) * ; match < nil >"
$EQLOG "< 'sibling(X,Y),nil >" "all * ; match < nil >"
$EQLOG "< 'relative('jane,'john),nil >" "(father | mother | grandpa | fact) * ; match < nil >"
$EQLOG "< 'relative(X,'john),nil >" "(father | mother | grandpa | fact) * ; match < nil >"

# the following command does not terminate, as expected
#$EQLOG "< 'relative(X,'john),nil >" "all * ; match < nil >"

$PROLOG "< 'sibling('sally, 'erica) >" solve --module PROLOG-FAMILY
$PROLOG "< 'sibling(X, 'erica) >" solve --module PROLOG-FAMILY
$PROLOG "< 'parent(X, 'john) >" solve --module PROLOG-FAMILY
$PROLOG "< 'parent(X, 'tom) >" solve --module PROLOG-FAMILY
# $PROLOG "< 'relative(X, 'john) >" solve
$PROLOG "< 'mortal('socrate) >" solve --module PROLOG-SOCRATE
$PROLOG "< 'inmortal('poseidon) >" solve --module PROLOG-SOCRATE
$PROLOG "< 'inmortal('socrate) >" solve --module PROLOG-SOCRATE

$PROLOG_APPEND "< 'append('nil, 'nil, X) >" solve
$PROLOG_APPEND "< 'append('cons['a, 'nil], 'cons['b, 'nil], X) >" solve
$PROLOG_APPEND "< 'append('cons['a, 'nil], X, 'cons['a, 'cons['c, 'nil]]) >" solve
$PROLOG_APPEND "< 'append2('a · 'b, 'c · 'd, X) >" solve
$PROLOG_APPEND "< 'append2('a · X, Y · 'e, 'a · 'b · 'c · 'd · 'e) >" solve
$PROLOG_APPEND "< 'contains('v, 'u · 'v · 'w) >" solve
$PROLOG_APPEND "< 'contains(X, 'u · 'v · 'w) >" solve
$PROLOG_APPEND "< 'contains('u, X) >" solve
$PROLOG_APPEND "< 'reverse(empty, X) >" solve
$PROLOG_APPEND "< 'reverse('1 · '2 · '3, X) >" solve
