member(X, cons(X, Y)) .
member(X, cons(Y, Z)) :- member(X, Z) .
intersect(cons(X, Y), Z) :- member(X, Z) .
intersect(cons(X, Y), Z) :- intersect(Y, Z) .
disjoint(X, Y) :- \+(intersect(X, Y)) .
