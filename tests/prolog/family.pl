mother(jane, mike) .
mother(sally, john) .
father(tom, sally) .
father(tom, erica) .
father(mike, john) .

sibling(X, Y) :- parent(Z, X), parent(Z, Y) .
parent(X, Y) :- father(X, Y) .
parent(X, Y) :- mother(X, Y) .
relative(X, Y) :- parent(X, Z), parent(Z, Y) .
relative(X, Y) :- sibling(X, Z), relative(Z, Y) .

distinct(X, X) :- !, fail(X) .
distinct(X, Y) .
