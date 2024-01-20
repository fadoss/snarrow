human(socrate) .
mortal(X) :- human(X) .
inmortal(X) :- mortal(X), !, fail(X) .
inmortal(X) .
