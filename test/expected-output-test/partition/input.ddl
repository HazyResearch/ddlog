a?(k int).
c?(k int).
d?(k int).
e?(k int).
f?(k int).
b(k int, p int, q text).

@partition(x)
@weight(x + y)
a(x) :- b(x,y,_).

@partition(y)
@weight("string")
c(x) :- b(x,y,_).

@weight(x, y)
d(x) :- b(x,y,_).

@weight(-10)
e(x) :- b(x,y,_).

@weight(-0.3)
f(x) :- b(x,y,_).