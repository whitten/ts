is_sumAnd(X) :-
  pcre:match('^and',X,R,one),
  \+ R == [].

is_conj(X) :-
  pcre:match('^conj',X,R,one),
  \+ R == [].

ok_argument(X) :-
  pcre:match('^conj',X,R,one),
  R == [].

proposition(Prop) :-
  arc(X,Y,R),
  is_sumAnd(X),
  is_conj(R),
  atom_concat(Y, ':', S),
  atom_concat(S, X, Prop).

proposition(Prop) :-
  arc(A,B,R),
  is_conj(R),
  \+ is_sumAnd(A),
  atom_concat(A,'[',P2),
  atom_concat(P2,R,P3),
  atom_concat(P3,'->',P4),
  atom_concat(P4,B,P5),
  atom_concat(P5,']',Prop).

/* argument relation */
proposition(Prop) :-
  arc(A,B,R),
  ok_argument(R),
  atom_concat(A,'[',P2),
  atom_concat(P2,R,P3),
  atom_concat(P3,'->',P4),
  atom_concat(P4,B,P5),
  atom_concat(P5,']',Prop).

print_list([]).
print_list([H|T]) :-
  write(H),
  write('.'),
  nl,
  print_list(T).

main :-
  setof(Pred, proposition(Pred), L),
  print_list(L).

