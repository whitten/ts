%   File   : ts.pl
%   Author : Alastair Butler
%   Purpose: Converts Normalised expressions into Target language expressions

:- import memberchk/2 from basics.
:- import append/3 from basics.
:- import length/2 from basics.

% intersection( +List1, +List2, ?Common )
% Common is unified with a list which contains the common elements of
% List1 and List2.
intersection( [], _, [] ).
intersection( [Head|L1tail], L2, L3 ) :-
  memberchk( Head, L2 ),
  !,
  L3 = [Head|L3tail],
  intersection( L1tail, L2, L3tail ).
intersection( [_|L1tail], L2, L3 ) :-
  intersection( L1tail, L2, L3 ).

% subtract( +List1, +List2, ?Remainder )
% Unifies Remainder with a list containing those elements of List1 which
% are not in List2.
subtract( [], _, [] ).
subtract( [Head|Tail], L2, L3 ) :-
  memberchk( Head, L2 ),
  !,
  subtract( Tail, L2, L3 ).
subtract( [Head|Tail1], L2, [Head|Tail3] ) :-
  subtract( Tail1, L2, Tail3 ).

% union( +List1, +List2, ?Union )
% Used to create the list of elements in List1 and not in List2, added to
% those in List2.
union( [], L, L ).
union( [Head|L1tail], L2, L3 ) :-
  memberchk( Head, L2 ),
  !,
  union( L1tail, L2, L3 ).
union( [Head|L1tail], L2, [Head|L3tail] ) :-
  union( L1tail, L2, L3tail ).

% delete(?list, ?term, ?list)
% delete(List1, Element, List2) removes all occurrences of Element in List1 to provide List2.
delete( [], _, [] ).
delete( [H|T], X, L ) :-
  H == X, !,
  delete( T, X, L ).
delete( [H|T], X, [H|L] ) :-
  delete( T, X, L ).

% replace( +List1, +Element, ?List2 )
% Used to create List2 that contains as many instances of Element as there
% are elements in List1.
replace( [], _, [] ).
replace( [_|L1tail], X, [X|L2tail] ):-
  replace( L1tail, X, L2tail ).

find_with_sub_atom( _, [], L, L ).
find_with_sub_atom( A, [H|T0], L, [H|T] ) :-
  sub_atom( H, _, _, _, A ),
  !,
  find_with_sub_atom( A, T0, L, T ).
find_with_sub_atom( A, [_|T0], L, T ) :-
  find_with_sub_atom( A, T0, L, T ).

%    A Normalised expression is a <normalised_term>, where
%        <normalised_term> ::=
%                 <sct_structure_mapping>
%              |  fresh( <fresh_list>, <normalised_term> )
%              |  local( <local_list>, <normalised_term> )
%              |  closure( <quantifier_operator>, <normalised_term>
%              |  pred( <relation_atom>, <normalised_term_list> )
%              |  some( <fresh_atom>, <discourse_referent>, <normalised_term>, <local_atom>, <normalised_term> )
%              |  someClassic_rest( <fresh_atom>, <discourse_referent>, <normalised_term>, <local_atom>, <normalised_term> )
%              |  someClassic( <fresh_atom>, <discourse_referent>, <local_atom>, <normalised_term> )
%              |  someFact( <fresh_atom>, <relation_atom>, <discourse_referent>, <normalised_term>, <local_atom>, <normalised_term> )
%              |  pick( <fresh_atom>, <sort_list>, <selection_atom>, <local_atom>, <normalised_term> )
%              |  pick_more( <fresh_atom>, <sort_list>, <selection_atom>, <local_atom>, <normalised_term> )
%              |  embed( <normalised_term> )
%              |  control( <normalised_term> )
%              |  control2( <normalised_term> )
%              |  connect( <relation_atom>, <normalised_term_list> )
%
%         <sct_structure_mapping> ::=
%                 t( <grammar_atom> )
%              |  at( <normalised_term>, <role_atom> )
%              |  mov( <grammar_atom>, <grammar_atom>, <normalised_term> )
%              |  namely( <discourse_referent>, <fresh_atom>, <sct_expr> )
%              |  bodyClimb( <fresh_atom>, <normalised_term> )
%
%        <fresh_list> ::=
%                 []
%              |  .( <fresh_atom>, <fresh_list> )
%
%        <local_list> ::=
%                 []
%              |  .( <local_atom>, <local_list> )
%
%        <sort_list> ::=
%                 []
%              |  .( <sort_atom>, <sort_list> )
%
%        <grammar_atom> ::=
%                 <fresh_atom>
%              |  <local_atom>
%              |  <context_atom>
%
%        <discourse_referent> ::=
%                 x( <sort_atom>, <integer> )
%              |  c( <sort_atom>, <constant_atom> )

%------------------------------------------------------------------------------%
% low level grammar building blocks
%------------------------------------------------------------------------------%

build_args( [], [] ).
build_args( [A0|As0], [at( t( A0 ), A0 )|As] ) :-
  build_args( As0, As ).

build_predicate( [], L, S, rel( [], [], S, Args ) ) :-
  build_args( L, Args ).
build_predicate( [H|T], L, S, ifThere( H, PredA, PredB ) ) :-
  build_predicate( T, [H|L], S, PredA ),
  build_predicate( T, L, S, PredB ).

make_subord( N, D, Ls, Keep, E, clean( N, Remove, D, E ) ) :-
  subtract( Ls, Keep, Remove ).

%------------------------------------------------------------------------------%
% transform Normalised expressions to SCT structures
%------------------------------------------------------------------------------%

transform_list( _, [], [] ).
transform_list( Env, [E0|T0], [E|T] ) :-
  transform( Env, E0, E ),
  transform_list( Env, T0, T ).

transform( _, t( X ), t( X ) ).

transform( Env, at( Norm, S ), at( E, S ) ) :-
  transform( Env, Norm, E ).

transform( Env, mov( X, Y, Norm ), mov( X, Y, E ) ) :-
  transform( Env, Norm, E ).

transform( Env, namely( DRef, X, Norm ), namely( DRef, X, E ) ) :-
  transform( Env, Norm, E ).

transform( Env, bodyClimb( V, Norm ), bodyClimb( V, E ) ) :-
  transform( Env, Norm, E ).

transform( env( _, _, D, Ls ), fresh( Fs, Norm ), E ) :-
  replace( Fs, D, Ds ),
  transform( env( Fs, Ds, D, Ls ), Norm, E ).

transform( env( Fs, Ds, D, _ ), local( Ls, Norm ), E ) :-
  transform( env( Fs, Ds, D, Ls ), Norm, E ).

transform( env( Fs, Ds, D, Ls ), closure( Oper, Norm ), head( Oper, Fs, body( Fs, E0 ) ) ) :-
  transform( env( Fs, Ds, D, Ls ), Norm, E0 ).

transform( env( Fs, Ds, D, Ls ), pred( S, Args ), P ) :-
  subtract( Ls, Args, Usable ),
  build_predicate( Usable, Args, S, P ).

transform( env( Fs, Ds, D, Ls ),
           some( V, DRef, R0, X, E0 ),
           namely( DRef, V,
                   mov( V, X,
                        rel( Fs, Ds,'',
                             [bodyClimb( V,
                                         mov( X, 'h', R ) )
                             ,E] ) ) )
         ) :-
  transform( env( Fs, Ds, D, Ls ), R0, R1 ),
  transform( env( Fs, Ds, D, Ls ), E0, E ),
  make_subord( 0, D, Ls, ['h'], clean( 1, ['h'], D, R1 ), R ).

transform( env( Fs, Ds, D, Ls ),
           someClassic_rest( V, DRef, R0, X, E0 ),
           headClimb( DRef, V,
                      mov( V, X,
                           rel( Fs, Ds, '',
                                [ bodyClimb( V,
                                             mov( X,'h',R ) )
                                , E] ) ) )
         ) :-
  transform( env( Fs, Ds, D, Ls ), R0, R1 ),
  transform( env( Fs, Ds, D, Ls ), E0, E ),
  make_subord( 0, D, Ls, ['h'], clean( 1, ['h'], D, R1 ), R ).

transform( env( Fs, Ds, D, Ls ),
           someClassic( V, DRef, X, E0 ),
           headClimb( DRef, V, mov( V, X, E ) )
         ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E ).

transform( env( Fs, Ds, D, Ls ),
           someFact( V, S, DRef, R0, X, E0 ),
           headClimb( DRef, V,
                      mov( V, X,
                           rel( Fs, Ds, '',
                                [bodyClimb( V,
                                            rel( [], [], S,
                                                 [at( t( X ), 'h' )
                                               ,
                                                 at( mov( X,'',R ), 'emb' ) ] )
                                          )
                              , E] ) ) )
         ) :-
  transform( env( Fs, Ds, D, Ls ), R0, R ),
  transform( env( Fs, Ds, D, Ls ), E0, E ).

transform( env( Fs, Ds, D, Ls ),
           pick( V, Sorts, S, X, E0 ),
           rel( [], [], '&', [bodyClimb( V, pick( S, t( X ), [D], Sorts )), E] )    % discourse bindings
         ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E ).

transform( env( Fs, Ds, D, Ls ),
           pick_more( V, Sorts, S, X, E0 ),
           rel( [], [], '&', [bodyClimb( V, pick( S, t( X ), Sources, Sorts )), E] )
         ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E ),
  subtract( [D|Ls], [X], Sources ).                                 % discourse and local bindings

transform( env( Fs, Ds, D, Ls ), embed( E0 ), E ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E1 ),
  make_subord( 0, D, Ls, [], E1, E ).

transform( env( Fs, Ds, D, Ls ), control( E0 ), E ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E1 ),
  find_with_sub_atom('arg2', Ls, [], C1),
  find_with_sub_atom('obu', Ls, C1, C2),
  find_with_sub_atom('arg1', Ls, C2, C3),
  find_with_sub_atom('arg0', Ls, C3, C4),
  intersection( ['h'], Ls, C5),
  append(C5, C4, Candidates),
  make_subord( 0, D, Ls, Candidates, clean( 1, ['arg0'], D, E1 ), E2 ),
  make_subord( 0, 'arg0', Candidates, [], E2, E ).

transform( env( Fs, Ds, D, Ls ), control2( E0 ), E ) :-
  transform( env( Fs, Ds, D, Ls ), E0, E1 ),
  find_with_sub_atom('arg0', Ls, [], Candidates),
  make_subord( 0, D, Ls, Candidates, clean( 1, ['arg0'], D, E1 ), E2 ),
  make_subord( 0, 'arg0', Candidates, [], E2, E ).

transform( env( Fs, Ds, D, Ls ), connect( S, Es0 ), rel( Fs, Ds, S, Es ) ) :-
  transform_list( env( Fs, Ds, D, Ls ), Es0, Es ).

%    An SCT expression is an <sct_expr>, where
%        <sct_expr> ::=
%                 <drs_structure_mapping>
%              |  namely( <discourse_referent>, <fresh_atom>, <sct_expr> )
%              |  <sct_term>
%              |  at( <sct_expr>, <role_atom> )
%              |  rel( <fresh_list>, <context_list>, <relation_atom>, <sct_expr_list> )
%              |  ifThere( <grammar_atom>, <sct_expr>, <sct_expr> )
%              |  mov( <grammar_atom>, <grammar_atom>, <sct_expr> )
%              |  clean( <integer>, <local_list>, <context_atom>, <sct_expr> )
%              |  pick( <selection_atom>, <sct_term>, <sources_list>, <sort_list> )
%
%        <drs_structure_mapping> ::=
%                 head( <quantifier_operator>, <fresh_list>, <sct_expr> )
%              |  body( <fresh_list>, <sct_expr> )
%              |  headClimb( <discourse_referent>, <fresh_atom>, <sct_expr> )
%              |  bodyClimb( <fresh_atom>, <sct_expr> )
%
%        <sct_term> ::= t( <grammar_atom> )
%
%        <sct_expr_list> ::=
%                 []
%              |  .( <sct_expr>, <sct_expr_list> )
%
%        <context_list> ::=
%                 []
%              |  .( <context_atom>, <context_list> )
%
%        <sources_list> ::=
%                 []
%              |  .( <local_atom>, <sources_list> )
%              |  .( <context_atom>, <sources_list> )

%------------------------------------------------------------------------------%
% operations on incomplete lists
%------------------------------------------------------------------------------%

length_il( List, Length ) :-                % use auxiliary predicate ...
  length_il_acc( List, 0, Length ).         % ... with count initialised to zero

length_il_acc( L, N0, N ) :- var( L ), !, N = N0.            % reached end, stop
length_il_acc( [_|L], N, Length ) :-
  N1 is N+1,
  length_il_acc( L, N1, Length ).

last_il( [X|Xs], Ys, Z ) :-                 % use auxiliary predicate ...
  last_il_lag( Xs, Ys, X, Z ).              % ... which lags behind by one item

last_il_lag( X0, X, Z0, Z ) :- var( X0 ), !, X = X0, Z = Z0. % reached end, stop
last_il_lag( [X1|Xs], [X0|Ys], X0, Z ) :-
  last_il_lag( Xs, Ys, X1, Z ).                              % lag behind by one

append_il( L, Z0, Z ) :- var( L ), !, Z = Z0.                % reached end, stop
append_il( [H|T], Z0, [H|Z] ) :-
  append_il( T, Z0, Z ).

%------------------------------------------------------------------------------%
% collect discourse referents with a difference list
%------------------------------------------------------------------------------%

discourse_refs_from_list( _, [], D-D ).
discourse_refs_from_list( X, [E|T], D-D0 ) :-
  discourse_refs( X, E, D1-D0 ),
  discourse_refs_from_list( X, T, D-D1 ).

discourse_refs( X, head( _, Vs, E ), Ds ) :-
  ( memberchk( X, Vs ) ->
    Ds = D-D
  ;
    discourse_refs( X, E, Ds )
  ).
discourse_refs( X, body( _, E ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( X, headClimb( _, _, E ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( X, bodyClimb( _, E ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( X, namely( DRef, Y, E ), Ds ) :-
  ( X == Y ->
    discourse_refs( X, E, D-D0 ),
    Ds = [DRef|D]-D0
  ;
    discourse_refs( X, E, Ds )
  ).
discourse_refs( _, t( _ ), D-D ).
discourse_refs( X, at( E, _ ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( X, rel( _, _, _, Es ), Ds ) :-
  discourse_refs_from_list( X, Es, Ds ).
discourse_refs( X, ifThere( _, E1, E2 ), Ds ) :-
  discourse_refs( X, E1, Ds ),
  discourse_refs( X, E2, Ds ).
discourse_refs( X, mov( _, _, E ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( X, clean( _, _, _, E ), Ds ) :-
  discourse_refs( X, E, Ds ).
discourse_refs( _, pick( _, _, _, _ ), D-D ).

%------------------------------------------------------------------------------%
%   Storing <discourse_referent>s
%
%   An ASSIGNMENT has the form of an ordered list of assignments
%   of the form map( <grammar_atom>, <discourse_referent_difference_list> ),
%   where <grammar_atom> serves as an ordering key.  If the ASSIGNMENT
%   list is empty then the assignment is the empty assignment ( that is,
%   the empty difference list ).
%------------------------------------------------------------------------------%

assignment_update( X, Ds, Assn0, Assn ) :-
  Assn = [map( X, Ds )|Assn0].

val( Assn, X, Ds ) :-
  ( memberchk( map( X, Ds0 ), Assn ) ->
    Ds = Ds0
  ;
    Ds = D-D                     % otherwise return the empty difference list
  ).

contentful_val( Assn, X, D-D0 ) :-
  memberchk( map( X, D-D0 ), Assn ),
  D \== D0.                      % assigned difference list must be non-empty

push( New-D, X, Assn0, Assn ) :-
  val( Assn0, X, D-Old ),
  assignment_update( X, New-Old, Assn0, Assn ).

pop( X, Assn0, Assn ) :-
  contentful_val( Assn0, X, [_|D]-D0 ),
  assignment_update( X, D-D0, Assn0, Assn ).

shift( X, Y, Assn0, Assn ) :-
  contentful_val( Assn0, X, [DRef|DX]-DX0 ),
  assignment_update( X, DX-DX0, Assn0, Assn1 ),
  val( Assn0, Y, DY-DY0 ),
  assignment_update( Y, [DRef|DY]-DY0, Assn1, Assn ).

shift_last( X, Y, Assn0, Assn ) :-
  contentful_val( Assn0, X, DX1-DX0 ),
  last_il( DX1, DX, DRef ),
  assignment_update( X, DX-DX0, Assn0, Assn1 ),
  val( Assn0, Y, DY-DY0 ),
  assignment_update( Y, [DRef|DY]-DY0, Assn1, Assn ).

split( 1, [_|T], [], T ) :- !.
split( N, [H|T], [H|Past], Future ) :-
  M is N - 1,
  split( M, T, Past, Future ).

do_pop( [], _, Assn, Assn ).
do_pop( [_|T], X, Assn0, Assn ):-
  pop( X, Assn0, Assn1 ),
  do_pop( T, X, Assn1, Assn ).

do_shift_last( [], _, _, Assn, Assn ).
do_shift_last( [_|T], X, Y, Assn0, Assn ):-
  shift_last( X, Y, Assn0, Assn1 ),
  do_shift_last( T, X, Y, Assn1, Assn ).

allocate( _, [], [], _, Assn, Assn ).
allocate( N, [X|FNs], [Y|CNs], Es, Assn0, Assn ) :-
  split( N, Es, Past, Future ),
  % the future
  discourse_refs_from_list( X, Future, FutureDRefs-[] ),
  % the past
  discourse_refs_from_list( X, Past, PastDRefs-[] ),
  % remove the future
  do_pop( FutureDRefs, X, Assn0, Assn1 ),
  % contextualise the past
  do_shift_last( PastDRefs, X, Y, Assn1, Assn2 ),
  % move to next allocate changes
  allocate( N, FNs, CNs, Es, Assn2, Assn ).

n_shift_last( N, _, _, Assn, Assn ) :-
  N =< 0.
n_shift_last( N, X, Y, Assn0, Assn ):-
  N > 0,
  shift_last( X, Y, Assn0, Assn1 ),
  C is N - 1,
  n_shift_last( C, X, Y, Assn1, Assn ).

dispose( _, [], _, Assn, Assn ).
dispose( N, [X|T], Y, Assn0, Assn ) :-
  val( Assn0, X, D-_ ),
  length_il( D, M ),
  C is M - N,
  n_shift_last( C, X, Y, Assn0, Assn1 ),
  dispose( N, T, Y, Assn1, Assn ).

%------------------------------------------------------------------------------%
% semantic calculation
%------------------------------------------------------------------------------%

binding_filter( L, Z0, Z ) :- var( L ), !, Z = Z0.      % reached end, stop
binding_filter( [X|L], Z0, Z ) :-
  ( X = x( _, _ ) ->
    Z1 = [X|Z0]
  ;
    Z1 = Z0
  ),
  binding_filter( L, Z1, Z ).

change_assignment( [], _, Assn, Assn, Bds, Bds ).
change_assignment( [X|T], E, Assn0, Assn, Bds0, Bds ):-
  discourse_refs( X, E, D-D0 ),
  push( D-D0, X, Assn0, Assn1 ),
  binding_filter( D, Bds0, Bds1 ),
  change_assignment( T, E, Assn1, Assn, Bds1, Bds ).

calculate_list( _, _, _, _, _, [], [] ).
calculate_list( Assn0, N, Xs, Ys, Es, [E|T0], [Target|T] ) :-
  I is N + 1,
  allocate( I, Xs, Ys, Es, Assn0, Assn ),
  calculate( Assn, E, Target ),
  calculate_list( Assn0, I, Xs, Ys, Es, T0, T ).

calculate( Assn0, head( Oper, Vs, E ), head( Oper, Vs, Bds, Target ) ) :-
  change_assignment( Vs, E, Assn0, Assn, [], Bds ),
  calculate( Assn, E, Target ).
calculate( Assn, body( Vs, E ), body( Vs, Target ) ) :-
  calculate( Assn, E, Target ).
calculate( Assn0, headClimb( DRef, X, E ), headClimb( DRef, X, Target ) ) :-
  push( [DRef|R]-R, X, Assn0, Assn ),
  calculate( Assn, E, Target ).
calculate( Assn, bodyClimb( X, E ), bodyClimb( X, Target ) ) :-
  calculate( Assn, E, Target ).
calculate( Assn, namely( _, _, E ), Target ) :-
  calculate( Assn, E, Target ).
calculate( Assn, t( X ), DRef ) :-
  memberchk( map( X, [DRef|_]-_ ), Assn ).
calculate( Assn, at( E, S ), at( Target, S ) ) :-
  calculate( Assn, E, Target ).
calculate( Assn, rel( Xs, Ys, S, Es ), rel( S, Ts ) ) :-
  calculate_list( Assn, 0, Xs, Ys, Es, Es, Ts ).
calculate( Assn, ifThere( X, E1, E2 ), Target ) :-
  ( contentful_val( Assn, X, _ ) ->
    calculate( Assn, E1, Target )
  ;
    calculate( Assn, E2, Target )
  ).
calculate( Assn0, mov( X, Y, E ), Target ) :-
  shift( X, Y, Assn0, Assn ),
  calculate( Assn, E, Target ).
calculate( Assn0, clean( N, Xs, Y, E ), Target ) :-
  dispose( N, Xs, Y, Assn0, Assn ),
  calculate( Assn, E, Target ).
calculate( Assn, pick( S, E, Sources, Sorts ), rel( S, [DRef|Resolved] ) ) :-
  calculate( Assn, E, DRef ),
  collect_context( Sources, Assn, [], Context ),
  antecedents( Sorts, Context, Resolved-[] ).

collect_context( [], _, Context, Context ).
collect_context( [X|Sources], Assn, Context0, Context ) :-
  val( Assn, X, D-_ ),
  append_il( D, Context0, Context1 ),
  collect_context( Sources, Assn, Context1, Context ).

antecedents( _, [], R-R ).
antecedents( Sorts, [x( S, I )|Context], [x( S, I )|R]-R0 ) :-
  memberchk( S, Sorts ), !,
  antecedents( Sorts, Context, R-R0 ).
antecedents( Sorts, [c( S, C )|Context], [c( S, C )|R]-R0 ) :-
  memberchk( S, Sorts ), !,
  antecedents( Sorts, Context, R-R0 ).
antecedents( Sorts, [_|Context], R-R0 ) :-
  antecedents( Sorts, Context, R-R0 ).

%    A Target language expression is a <target_expr>, where
%        <target_expr> ::=
%                 <discourse_referent>
%              |  rel( <relation_atom>, <target_expr_list> )
%              |  at( <target_expr>, <role_atom> )
%              |  quant( <quantifier_operator>, <bound_list>, <target_expr> )
%              |  <drs_expr>
%
%        <target_expr_list> ::=
%                 []
%              |  .( <target_expr>, <target_expr_list> )
%
%        <bound_list> ::=
%                 []
%              |  .( x( <sort_atom>, <integer> ), <bound_list> )
%
%        <drs_expr> ::=
%                 head( <quantifier_operator>, <fresh_list>, <bound_list>, <target_expr> )
%              |  body( <fresh_list>, <target_expr> )
%              |  headClimb( <discourse_referent>, <fresh_atom>, <target_expr> )
%              |  bodyClimb( <fresh_atom>, <target_expr> )
%

%------------------------------------------------------------------------------%
% post calculate repositioning of Target expression material
%------------------------------------------------------------------------------%

collect_bindings_from_target_list( _, [], C, C ).
collect_bindings_from_target_list( X, [Target|T], C0, C ):-
  collect_bindings( X, Target, C0, C1 ),
  collect_bindings_from_target_list( X, T, C1, C ).

collect_bindings_from_binding_list( [], _, C, C ).
collect_bindings_from_binding_list( [X|T], Target, C0, C ):-
  collect_bindings( X, Target, C0, C1 ),
  collect_bindings_from_binding_list( T, Target, C1, C ).

collect_bindings( X, rel( _, Targets ), C0, C ) :-
  collect_bindings_from_target_list( X, Targets, C0, C ).
collect_bindings( X, quant( _, _, Target ), C0, C ) :-
  collect_bindings( X, Target, C0, C ).
collect_bindings( X, at( Target, _ ), C0, C ) :-
  collect_bindings( X, Target, C0, C ).
collect_bindings( X, head( _, Vs, _, Target ), C0, C ) :-
  ( memberchk( X, Vs ) ->
    C = C0
  ;
    collect_bindings( X, Target, C0, C )
  ).
collect_bindings( X, body( _, Target ), C0, C ) :-
  collect_bindings( X, Target, C0, C ).
collect_bindings( X, headClimb( DRef, Y, Target ), C0, C ) :-
  ( X == Y, DRef = x(_, _) ->
    C1 = [DRef|C0],
    collect_bindings( X, Target, C1, C )
  ;
    collect_bindings( X, Target, C0, C )
  ).
collect_bindings( X, bodyClimb( _, Target ), C0, C ) :-
  collect_bindings( X, Target, C0, C ).
collect_bindings( _, x( _, _ ), C, C ).
collect_bindings( _, c( _, _ ), C, C ).

collect_conditions_from_binding_list( [], _, C, C ).
collect_conditions_from_binding_list( [X|T], Target, C0, C ):-
  collect_conditions( X, Target, C0, C1 ),
  collect_conditions_from_binding_list( T, Target, C1, C ).

collect_conditions_from_target_list( _, [], C, C ).
collect_conditions_from_target_list( X, [H|T], C0, C ):-
  collect_conditions( X, H, C0, C1 ),
  collect_conditions_from_target_list( X, T, C1, C ).

collect_conditions( X, rel( _, Targets ), C0, C ) :-
  collect_conditions_from_target_list( X, Targets, C0, C ).
collect_conditions( X, quant( _, _, Target ), C0, C ) :-
  collect_conditions( X, Target, C0, C ).
collect_conditions( X, at( Target, _ ), C0, C ) :-
  collect_conditions( X, Target, C0, C ).
collect_conditions( X, head( _, _, _, Target ), C0, C ) :-
  collect_conditions( X, Target, C0, C ).
collect_conditions( X, body( Vs, Target ), C0, C ) :-
  ( memberchk( X, Vs ) ->
    C = C0
  ;
    collect_conditions( X, Target, C0, C )
  ).
collect_conditions( X, headClimb( _, _, Target ), C0, C ) :-
  collect_conditions( X, Target, C0, C ).
collect_conditions( _, bodyClimb( _, rel( '', [at( _, 'h' )] ) ), C0, C ) :- !, C = C0.  % remove empty relation
collect_conditions( X, bodyClimb( Y, Target ), C0, C ) :-
  ( X == Y ->
    reposition_to_list( Target, C0, C1 ),
    collect_conditions( X, Target, C1, C )
  ;
    collect_conditions( X, Target, C0, C )
  ).
collect_conditions( _, x( _, _ ), C, C ).
collect_conditions( _, c( _, _ ), C, C ).

single_content( [Target0], Target ) :- !,
  Target = Target0.
single_content( Target, rel( '', Target ) ).

reposition( Target0, Target ) :-
  reposition_to_list( Target0, [], Targets ),
  single_content( Targets, Target ).

reposition_list_to_list( [], C, C ).
reposition_list_to_list( [Target|T], C0, C ) :-
  reposition_to_list( Target, C0, C1 ),
  reposition_list_to_list( T, C1, C ).

reposition_list_to_list_extra( [], C, C ).
reposition_list_to_list_extra( [Target|T], C0, C ) :-
  reposition_to_list( Target, [], C1 ),
  append( C0, C1, C2 ),
  reposition_list_to_list_extra( T, C2, C ).

reposition_to_list( rel( '', Targets ), C0, C ) :- !,
  reposition_list_to_list( Targets, [], ColOut ),
  (
    (
      memberchk( at( _, _ ), Targets )
    ;
      memberchk( x( _, _ ), Targets )
    ;
      memberchk( c( _, _ ), Targets )
    ) ->
    C = [rel( '', ColOut )|C0]
  ;
    append( ColOut, C0, C )
  ).
reposition_to_list( rel( S, TargetsIn ), C, [rel( S, TargetsOut )|C] ) :-
  reposition_list_to_list_extra( TargetsIn, [], TargetsOut ).
reposition_to_list( quant( S, [], Target0 ), C0, C ) :- !,
  ( memberchk( S, ['exists', 'forall'] ) ->
    reposition_to_list( Target0, C0, C )
  ;
    reposition( Target0, Target ),
    C = [quant( S, [], Target )|C0]
  ).
reposition_to_list( quant( S, Bds, Target0 ), C, [quant( S, Bds, Target )|C] ) :-
  reposition( Target0, Target ).
reposition_to_list( at( Target0, S ), C, [at( Target, S )|C] ) :-
  reposition( Target0, Target ).
reposition_to_list( head( S, Vs, Bds, Target0 ), C0, C ) :-
  collect_bindings_from_binding_list( Vs, Target0, Bds, Bindings ),
  ( Bindings == [], memberchk( S, ['exists', 'forall'] ) ->
    reposition_to_list( Target0, C0, C )
  ;
    reposition( Target0, Target ),
    C = [quant( S, Bindings, Target )|C0]
  ).
reposition_to_list( body( Vs, Target0 ), C0, C ) :-
  reposition( Target0, Target ),
  collect_conditions_from_binding_list( Vs, Target0, [Target|C0], C ).
reposition_to_list( headClimb( _, _, Target ), C0, C ) :-
  reposition_to_list( Target, C0, C ).
reposition_to_list( bodyClimb( _, _ ), C, C ).
reposition_to_list( x( Sort, I ), C, [x( Sort, I )|C] ).
reposition_to_list( c( Sort, S ), C, [c( Sort, S )|C] ).

%    A Processed language expression is a <processed_expr>, where
%        <processed_expr> ::=
%                 <discourse_referent>
%              |  connect( <relation_atom>, <processed_expr_list> )
%              |  pred( <relation_atom>, <processed_expr_list> )
%              |  test( <discourse_referent_list> )
%              |  at( <target_expr>, <role_atom> )
%              |  quant( <quantifier_operator>, <bound_list>, <target_expr> )
%
%        <processed_expr_list> ::=
%                 []
%              |  .( <processed_expr>, <processed_expr_list> )

%------------------------------------------------------------------------------%
% postprocessing Target expression
%------------------------------------------------------------------------------%

postprocess_list(_, [], []).
postprocess_list(Env, [E|Tail], Rest) :-
  E = rel( '', [at( _, 'h' )] ),
  !,
  postprocess_list(Env, Tail, Rest).
postprocess_list(Env, [E|Tail], Rest) :-
  (
    E = x('DUMMY', _) ; E = c('DUMMY', _)
  ;
    E = at(x('DUMMY', _), _) ; E = at(c('DUMMY', _), _)
  ),
  !,
  postprocess_list(Env, Tail, Rest).
postprocess_list(Env, [E0|Tail], [E|Rest]) :-
  postprocess(Env, E0, E),
  postprocess_list(Env, Tail, Rest).

postprocess_binding_list(_, [], []).
postprocess_binding_list(Env, [E|Tail], Rest) :-
  (
    E = x('FRAG', _) ; E = c('FRAG', _)
  ;
    E = x('DUMMY', _) ; E = c('DUMMY', _)
  ;
    E = at(x('DUMMY', _), _) ; E = at(c('DUMMY', _), _)
  ),
  !,
  postprocess_binding_list(Env, Tail, Rest).
postprocess_binding_list(Env, [E0|Tail], [E|Rest]) :-
  postprocess(Env, E0, E),
  postprocess_binding_list(Env, Tail, Rest).

postprocess(_, x(Sort, I), x(Sort, I)).
postprocess(_, c(Sort, Name), c(Sort, Name)).
postprocess(Env, at(E0, L), at(E, L)) :-
  postprocess(Env, E0, E).
postprocess(_, quant(Q, B0, E0), quant(Q, B, E)) :-
  postprocess_binding_list(Q, B0, B),
  postprocess(Q, E0, E).
postprocess(Env, rel(R, L0), test(R, L)) :-
  (
    memberchk(x(_, _), L0)
  ;
    memberchk(c(_, _), L0)
  ),
  !,
  postprocess_list(Env, L0, L).
postprocess(Env, rel(R, L0), pred(R, L)) :-
  memberchk(at(Lgs, 'lgs'), L0),
  !,
  delete(L0, at(Lgs, 'lgs'), L1),
  (
    memberchk(at(Arg0, 'arg0'), L1) ->
    delete(L1, at(Arg0, 'arg0'), L2),
    (
      memberchk(at(_, 'arg1'), L2) ->
      L3 = [at(Arg0, 'arg2')|L2]
    ;
      L3 = [at(Arg0, 'arg1')|L2]
    )
  ;
    L3 = L1
  ),
  postprocess_list(Env, [at(Lgs, 'arg0')|L3], L).
postprocess(Env, rel(R, L0), pred(R, L)) :-
  (
    memberchk(at(_, 'cat'), L0)
  ;
    memberchk(at(_, 'seq'), L0)
  ),
  memberchk(at(Arg0, 'arg0'), L0),
  !,
  delete(L0, at(Arg0, 'arg0'), L1),
  postprocess_list(Env, L1, L).
postprocess(Env, rel(R, L0), pred(R, L)) :-
  memberchk(at(_, _), L0),
  !,
  postprocess_list(Env, L0, L).
postprocess(Env, rel('', L0), connect(R, L)) :-
  !,
  connective(Env, R),
  postprocess_list(Env, L0, L).
postprocess(Env, rel(R, L0), connect(R, L)) :-
  postprocess_list(Env, L0, L).

connective('exists', '&') :- !.
connective('forall', 'cnd_') :- !.
connective(_, 'unk_').

%------------------------------------------------------------------------------%
% flatten postprocessed expression
%------------------------------------------------------------------------------%

flatten_post_list([], []).
% removes any darg1 argument
flatten_post_list([at(_, 'darg1')|T0], T) :-
  !,
  flatten_post_list(T0, T).
flatten_post_list([test(_, [])|T0], T) :-
  !,
  flatten_post_list(T0, T).
flatten_post_list([H0|T0], [H|T]) :-
  flatten_post(H0, H),
  flatten_post_list(T0, T).

flatten_post(connect('&', [E0]), E) :-
  !,
  flatten_post(E0, E).
flatten_post(quant(Q, B, E0), quant(Q, B, E)) :-
  !,
  flatten_post(E0, E).
flatten_post(connect(R0, L0), connect(R1, STRUC)) :-
  sub_atom(R0, 0, 9, _, 'scon_cnd_'),
  append(L1, [connect(R1, L2)], L0),
  sub_atom(R1, 0, 9, _, 'scon_cnd_'),
  !,
  append(L1, L2, L3),
  flatten_post_list(L3, L4),
  append(L5, [Last], L4),
  length(L5, N),
  (
    N > 1 ->
    STRUC = [connect('&', L5), Last]
  ;
    STRUC = L4
  ).
flatten_post(connect(R, L0), connect(R, STRUC)) :-
  sub_atom(R, 0, 9, _, 'scon_cnd_'),
  !,
  flatten_post_list(L0, L1),
  append(L2, [Last], L1),
  length( L2, N ),
  (
    N > 1 ->
    STRUC = [connect('&', L2), Last]
  ;
    STRUC = L1
  ).
flatten_post(connect(R0, L0), connect(R1, STRUC)) :-
  sub_atom(R0, 0, 4, _, 'unk_'),
  append(L1, [connect(R1, L2)], L0),
  sub_atom(R1, 0, 4, _, 'unk_'),
  !,
  append(L1, L2, L3),
  flatten_post_list(L3, L4),
  append(L5, [Last], L4),
  length(L5, N),
  (
    N > 1 ->
    STRUC = [connect('&', L5), Last]
  ;
    STRUC = L4
  ).
flatten_post(connect(R, L0), connect(R, STRUC)) :-
  sub_atom(R, 0, 4, _, 'unk_'),
  !,
  flatten_post_list(L0, L1),
  append(L2, [Last], L1),
  length( L2, N ),
  (
    N > 1 ->
    STRUC = [connect('&', L2), Last]
  ;
    STRUC = L1
  ).
flatten_post(connect(R, L0), connect(R, L)) :-
  !,
  flatten_post_list(L0, L).
flatten_post(pred(R, L0), pred(R, L)) :-
  !,
  flatten_post_list(L0, L).
flatten_post(at(E0, L), at(E, L)) :-
  !,
  flatten_post(E0, E).
flatten_post(A, A).

%------------------------------------------------------------------------------%
% change connect
%------------------------------------------------------------------------------%

change_connect_conj(_, _, [], []).
change_connect_conj(Num, Head, [H0|T0], [at(H, Conj)|T]) :-
  change_connect(H0, H),
  number_codes(Num, CharNum),
  atom_codes(AtomNum, CharNum),
  atom_concat( 'conj', AtomNum, Conj),
  NewNum is Num + 1,
  change_connect_conj(NewNum, Head, T0, T).

change_connect_list([], []).
change_connect_list([H0|T0], [H|T]) :-
  change_connect(H0, H),
  change_connect_list(T0, T).

change_connect(connect('&', L0), connect('&', L)) :- !,
  change_connect_list(L0, L).
change_connect(connect(R, L0), pred(R, [at(Head, 'h')|L])) :-
  Head = c('CONJ', R),
  change_connect_conj(1, Head, L0, L).
change_connect(pred(R, L0), pred(R,L)) :-
  change_connect_list(L0, L).
change_connect(test(R, L), test(R, L)).
change_connect(at(X0, L), at(X, L)) :-
  change_connect(X0, X).
change_connect(quant(Q, B, E0), quant(Q, B, E)) :-
  change_connect(E0, E).
change_connect(x(S,I), x(S,I)).
change_connect(c(S,C), c(S,C)).

%------------------------------------------------------------------------------%
% TPTP output of Target language expressions without extensions
%------------------------------------------------------------------------------%

runtotptp( Target, ID ) :-
  write( 'fof(' ),
  write( ID ),
  write( ',axiom,' ),
  totptp( Target, 2 ),
  nl,
  write( ').\n\n' ).

boundtptp( [] ).
boundtptp( [X|Bds] ) :-
  write( ',' ),
  termtotptp(X),
  boundtptp(Bds).

do_totptp( _, [], _ ).
do_totptp( S, [H|T], Column ):-
  nl,
  tab(Column),
  write( S ),
  NextColumn is Column+2,
  totptp( H, NextColumn ),
  do_totptp( S, T, Column ).

tohead([], Head, Head, []).
tohead([H|T], _, Y, R) :-
  H = at(X, 'h'), !,
  tohead(T, X, Y, R).
tohead([H|T], _, Y, R) :-
  H = at(X, '.event'), !,
  tohead(T, X, Y, R).
tohead([H|T], X, Y, [H|R]) :-
  tohead(T, X, Y, R).

do_link_totptp([], _, _).
do_link_totptp([at(X, Link)|T], Column, Head) :-
  (
    X = c(_, _)
  ;
    X = x(_, _)
  ), !,
  nl,
  tab(Column),
  write( '& ' ),
  write( Link ),
  write( '(' ),
  termtotptp( Head ),
  write( ') = ' ),
  termtotptp( X ),
  do_link_totptp(T, Column, Head).
do_link_totptp([at(X, Link)|T], Column, Head) :-
  X = pred(_, Targets), !,
  tohead(Targets, none, NewHead, _),
  nl,
  tab(Column),
  write( '& ' ),
  write( Link ),
  write( '(' ),
  termtotptp( Head ),
  write( ') = ' ),
  termtotptp( NewHead ),
  NextColumn is Column+2,
  nl,
  tab(Column),
  write( '&' ),
  totptp( X, NextColumn ),
  do_link_totptp(T, Column, Head).

totptp( pred( S, [X] ), _Column ) :-
  tohead([X], none, Head, []), !,
  write( ' isA(' ),
  termtotptp( Head ),
  write( ',' ),
  write( S ),
  write( ')' ).

totptp( pred( S, Targets ), Column ) :-
  tohead(Targets, none, Head, Rest),
  write( ' (' ),
  write( ' isA(' ),
  termtotptp( Head ),
  write( ',' ),
  write( S ),
  write( ')' ),
  do_link_totptp( Rest, Column, Head ),
  write( ' )' ).

totptp( connect( '&', [H|Targets] ), Column ) :- !,
  nl,
  tab(Column),
  write( '(' ),
  NextColumn is Column+2,
  totptp( H, NextColumn ),
  do_totptp( '&', Targets, Column ),
  write( ' )' ).

totptp( quant( 'exists', [X|Bds], Target ), Column ) :-
  nl,
  tab(Column),
  write( '? [' ),
  termtotptp( X ),
  boundtptp( Bds ),
  write( ']:' ),
  totptp( Target, Column ).

totptp( test( _S, [X,Y|More] ), Column ) :-
  nl,
  tab(Column),
  write( '( ' ),
  termtotptp(X),
  write(' = '),
  termtotptp(Y),
  linkstptp(X, More, Column),
  write( ' )' ).

totptp( test( S, [X]), _) :-
  write( ' isA(' ),
  termtotptp( X ),
  write( ',' ),
  write( S ),
  write( ')' ).

termtotptp( x( Sort, I ) ) :-
  write( Sort ),
  write( 'X' ),
  write( I ).
termtotptp( c( Sort, Name ) ) :-
  write( 'c' ),
  write( Sort ),
  write( 'Sort' ),
  write( Name ).

linkstptp(_, [], _).
linkstptp(X, [H|T], Column) :-
  nl,
  tab(Column),
  write( ' | ' ),
  termtotptp(X),
  write(' = '),
  termtotptp(H),
  linkstptp(X, T, Column).

%------------------------------------------------------------------------------%
% Main run routine
%------------------------------------------------------------------------------%

do_it( Id, Norm ) :-
  transform( env( [], [], '*', [] ), Norm, E ),
  calculate( [], E, Target0 ),
  reposition( Target0, Target ),
  postprocess( 'exists', Target, Post ),
  flatten_post( Post, Flat ),
  change_connect( Flat, Final ),
  runtotptp( Final, Id ).

