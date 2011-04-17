sublist([], []).
sublist([H | Tail1], [H | Tail2]) :-
	sublist(Tail1, Tail2).
sublist(H, [_ | Tail]) :-
	sublist(H, Tail).

less(X, X, _).
less(X, Z, RelationList) :- 
	member([X,Z], RelationList).
less(X, Z, RelationList) :- 
	member([X,Y], RelationList),
	less(Y, Z, RelationList),
	\+less(Z, X, RelationList).

lessList(X, LessList, RelationList) :-
	findall(Y, less(X, Y, RelationList), List),
	list_to_set(List, L),
	sort(L, LessList), !.

bigList(X, LessList, RelationList) :-
	findall(Y, less(Y, X, RelationList), List),
	list_to_set(List, L),
	sort(L, LessList), !.
	

/****************************************
 * L - set of X's elements 
 ****************************************/
get_set([], [], _).
get_set([X | Xs], [H | Tail], RelationList) :-
	lessList(H, List, RelationList),
	member(X, List),
	get_set(Xs, Tail, RelationList).	

/****************************************
 * Y = alpha(X). Eq - permutation string 
 ****************************************/
alpha(Eq, X, Y) :-
	nth1(X, Eq, Y).

/****************************************
 * alpha : Isotone property
 ****************************************/
alpha_isotone(Eq, Points, RelationList) :-
	forall((member(X, Points),
	member(Y, Points),
	less(X, Y, RelationList),
	alpha(Eq, X, X_alpha),
	alpha(Eq, Y, Y_alpha)),
	less(X_alpha, Y_alpha, RelationList)).

/****************************************
 * alpha^2 = alpha
 ****************************************/
idempotence(Eq) :- idempotence(Eq, Eq).
idempotence([], _).
idempotence([H | Tail], Eq) :-
	alpha(Eq, H, X),
	alpha(Eq, X, Y),
	H =:= Y,
	idempotence(Tail, Eq). 

/****************************************
 * (x<=y, alpha(y)=y) => alpha(x)=x
 ****************************************/
alpha_condition(Eq, Points, RelationList) :-
	forall((member(X, Points),
	member(Y, Points),
	less(Y, X, RelationList),
	alpha(Eq, Y, Y)),
	alpha(Eq, X, X)).

transitive(PhiList, E, RelationList) :-
	length(E,Length),
	forall((member(X,E),
		lessList(X,Cones,RelationList),
		member(Cone,Cones),
		length(Alpha,Length),
		nth1(X,Alpha,Cone)),
		member(Alpha,PhiList)
	).
/**********************************/

list_mltpl(List1, List2, List) :-
	findall(X, (
		member(X, List1),
		member(X, List2)),
	List).

poset_with_maximum(RelationList, E) :-
	member(Maximum, E),
	forall(member(Element, E),
	less(Maximum, Element, RelationList)),
	!.

chain([_], _).
chain([H,T | Tail], RelationList) :-
	less(H, T, RelationList),
	chain([T|Tail], RelationList),
	!.	

have_inf(X1, X2, RelationList) :-
	lessList(X1, X1_cone, RelationList),
	lessList(X2, X2_cone, RelationList),
	list_mltpl(X1_cone, X2_cone, Cone),
	poset_with_maximum(RelationList, Cone),
	!.
	
active_elements(List, E) :-
	flatten(List, FlatList),
	sort(FlatList, SortList),
	SortList = E.

relations(List, E) :-
	findall([X1,X2],
		(member(X1, E),
		member(X2, E),
		X1 < X2),
	Relations),
	sublist(List, Relations),
	active_elements(List, E).

connected(X, Y, RelationList) :-
	(member([X,Y], RelationList);
	member([Y,X], RelationList)).

path(X, Y, RelationList, Path) :-
	travel(X, Y, RelationList, [X], ReversePath),
	reverse(ReversePath, Path),!.

travel(X, Y, RelationList, Point, [Y | Point]) :-
	connected(X, Y, RelationList).
travel(X, Y, RelationList, Visited, Path) :-
	connected(X, Z, RelationList),
	Z =\= Y,
	\+member(Z, Visited),
	travel(Z, Y, RelationList, [Z|Visited], Path).

connective_graph(RelationList, E) :-
	forall((member(X, E),
		member(Y, E),
		X < Y)
	,path(X,Y,RelationList,_)).

semilattice(RelationList, E) :-
	forall(
	(	
		member(X1, E),
		member(X2, E),
		X1 < X2),
	have_inf(X1, X2, RelationList)).

/*
all_semilattice(List, E) :-
	relations(List, E),
	semilattice(List, E).
*/

phi_for_List(RelationList, E, PhiList) :-
	findall(Eq,
	(
		get_set(Eq, E, RelationList),
		idempotence(Eq),
		alpha_isotone(Eq, E, RelationList),
		alpha_condition(Eq, E, RelationList)
	), PhiList).


/*
all_condition_phi(RelationList, E) :-
	phi_for_List(RelationList, E, []).

main(E) :-
	all_semilattice(List, E),
	all_condition_phi(List, E).
*/

/*************************
           NEW
 *************************/
poset_with_semilattices(RelationList, E) :-
	forall(
	member(Element, E),(
	lessList(Element, LessList, RelationList),
	findall([X,Y], (
		member([X,Y], RelationList),
		member(X, LessList),
		member(Y, LessList)
		), LIST),
	sort(LIST, SORTLIST),
	(
	semilattice(SORTLIST, LessList)
	;
	(
	length(SORTLIST, Len),
	Len =:= 1
	)))).

number_of_N_sets(N, Number) :-
	numlist(1, N, E),
	findall(List,(
		relations(List, E),
		connective_graph(List, E),
		poset_with_semilattices(List, E)
	), AllSets),
	length(AllSets, Number).

main(N) :-
	numlist(1, N, E),
	open('log_semi_lattice_phi.txt',write,OS),
	(
	relations(List, E),
	\+member([1,2],List),
	connective_graph(List, E),
	poset_with_semilattices(List, E),
	phi_for_List(List, E, PhiList),
	((
		transitive(PhiList, E, List),
		write(OS,('Poset= ')),
		write(OS, List),
		nl(OS),
		write(OS,('Phi= ')),
		write(OS,PhiList),
		nl(OS),
		write(OS,'PHI is transitive => FAILED'),
		nl(OS),nl(OS)
	)
	;
	(
		\+transitive(PhiList, E, List),
		write(OS,('Poset= ')),
		write(OS, List),
		nl(OS),
		write(OS,('Phi= ')),
		write(OS,PhiList),
		nl(OS),
		write(OS,'PHI is nontransitive => PASSED'),
		nl(OS),nl(OS)
	)),
	fail
	;
	close(OS)
	).
