sublist( [], [] ).
sublist( [H | Tail1], [H | Tail2] ) :-
	sublist( Tail1, Tail2 ).
sublist( H, [_ | Tail] ) :-
	sublist( H, Tail ).

less( X, X, _ ).
less( X, Z, RelationList ) :- 
	member( [X,Z], RelationList ).
less( X, Z, RelationList ) :- 
	member( [X,Y], RelationList ),
	less( Y, Z, RelationList ),
	\+less( Z, X, RelationList ).

lessList( X, LessList, RelationList ) :-
	findall( Y
           , less( X, Y, RelationList )
           , List
           ),
	list_to_set( List, L ),
	sort( L, LessList ),
    !.

/****************************************
 * L - set of X's elements 
 ****************************************/
get_set( [], [], _ ).
get_set( [X | Xs], [H | Tail], RelationList ) :-
	lessList( H, List, RelationList ),
	member( X, List ),
	get_set( Xs, Tail, RelationList ).	

/****************************************
 * Y = alpha(X). Eq - permutation string 
 ****************************************/
alpha( Eq, X, Y ) :- nth1( X, Eq, Y ).

/****************************************
 * alpha : Isotone property
 ****************************************/
alpha_isotone( Eq, Points, RelationList ) :-
	forall( ( member( X, Points )
            , member( Y, Points )
            , less( X, Y, RelationList )
            , alpha( Eq, X, X_alpha )
            , alpha( Eq, Y, Y_alpha )
            )
          , less( X_alpha, Y_alpha, RelationList )
          ).

/****************************************
 * alpha^2 = alpha
 ****************************************/
idempotence( Eq ) :- idempotence( Eq, Eq ).
idempotence( [], _ ).
idempotence( [H | Tail], Eq ) :-
	alpha( Eq, H, X ),
	alpha( Eq, X, Y ),
	H =:= Y,
	idempotence( Tail, Eq ). 

%% alpha_condition( +Eq, +Elements, +RelationList )
%
% Check alpha setted as Eq for
% (x<=y, alpha(y)=y) => alpha(x)=x

alpha_condition( Eq, Elements, RelationList ) :-
	forall( ( member( X, Elements )
            , member( Y, Elements )
            , less( Y, X, RelationList )
            , alpha(Eq, Y, Y)
            )
          , alpha( Eq, X, X ) ).

%% transitive( +PhiList, +Elements, +RelationList )
%
% Check transitivity of PhiList

transitive( PhiList, Elements, RelationList ) :-
	length( Elements, Length ),
	forall( ( member( X, Elements )
            , lessList( X, Cones, RelationList )
            , member( Cone, Cones )
            , length( Alpha, Length )
            , nth1( X, Alpha, Cone )
            )
          , member( Alpha, PhiList )
	).

list_mltpl( List1, List2, List ) :-
	findall( X
           , ( member( X, List1 )
             , member( X, List2 )
             )
           , List ).

poset_with_maximum( RelationList, E ) :-
	member( Maximum, E ),
	forall( member( Element, E )
          , less( Maximum, Element, RelationList )
          ),
	!.

chain( [_], _ ).
chain( [H,T | Tail], RelationList ) :-
	less( H, T, RelationList ),
	chain( [T|Tail], RelationList ),
	!.	

have_inf( X1, X2, RelationList ) :-
	lessList( X1, X1_cone, RelationList ),
	lessList( X2, X2_cone, RelationList ),
	list_mltpl( X1_cone, X2_cone, Cone ),
	poset_with_maximum( RelationList, Cone ),
	!.

%% active_elements( +List, +Elements )
% 
% Check that in relationList List all elements of Elements
% is active.

active_elements( List, Elements ) :-
	flatten( List, FlatList ),
	sort( FlatList, Elements ).


%% relations( -List, +E )  
% 
% Generate poset graph List, containing list of relations
% Elements are list of elements ([1,2,3] i.e.)

relations( List, Elements ) :-
	findall( [X1,X2]
           , ( member(X1, Elements)
             , member(X2, Elements)
		     , X1 < X2
             )
           , Relations
           ),
	sublist( List, Relations ),
	active_elements( List, Elements ).



connected( X, Y, RelationList ) :-
    member( [X,Y], RelationList )
    ;
	member( [Y,X], RelationList ).

path( X, Y, RelationList, Path ) :-
	travel( X, Y, RelationList, [X], ReversePath ),
	reverse( ReversePath, Path ),
    !.

travel( X, Y, RelationList, Point, [Y | Point] ) :-
	connected( X, Y, RelationList ).
travel( X, Y, RelationList, Visited, Path ) :-
	connected( X, Z, RelationList ),
	Z =\= Y,
	\+member( Z, Visited ),
	travel( Z, Y, RelationList, [Z|Visited], Path ).

%% connective_graph( +RelationList, +Elements )
%
% Check graph setted as RelationList for connectivity

connective_graph( RelationList, Elements ) :-
	forall( ( member( X, Elements )
            , member( Y, Elements )
            , X < Y
            )
	      , path( X,Y,RelationList,_ )
          ).

semilattice( RelationList, E ) :-
	forall( ( member( X1, E )
            , member( X2, E )
            , X1 < X2
            )
          ,	have_inf(X1, X2, RelationList)
          ).

%% phi_for_List( +RelationList, +E, -PhiList )
%
% Generate PhiList list of alpha convertions

phi_for_List( RelationList, E, PhiList ) :-
	findall( Eq
           , ( get_set( Eq, E, RelationList )
             , idempotence( Eq )
             , alpha_isotone( Eq, E, RelationList )
             , alpha_condition(Eq, E, RelationList)
	         )
           , PhiList
           ).

%% poset_with_semilattices( +RelationList, +E )
% 
% Check that lower cone of every element of poset RelationList 
% is semilattice

poset_with_semilattices( RelationList, E ) :-
	forall( member( Element, E )
          , ( lessList( Element, LessList, RelationList )
            , findall( [X,Y]
                     , ( member( [X,Y], RelationList )
                       , member( X, LessList )
                       , member( Y, LessList )
                       )
                     , LIST
                     )
            , sort( LIST, SORTLIST )
            , ( semilattice( SORTLIST, LessList )
              ; ( length( SORTLIST, Len )
                , Len =:= 1
                )
              )
            )
          ).

number_of_N_sets( N, Number ) :-
	numlist( 1, N, E ),
	findall( List
           , ( relations( List, E )
             , connective_graph( List, E )
             , poset_with_semilattices( List, E )
             )
           , AllSets 
           ),
	length( AllSets, Number ).

main( N ) :-
    numlist( 1, N, E ),
    open( 'log_semi_lattice_phi.txt', write, OS),
    ( relations( List, E )
    , connective_graph( List, E )
    , poset_with_semilattices( List, E )
    , phi_for_List( List, E, PhiList )
    , ( ( transitive( PhiList, E, List )
        , write( OS, ('Poset= ') )
        , write( OS, List )
        , nl( OS )
        , write( OS, ('Phi= ') )
        , write( OS, PhiList )
        , nl( OS )
        , write( OS, 'PHI is transitive => FAILED' )
        , nl( OS ), nl( OS )
	    )
	  ; ( \+transitive( PhiList, E, List )
        , write( OS, ('Poset= ') )
        , write( OS, List )
        , nl( OS )
        , write( OS, ('Phi= ') )
        , write( OS, PhiList )
        , nl( OS )
        , write( OS, 'PHI is nontransitive => PASSED' )
        , nl( OS ), nl( OS )
	    )
      )
    , fail
    ; close(OS)
    ).
