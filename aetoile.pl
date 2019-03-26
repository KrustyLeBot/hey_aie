%*******************************************************************************
%                                    AETOILE
%*******************************************************************************

/*
Rappels sur l'algorithme
 
- structures de donnees principales = 2 ensembles : P (etat pendants) et Q (etats clos)
- P est dedouble en 2 arbres binaires de recherche equilibres (AVL) : Pf et Pu
 
   Pf est l'ensemble des etats pendants (pending states), ordonnes selon
   f croissante (h croissante en cas d'egalite de f). Il permet de trouver
   rapidement le prochain etat a developper (celui qui a f(U) minimum).
   
   Pu est le meme ensemble mais ordonne lexicographiquement (selon la donnee de
   l'etat). Il permet de retrouver facilement n'importe quel etat pendant

   On gere les 2 ensembles de façon synchronisee : chaque fois qu'on modifie
   (ajout ou retrait d'un etat dans Pf) on fait la meme chose dans Pu.

   Q est l'ensemble des etats deja developpes. Comme Pu, il permet de retrouver
   facilement un etat par la donnee de sa situation.
   Q est modelise par un seul arbre binaire de recherche equilibre.

Predicat principal de l'algorithme :

   aetoile(Pf,Pu,Q)

   - reussit si Pf est vide ou bien contient un etat minimum terminal
   - sinon on prend un etat minimum U, on genere chaque successeur S et les valeurs g(S) et h(S)
	 et pour chacun
		si S appartient a Q, on l'oublie
		si S appartient a Ps (etat deja rencontre), on compare
			g(S)+h(S) avec la valeur deja calculee pour f(S)
			si g(S)+h(S) < f(S) on reclasse S dans Pf avec les nouvelles valeurs
				g et f 
			sinon on ne touche pas a Pf
		si S est entierement nouveau on l'insere dans Pf et dans Ps
	- appelle recursivement etoile avec les nouvelles valeurs NewPF, NewPs, NewQs

*/

%*******************************************************************************

:- ['avl.pl'].       % predicats pour gerer des arbres bin. de recherche   
:- ['taquin.pl'].    % predicats definissant le systeme a etudier

%*******************************************************************************

main :-
	% initialisations Pf, Pu et Q 
	initial_state(Ini),
	heuristique(Ini,H),
	empty(Pu),
	empty(Pf),
	empty(Q),
	insert([[H,H,0],Ini],Pf,PfNew),
	insert([Ini,[H,H,0],nil,nil],Pu,PuNew),
	writeln("debut aetoile"),
	aetoile(PfNew,PuNew,Q).


%*******************************************************************************
%Kassos (Cas sans solution)
aetoile(Pf, _, _) :-
	Pf = nil, !,		%Wololo on sait pas si ça marche
	writeln("Pas de solution").
	
%EPHAD (Situation terminale)
aetoile(Pf,Pu,Q) :-
	writeln("debut aetoile situation terminale"),
	suppress_min(MinTerm, Pf, _),		%Suppression du terme dans Pf
	MinTerm = [[F,H,G],S],
	suppress([S,[F,H,G],Papa,Action], Pu, _),	%Suppression du terme dans Pu
	final_state(Fin),
	writeln(S),
	writeln(Fin),
	S = Fin, !,					%On verifie qu'on est bien à l'état final
	insert([S,[F,H,G],Papa,Action],Q,QNew),
	writeln("Solution trouvée : "),
	write_solution(S,QNew).


%De Gaulle (Cas général)
aetoile(Pf,Pu,Q) :-
	writeln("debut aetoile cas general"),
	suppress_min(MinTerm, Pf, PfNew),
	MinTerm = [[F,H,G],S],
	Terme = [S,[F,H,G],_,_],
	suppress(Terme, Pu, PuNew),
	liste_successeur(Terme,Liste,Q),
	loop_successeur(Liste,S,PfNew,PuNew,PfNewNew,PuNewNew,Q),
	insert(Terme,Q,QNew),
	aetoile(PfNewNew,PuNewNew,QNew).


afficher_taquin([]).
afficher_taquin([X|Y]):-
	writeln(X),
	afficher_taquin(Y).

%affichage d'une solution finale ou d'une solution intermediaire
write_solution(S,Q):-
	suppress([S, F, Papa, Action], Q, QNew),
	writeln('-------------------------------------'),
	writeln(Action),
	afficher_taquin(S),
	initial_state(Ini),
	(S=Ini ->
		writeln('-------------------------------------'),
	;
		write_solution(Papa,QNew)
	).


liste_successeur(Pu_elem,Liste,Q):-
	findall(Suc_elem,successeur(Pu_elem,Suc_elem,Q), Liste). %Lister tous les successeurs d'un etat donné par AVL Pu


successeur([S,[_,_,G],_,_], Suc_elem, Q):-
	rule(Action, Cout, S, Suc),	%récupération successeurs
	not(belongs(Suc, Q)),	%Verif pas explorés
	heuristique(Suc, H_suc),	%Calcul de leur heuristique
	G_suc is G+Cout,			%Ajout du cout
	F_suc is H_suc+G_suc,		%Ajout du cout estimé final
	Suc_elem = [Suc,[F_suc,H_suc,G_suc],S,Action].	%Nouvel AVL Pu


%cerveau macron (cas vide)
loop_successeur([],_,Pf,Pu,Pf,Pu,_).

%Cas proctologue : S est dans cul (deja exploré)
loop_successeur([X|Reste],U,Pf,Pu,PfNew,PuNew,Q):-
	X = [S,[F_suc,H_suc,G_suc],Papa,Action],
	put_flat(Pu),

	belongs([S,[F_suc,H_suc,G_suc],Papa,Action],Q), !,
	loop_successeur(Reste,U,Pf,Pu,PfNew,PuNew,Q).
	
%Cas S dans Pu => S pas encore developé
loop_successeur([X|Reste],U,Pf,Pu,PfNew,PuNew,Q):-
	X = [S,[F_suc,H_suc,G_suc],Papa,Action],
	belongs([S,[F,H,G],_,_],Pu), !,   %check S dans Pu
	(F_suc<F ->                     %si new cout inf a l'ancien
		%on garde le nouveau
		supress([S,[_,_,_],_,_], Pu, PuTmp),
		supress([[F,H,G],S], Pf, PfTmp),

		insert([S,[F_suc,H_suc,G_suc],Papa,Action], PuTmp, PuTmp2),
		insert([[F_suc,H_suc,G_suc],S], PfTmp, PfTmp2),
		
		loop_successeur(Reste,U,PfTmp2,PuTmp2,PfNew,PuNew,Q)
	;
		%sinon on loop sur le reste avec pf et pu
		loop_successeur(Reste,U,Pf,Pu,PfNew,PuNew,Q)
	).	
	

%Cas S pas dans Pu
loop_successeur([[S,[F_suc,H_suc,G_suc],Papa,Action]|Reste],U,Pf,Pu,PfNew,PuNew,Q):-
	%not(belongs([S,[F,H,G],_,_],Pu),		%On vérfie que S n'est pas dans Pu
	insert([S,[F_suc,H_suc,G_suc],Papa,Action], Pu,PuTmp),	%On rajoute S dans Pu
	insert([[F_suc,H_suc,G_suc],S], Pf, PfTmp),				%On rajoute S dans Pf
	loop_successeur(Reste,U,PfTmp,PuTmp,PfNew,PuNew,Q).



















