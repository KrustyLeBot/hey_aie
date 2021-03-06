	/*********************************
	DESCRIPTION DU JEU DU TIC-TAC-TOE
	*********************************/

	/*
	Une situation est decrite par une matrice 3x3.
	Chaque case est soit un emplacement libre, soit contient le symbole d'un des 2 joueurs (o ou x)

	Contrairement a la convention du tp pr�c�dent, pour mod�liser une case libre
	dans une matrice on n'utilise pas une constante sp�ciale (ex : nil, 'vide', 'libre','inoccupee' ...);
	On utilise plut�t une variable libre (_), c'est�-dire un terme non instanci� ('_').
	La situation initiale est donc une matrice 3x3 composee uniquement de variables libres (_). 
	Ceci est possible car le jeu consiste � instancier la grille avec des symboles et non � d�placer les symbles d�j� affect�s.
	
	
	
	Jouer un coup, c-a-d placer un symbole dans une grille S1 ne consiste pas � g�n�rer une nouvelle grille S2 obtenue 
	en copiant d'abord S1 puis en remplacant le symbole de case libre par le symbole du joueur, mais plus simplement
	� INSTANCIER (au sens Prolog) la variable libre qui repr�sentait la case libre par la valeur associ�e au joueur, ex :
	Case = Joueur, ou a realiser indirectement cette instanciation par unification via un pr�dicat comme member/2, select/3, nth1/3 ...
	
	Ainsi si on joue un coup en S, S perd une variable libre, mais peut continuer � s'appeler S (on n'a pas besoin de la d�signer
	par un nouvel identificateur).
	La situation initiale est une "matrice" 3x3 (liste de 3 listes de 3 termes chacune)
	o� chacun des 9 termes est une variable libre.	
	*/


:-use_module(library(clpfd)).

situation_initiale([ [_,_,_],
                     [_,_,_],
                     [_,_,_] ]).

	% Convention (arbitraire) : c'est x qui commence

joueur_initial(x).


	% Definition de la relation adversaire/2

adversaire(x,o).
adversaire(o,x).


	/****************************************************
	 DEFINIR ICI � l'aide du pr�dicat ground/1 comment
	 reconnaitre une situation terminale dans laquelle il
	 n'y a aucun emplacement libre : aucun joueur ne peut
	 continuer � jouer (quel qu'il soit).
	 ****************************************************/

%le board est remplit
situation_terminale(_Joueur, Situation) :- ground(Situation).

%joueur a un alignement gagnant
situation_terminale(Joueur, Situation) :-
	alignement(Ali, Situation),
	alignement_gagnant(Ali,Joueur),!.

%L'adversaire de joueur a un alignement gagnant
situation_terminale(Joueur, Situation) :-
	adversaire(Adv, Joueur),
	alignement(Ali, Situation),
	alignement_gagnant(Ali,Adv),!.

					   


/***************************
 DEFINITIONS D'UN ALIGNEMENT
 ***************************/

alignement(L, Matrix) :- ligne(    L,Matrix).
alignement(C, Matrix) :- colonne(  C,Matrix).
alignement(D, Matrix) :- diagonale(D,Matrix).

	/********************************************
	 DEFINIR ICI chaque type d'alignement maximal 
 	 existant dans une matrice carree NxN.
	 ********************************************/
	
ligne(L, M) :-
	length(M, N),
	ligne(N,L,M).

%1 seule ligne
ligne(1,L,[L|_]).

%on renvoie L
ligne(_,L,[L|M]):-
	M\=[].

%on parcours M
ligne(N,L,[_|M]):-
	N\=1,
	NMOINSSS is N-1,
	ligne(NMOINSSS,L,M).	
 
colonne(C,M) :-
	length(M,N),
	transpose(M,MNew),
	ligne(N,C,MNew).

	/* D�finition de la relation liant une diagonale D � la matrice M dans laquelle elle se trouve.
		il y en a 2 sortes de diagonales dans une matrice carree(https://fr.wikipedia.org/wiki/Diagonale) :
		- la premiere diagonale (principale) (descendante) : (A I)
		- la seconde diagonale  (ascendante)  : (R Z)
		A . . . . . . . Z
		. \ . . . . . / .
		. . \ . . . / . .
		. . . \ . / . . .
		. . . . X . . .
		. . . / . \ . . . 
		. . / . . . \ . .
		. / . . . . . \ .
		R . . . . . . . I
	*/
		
diagonale(D, M) :-
	premiere_diag(1,D,M).

diagonale(D, M) :-
	seconde_diag(1,D,M).

premiere_diag(_,[],[]).
premiere_diag(K,[E|D],[Ligne|M]) :-
	nth1(K,Ligne,E),
	K1 is K+1,
	premiere_diag(K1,D,M).

% definition de la seconde diagonale A COMPLETER
%reverse haut bas m

seconde_diag(K,D,M) :-
	reverse(M,MNew),
	premiere_diag(K,D,MNew).
	


	/***********************************
	 DEFINITION D'UN ALIGNEMENT POSSIBLE
	 POUR UN JOUEUR DONNE
	 **********************************/

possible([X|L], J) :- unifiable(X,J), possible(L,J).
possible([], _).

	/* Attention 
	il faut juste verifier le caractere unifiable
	de chaque emplacement de la liste, mais il ne
	faut pas realiser l'unification.
	*/

%check si X est vide
unifiable(X,_) :- var(X).
%check si X est pas vide puis si X=J 
unifiable(X,J) :- ground(X),
		  X==J.
	
	/**********************************
	 DEFINITION D'UN ALIGNEMENT GAGNANT
	 OU PERDANT POUR UN JOUEUR DONNE J
	 **********************************/

	/*
	Un alignement gagnant pour J est un alignement
possible pour J qui n'a aucun element encore libre.
Un alignement perdant pour J est gagnant
pour son adversaire.
	*/


alignement_gagnant(Ali, J) :- ground(Ali), possible(Ali, J).

alignement_perdant(Ali, J) :- adversaire(J, Adv), alignement_gagnant(Ali, Adv).

alignement_possible(J,Ali_poss,Etat) :-
	alignement(Ali_poss,Etat),
	possible(Ali_poss,J).

	/******************************
	DEFINITION D'UN ETAT SUCCESSEUR
	*******************************/

     /*Il faut definir quelle op�ration subit une matrice M representant la situation courante
	lorsqu'un joueur J joue en coordonnees [L,C]
     */	

%renvoit tous les coups possibles de jouer avec l'etat successeur
successeur(J,Etat,[L,C]) :-
	nth1(L,Etat,Ligne),
	nth1(C,Ligne,Elem),
	var(Elem), %check si l'element est pas deja unifié
	Elem = J.

	/**************************************
   	 EVALUATION HEURISTIQUE D'UNE SITUATION
  	 **************************************/

/*
1/ l'heuristique est +infini si la situation J est gagnante pour J
2/ l'heuristique est -infini si la situation J est perdante pour J
3/ sinon, on fait la difference entre :
	   le nombre d'alignements possibles pour J
	moins
 	   le nombre d'alignements possibles pour l'adversaire de J
*/


heuristique(J,Situation,H) :-		% cas 1
   H = 10000,				% grand nombre approximant +infini
   alignement(Alig,Situation),
   alignement_gagnant(Alig,J), !.
	
heuristique(J,Situation,H) :-		% cas 2
   H = -10000,				% grand nombre approximant -infini
   alignement(Alig,Situation),
   alignement_perdant(Alig,J),!.	


% on ne vient ici que si les cut precedents n'ont pas fonctionne,
% c-a-d si Situation n'est ni perdante ni gagnante.

heuristique(J,Situation,H) :-
	
	findall(Ali_J, alignement_possible(J,Ali_J,Situation), Liste_ali_J),
	length(Liste_ali_J, PossJ),

	adversaire(J,Adv),
	findall(Ali_Adv, alignement_possible(Adv,Ali_Adv,Situation), Liste_ali_Adv),
	length(Liste_ali_Adv, PossAdv),

	H is PossJ - PossAdv.



