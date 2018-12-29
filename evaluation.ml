open Prop_def;;
(********************************************* verfier si c'est une tautologie ***********************************************************)
let rec tautologie l =
	match l with 
	|[]-> true 
	|hd::tl -> if hd=Vrai then tautologie tl else false
;;

(*
@param1 l : proposition liste 
@return : returne true si tout les elements de la liste sont "Vrai"
val tautologie : proposition list -> bool = <fun> 
*)
(********************************************* verfier si c'est une contradiction *******************************************************)
let rec contradictoire l =
	match l with 
	|[]-> true 
	|hd::tl -> if hd=Faux then contradictoire tl else false
;;

(*
@param1 l : proposition liste 
@return : returne true si tout les elements de la liste sont "Faux" 
val contradictoire : proposition list -> bool = <fun>
*)
(******************************************** afficher le resultat de l'algo de quine *************************************************)
let quine l =
	if (tautologie l) then print_string "la formule est une tautologie"
	else	if (contradictoire l) then print_string "la formule est une contradiction" 
		else  print_string "la formule est satisfaite"
;;

(*
@param1 : proposition liste 
@return : (unit) affiche "le message" en string 
val quine : proposition list -> unit = <fun>
*)
(******************************************** afficher les  elements d'une liste ***********************************************)
let rec print_list l =
	match l with 
	|[]-> print_string ""
	|(Vrai)::tl ->      print_string "vrai  |"; print_list tl;
	|(Faux)::tl ->     print_string "faux  |"; print_list tl;
	|(Var hd)::tl -> print_string hd; print_string "   |"; print_list tl;
	|_-> failwith "erreur fun: print_list"
;;

(*
@param1 : proposition list 
@return : (unit) affiche les elements de la liste 
val print_list : proposition list -> unit = <fun>
*)
(******************************************* verifier si la valeur exisite dans une liste ****************************************)
let rec exists l x = 
	match l with 
	|[] 	-> false
	|td::tl -> if td = x then true else exists tl x
;;

(*
@param1 : propositition list 
@param2 : proposition
@return : returne true si l'element x existe dans la liste 
val exists : 'a list -> 'a -> bool = <fun>
*)
(****************************************** recuperer les variables d'une proposition ******************************************)
let rec recup p l =
	match p with 
	|Var x|(NEG(NEG (Var x))) -> if not(exists l (Var x)) then (Var x)::l else l;
	|NEG (Var x)		  -> if not(exists l (NEG(Var x))) then (NEG (Var x))::l else l; 
	|OU(x,y)|ET(x,y)	  -> recup y (recup x l);
	|_			  -> l; 
;;

(*
@param1 : proposition
@param2 : liste vide 
@return : returne la liste des variable en ordre inversé sans doublant 
val recup : proposition -> proposition list -> proposition list = <fun>
*)
(***************************************** retourne le 1er element d'une liste **************************************************)
let rec premier l = 
	match l with 
	|[]-> failwith "erreur : la liste est vide :o xD " 
	|[x]-> x
	|x::lr -> premier lr
;;

(*
@param1 : proposition liste
@return : le premier element
val premier : 'a list -> 'a = <fun>
*)
(**************************************** substitution d'une proposition par une autre ************************************************)
let rec transfaire p a vf =
	match (p,a) with
	|(Vrai,_) |(NEG Faux,_)	->   Vrai
	|(Faux,_) |(NEG Vrai,_) ->   Faux
	|(Var x,Var y) 		->   if (Var x)=(Var y) then vf else (Var x)
 	|(Var x,(NEG (Var y)))  ->   if (Var x)=(Var y) then 
					if vf=Vrai then Faux 
					else Vrai 
				     else (Var x)
	|((NEG (Var x)),Var y) 	->   if (Var x)=(Var y) then 
					if vf=Vrai then Faux 
					else Vrai 
				     else (Var x)
	|((NEG (Var x)),(NEG (Var y))) -> if (Var x)=(Var y) then vf else (Var x)
	|(OU(x,y),_)	-> OU((transfaire x a vf) , (transfaire y a vf))	
	|(ET(x,y),_)	-> ET((transfaire x a vf) , (transfaire y a vf))
	|(_,_) 		-> failwith "erreur fun: transfaire"
;;
	
(*
@param1 : proposition
@param2 : proposition  a change
@param3 : proposition changée par Vrai ou Faux
@return : retourne proposition apres le changement du @param2 par @param3
val transfaire : proposition -> proposition -> proposition -> proposition =<fun>
*)
(*************************************** verfier si on peut simplifier une proposition ********************************************)	
let rec possible p = 
	match p with 
	|OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	
	|ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	
		->   	true
	|Var _|NEG (Var _) |Faux |NEG Vrai |Vrai |NEG Faux -> false
	|OU(x,y) |ET(x,y) -> (possible x)||(possible y)
	|_ 	-> failwith "erreur fun: possible"  
;;

(*
@param1 : proposition
@return : retourne true si on peut sinplifier @param1
val possible : proposition -> bool = <fun>
*)
(*************************************** simplifier une proposition ***************************************************************)
let rec simplify p =
	match p with 
	|Vrai |NEG Faux |OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	
		->   	Vrai
	|Faux |NEG Vrai |ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	
		->   	Faux
	|Var x -> Var x
	|NEG (Var x) -> NEG (Var x)
	|ET(x,y)->  
		if (possible x) then simplify (ET((simplify x),y))
		else if (possible y) then simplify (ET(x,(simplify y)))
			else ET(x,y)	
	|OU(x,y)->  
		if (possible x) then simplify (OU((simplify x),y))
		else if (possible y) then simplify (OU(x,(simplify y)))
			else ET(x,y)
	|_ 	-> failwith "erreur fun: simplify"  
;;

(*
@param1 : proposition
@return : returnee la proposition simplifie @param1         
val simplify : proposition -> proposition = <fun>
*)
(************************************** evaluer une propostion et retourner la liste des resultats *************************************)
let rec evaluer p = 
	match p with
	|Vrai |NEG Faux	|OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	->   	[Vrai]
	|Faux |NEG Vrai |ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	->   	[Faux]
	|Var _ |NEG (Var _) 					-> [Vrai;Faux]
	|OU(Faux,x) |OU(x,Faux) |ET(x,Vrai) |ET(Vrai,x) 	->	if (possible x) then 
			evaluer (simplify x)
			else 	 (* nv arbr *) 
			evaluer (transfaire x (premier (recup x [])) Vrai)@evaluer (transfaire x (premier (recup x [])) Faux)
	|OU(x,y)->	if (possible (OU(x,y))) then 	evaluer (simplify (OU(x,y)))
			else 	 (* nv arbr *) 
			(evaluer (transfaire (OU(x,y)) (premier (recup (OU(x,y)) [])) Vrai))@(evaluer (transfaire (OU(x,y)) (premier (recup (OU(x,y)) [])) Faux))
	|ET(x,y)->	if (possible (ET(x,y))) then evaluer (simplify (ET(x,y)))
			else 	 (* nv arbr *) 
			(evaluer (simplify (transfaire (ET(x,y)) (premier (recup (ET(x,y)) [])) Vrai)))@(evaluer (simplify
(transfaire (ET(x,y)) (premier (recup (ET(x,y)) [])) Faux)))	
	|_ -> failwith "erreur fun: evaluer "
;;

(*
@param1 : proposition
@return : returnee la list des resultats de sous arbre Vrai/Faux
val evaluer : proposition -> proposition list = <fun>
*)
(************************************************************************************************************************************)
(**************** execution *******************)
(* 
exists [Var "x"; Var "y";NEG (Var "z"); Vrai] (NEG(Var "x")) ;; 
*)

(* 
recup (OU(Var "x",(ET(OU(Var "x", Var "y") , OU((NEG (Var "z")), Vrai))))) [];; 
recup (OU(OU(Var "a", Var "b"), Var "c")) m[];; 
*)

(*
transfaire (OU(Var "x",(ET(OU(Var "x", Var "y") , OU((NEG (Var "x")), Vrai))))) (Var "x") Vrai;;
transfaire (OU(OU((NEG (Var "x")), Var "y"),Var "x")) (Var "x") Vrai;;
transfaire (OU(OU((NEG (Var "x")), Var "y"),Var "x")) (Var "x") Faux;;
transfaire (OU(OU((NEG (Var "x")), Var "y"),Var "x")) (NEG (Var "x")) Vrai;;
transfaire (OU(OU((NEG (Var "x")), Var "y"),Var "x")) (NEG (Var "x")) Faux;;
transfaire (ET(OU(NEG (Var "a"), Var "c"),OU(NEG (Var "b"), Var "c"))) (Var "c") Vrai;;
*)

(*
evaluer Vrai;;
evaluer Faux;;
evaluer (NEG Vrai);;
evaluer (NEG Faux);;
evaluer (OU(Faux, Vrai));;
evaluer (OU(Vrai, Var "x"));;
evaluer (OU(Var "x", Vrai));;
evaluer (OU(Faux, Var "x"));;
evaluer (OU(Var "x", Faux));;
evaluer (OU(Var "x", Var "y"));;
evaluer (OU(Var "x", Var "x"));;
evaluer (OU(NEG (Var "x"), Var "x"));;
evaluer (OU(Var "x", NEG (Var "x")));;
evaluer (ET(Vrai, Vrai));;
evaluer (ET(Faux, Vrai));;
evaluer (ET(Faux, Var "x"));;
evaluer (ET(Var "x", Faux));;
evaluer (ET(Vrai, Var "x"));;
evaluer (ET(Var "x", Vrai));;
evaluer (ET(Var "x", Var "y"));;
evaluer (ET(Var "x", Var "x"));;
evaluer (ET(NEG (Var "x"), Var "x"));; 
evaluer (ET(Var "x", NEG (Var "x")));; 
evaluer (Var "x");;
evaluer (NEG (Var "x"));;
evaluer (OU(OU((NEG (Var "x")), Vrai),Var "E"));;
evaluer (OU(OU((NEG (Var "x")), Var "z"),Vrai));;
evaluer (ET(OU((NEG (Var "x")), Var "z"),Faux));;
evaluer (OU(OU((NEG (Var "x")), Var "y"),Var "x")) ;;
evaluer (OU(OU(NEG (Var "a"), Var "c"),OU(NEG (Var "b"), Var "c")));;
*)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)
(****************************************************************************************************************************************************)



