open Prop_def;;

let rec tautologie l =
	match l with 
	|[]-> true 
	|hd::tl -> if hd=Vrai then tautologie tl else false
;;

let rec contradictoire l =
	match l with 
	|[]-> true 
	|hd::tl -> if hd=Faux then contradictoire tl else false
;;

let quein l =
	if (tautologie l) then print_string "la formule tautologie"
	else	if (contradictoire l) then print_string "la formule contradictoire" 
		else  print_string "la formule satisfait"
;;
let rec print_list l =
	match l with 
	|[]-> print_string ""
	|(Vrai)::tl ->      print_string "vrai  |"; print_list tl;
	|(Faux)::tl ->     print_string "faux  |"; print_list tl;
	|(Var hd)::tl -> print_string hd; print_string "   |"; print_list tl;
	|_-> failwith "non"
;;

let rec exists l x = 
	match l with 
	|[] 	-> false
	|td::tl -> if td = x then true else exists tl x
;;

let rec recup p l =
	match p with 
	|Var x|(NEG(NEG (Var x))) -> if not(exists l (Var x)) then (Var x)::l else l;
	|NEG (Var x)		  -> if not(exists l (NEG(Var x))) then (NEG (Var x))::l else l; 
	|OU(x,y)|ET(x,y)	  -> recup y (recup x l);
	|_			  -> l; 
;;



let premier l = 
	match l with 
	|[]-> failwith "list vide " 
	|x::lr -> x
;;

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
	|(_,_) 		-> failwith "p or a are not exeprition"
;;	



 
(****************************************************************************************************************************************************)	
	

 



(************************************)
(***************** function d'evaluation ******************)


(***************)


let rec possible p = 
	match p with 
	|OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	
	|ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	
		->   	true
	|Var _|NEG (Var _) |Faux |NEG Vrai |Vrai |NEG Faux -> false
	|OU(x,y) |ET(x,y) -> (possible x)||(possible y)
	|_ 	-> failwith "possible p erreur ..."  
;;

(***************)

let rec simple p =
	match p with 
	|Vrai |NEG Faux |OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	
		->   	Vrai
	|Faux |NEG Vrai |ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	
		->   	Faux
	|Var x -> Var x
	|NEG (Var x) -> NEG (Var x)
	|ET(x,y)->  
		if (possible x) then simple (ET((simple x),y))
		else if (possible y) then simple (ET(x,(simple y)))
			else ET(x,y)	
	|OU(x,y)->  
		if (possible x) then simple (OU((simple x),y))
		else if (possible y) then simple (OU(x,(simple y)))
			else ET(x,y)
	|_ 	-> failwith "simple p erreur ..."  
;;

(***************)

let rec evaluer p = 
	match p with
	|Vrai |NEG Faux	|OU(_,Vrai) |OU(Vrai,_) |ET(Vrai,Vrai)	
		->   	[Vrai]
	
	|Faux |NEG Vrai |ET(_,Faux) |ET(Faux,_) |OU(Faux,Faux)	
		->   	[Faux]
	
	|Var _ |NEG (Var _) 	
		-> [Vrai;Faux]

	|OU(Faux,x) |OU(x,Faux) |ET(x,Vrai) |ET(Vrai,x) 
		->	if (possible x) then 
				evaluer (simple x)
			else 	 (* nv arbr *) 
			evaluer (transfaire x (premier (recup x [])) Vrai)@evaluer (transfaire x (premier (recup x [])) Faux)

	|OU(x,y)->	if (possible (OU(x,y))) then 
				evaluer (simple (OU(x,y)))
			else 	 (* nv arbr *) 
			(evaluer (transfaire (OU(x,y)) (premier (recup (OU(x,y)) [])) Vrai))@(evaluer (transfaire (OU(x,y)) (premier (recup (OU(x,y)) [])) Faux))
	|ET(x,y)->	if (possible (ET(x,y))) then evaluer (simple (ET(x,y)))
			else 	 (* nv arbr *) 
			(evaluer (simple (transfaire (ET(x,y)) (premier (recup (ET(x,y)) [])) Vrai)))@(evaluer (simple(transfaire (ET(x,y)) (premier (recup (ET(x,y)) [])) Faux)))	

	|_ -> failwith ".. rest .. "  (* rest bar flech implique ... *)
;;


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
(****************************************************************************************************************************************************)


