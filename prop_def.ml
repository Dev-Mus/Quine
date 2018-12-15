exception EndSession;;
exception LexError;;
exception EOF;;
type proposition = 
Vrai
  |Faux
  |Var of string 
  |ET of proposition * proposition
  |NEG of proposition 
  |OU of proposition * proposition
  |IMPLIQ of proposition * proposition
  |EQIV of proposition * proposition 
  |FLECHE of proposition * proposition
  |BARRE of proposition * proposition
;;


let lines = ref 0;;
let words = ref 0;;


let rec print_term  term =
match term with

(Var x) ->  print_string x
|Vrai ->      print_string "vrai";
|Faux  ->     print_string "faux";
|OU(x,y) ->   (
             print_string "(";
             print_term x;
             print_string "#";
             print_term y;
             print_string ")"; )
             
|ET(x,y)      ->  
             (
             print_string "("; 
             print_term x;
             print_string "&";
             print_term y;
             print_string ")"; )
             
|IMPLIQ(x,y) -> 
               (
             print_string "("; 
             print_term x;
             print_string "->";
             print_term y;
             print_string ")";
                )

|EQIV(x,y) -> 
				(
			print_string "(";
			print_term x;
			print_string "<->";
			print_term y;
			print_string ")";
				)

|FLECHE(x,y) ->
				(
			print_string "(";
			print_term x;
			print_string "!";
			print_term y;
			print_string ")";
				)
|BARRE(x,y) ->
				(
			print_string "(";
			print_term x;
			print_string "|";
			print_term y;
			print_string ")";
				)

			
             
|NEG x   -> (print_string "~"; print_term x)
;;

