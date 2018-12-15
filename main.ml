open Prop_def;;
open Fichier;;
open Evaluation;;
 
open List;;
open Prop_lexer;;


 

let boucle in_channel =
	let lexbuffer = Lexing.from_channel in_channel in
		let lire_prop_expr () = 
		Prop_parser.programme Prop_lexer.token lexbuffer in
			let p = lire_prop_expr () in 
				let k p = 			
			print_string "\nLa forme normale conjonctive de la proposition \t"; 
				print_term p;
			print_string " est la suivante : \n";
				print_term (fnc p);
			print_string "\n\n";
			print_list (evaluer (fnc p));
			print_string "\n\n";
			quein (evaluer (fnc p));
			print_string "\n\n";			
		  		in 
					k p ;
	exit 0;;

boucle stdin;;




