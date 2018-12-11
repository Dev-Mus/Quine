open Prop_def;;

let rec fnc  p =
	match p with
		(Var x) 		->   Var x;
		|Vrai |NEG Faux		->   Vrai;
		|Faux |NEG Vrai 	->   Faux;

		|OU( (ET(x,y)), z) 	->    fnc( ET( OU(x,z), OU(y,z) ) );			
		|OU( (x, ET(y,z))) 	->    fnc( ET( OU(x,y), OU(x,z) ) );			
		
		|NEG OU(x,y) 		->    fnc (ET( (NEG x), (NEG y) ) );

		|NEG ET(x,y) 		->    fnc (OU( (NEG x), (NEG y) ) );

    		|NEG IMPLIQ(x,y) 	->    fnc ( ET( x, (NEG y)) );         

		|NEG NEG x		->    fnc x;					

		|OU(x,y) 		->    OU((fnc x),(fnc y)); 
						             
		|ET(x,y)  	 	->    ET((fnc x),(fnc y));   

		|FLECHE(x,y) 		->    fnc(NEG(OU(x,y)));

		|BARRE(x,y)		->    fnc(NEG(ET(x,y)));

		|NEG FLECHE(x,y)	->    fnc(NEG(ET(x,y)));
		
		|NEG BARRE(x,y)		->    fnc(NEG(OU(x,y)));

		|EQIV(x,y) 		->    fnc (ET( OU( (NEG x), y) , OU( (NEG y), x) ) ); 

		|NEG EQIV(x,y) 		->    fnc (OU( ET( x,(NEG y)) , ET( y, (NEG x)) ) ); 

		|IMPLIQ(x,y) 		->    fnc ( OU( (NEG x), y) ); 

       		|NEG x			 ->   NEG (fnc x);
						
;;
