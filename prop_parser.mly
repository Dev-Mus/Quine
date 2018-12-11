%{
open Prop_def;;
%}


%token ET OU IMPLIQ NEG  LPAR RPAR  QUIT Vrai Faux EQIV FLECHE BARRE
%token <string> VAR
%token EOF
%right IMPLIQ

%left ET
%left OU
%nonassoc NEG
%nonassoc EQIV
%start programme
%type <Prop_def.proposition> programme 
%%

programme   : proplog      EOF                    {$1};

proplog:
       	 VAR					{Var ($1)}
         | Vrai                                  {Vrai}
         | Faux                                 { Faux}
	| NEG proplog				{(NEG ($2))}
	| LPAR NEG proplog RPAR			{(NEG ($3))}
	| proplog IMPLIQ proplog    		{(IMPLIQ ($1,$3))}
	| LPAR proplog IMPLIQ  proplog RPAR   	{(IMPLIQ ($2,$4))}
	| proplog EQIV proplog			{(EQIV ($1,$3))}
	| LPAR proplog EQIV proplog RPAR	{(EQIV ($2,$4))}

	| proplog FLECHE proplog		{(FLECHE ($1,$3))}
	| LPAR proplog FLECHE proplog RPAR	{(FLECHE ($2,$4))}

	| proplog BARRE proplog			{(BARRE ($1,$3))}
	| LPAR proplog BARRE proplog RPAR	{(BARRE ($2,$4))}

	| proplog OU proplog 			{(OU ($1,$3))}
	| LPAR proplog OU proplog RPAR 		{(OU ($2,$4))}

	| proplog ET proplog      		{(ET ($1,$3))}
	| LPAR proplog ET proplog RPAR   	{(ET ($2,$4))}

;
