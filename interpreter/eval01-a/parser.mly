%{
let make_fun vars expr =
  List.fold_right (fun v e -> Syntax.Fun (v, e)) vars expr
%}
/* token definition */
%token LPAREN RPAREN
%token <int> NUMBER
%token <string> VAR
%token PLUS MINUS TIMES DIVIDE EQUAL LESS
%token TRUE FALSE IF THEN ELSE
%token FUN ARROW
%token TRY WITH SEM CALLD CALLS
%token LET REC IN
%token EOF
/* End of File */

/* terminal symbol */
%type <Syntax.e> expr

/* start symbol */
%start expr

%nonassoc ARROW
%nonassoc EQUAL LESS
%left PLUS MINUS
%left TIMES DIVIDE

/* Don't omitte '%%' */
%%

/* Write grammar rules */  
  
simple_expr:
| NUMBER
        { Syntax.Num ($1) }
| TRUE
        { Bool (true) }
| FALSE
        { Bool (false) }
| VAR
        { Syntax.Var ($1) }
| LPAREN expr RPAREN
        { $2 }

expr:
| simple_expr
        { $1 }
| expr PLUS expr
        { Syntax.Op ($1, Syntax.Plus, $3) }
| expr MINUS expr
        { Syntax.Op ($1, Syntax.Minus, $3) }
| expr TIMES expr
        { Syntax.Op ($1, Syntax.Times, $3) }
| expr DIVIDE expr
        { Syntax.Op ($1, Syntax.Divide, $3) }
| expr EQUAL expr
        { Syntax.Op ($1, Syntax.Equal, $3) }
| expr LESS expr
        { Syntax.Op ($1, Syntax.Less, $3) }
| IF expr THEN expr ELSE expr
        { Syntax.If ($2, $4, $6) }
| LET REC VAR VAR vars EQUAL expr IN expr
        { Syntax.Rec ($3, $4, make_fun $5 $7, $9) }
| FUN VAR vars ARROW expr
        { Syntax.Fun ($2, make_fun $3 $5) }
| app
        { $1 }
| TRY expr WITH LPAREN VAR SEM VAR RPAREN ARROW expr
        { Syntax.TryWith ($2, $5, $7, $10)  }
| CALLD LPAREN expr RPAREN
        { Syntax.CallD ($3) }
| CALLS LPAREN expr RPAREN
        { Syntax.CallS ($3) }
        
vars:
|
        { [] }
| VAR vars
        { $1 :: $2 }

app:
| simple_expr simple_expr
        { Syntax.App ($1, $2) }
| app simple_expr
        { Syntax.App ($1, $2) }
