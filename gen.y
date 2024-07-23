%code {
#include <stdio.h>
#include <string.h>
#include <stdarg.h>
#include <stdlib.h>
#include <assert.h>
#include "utilities.h"
#include "symboltable.h"

typedef int TEMP;  /* temporary variable.
                       temporary variables are named t1, t2, ... 
                       in the generated code but
					   inside the compiler they may be represented as
					   integers. For example,  temporary 
					   variable 't3' is represented as 3.
					*/
  
// number of errors found by the compiler 
int errors = 0;					


////////////////////// new funcs at the end//////////////////////////////
void checkVariableDef(const char *);
void checkVariableRedef(const char *);
////////////////////////////////////////////////////////////////////////


extern int yylex (void);
void yyerror (const char *s);

static int newtemp(), newlabel();
void emit (const char *format, ...);
void emitlabel (int label);

/* stack of "exit labels".  An "exit label" is the target 
   of a goto used to exit a statement (e.g. a while statement or a 
   switch statement.)
   The stack is used to implement 'break' statements which may appear
   in while statements.
   A stack is needed because such statements may be nested.
   The label at the top of the stack is the "exit label"  for
   the innermost while statement currently being processed.
   
   Labels are represented here by integers. For example,
   L_3 is represented by the integer 3.
*/

typedef intStack labelStack;
labelStack exitLabelsStack;

enum type currentType;  // type specified in current declaration

} // %code

%code requires {
    void errorMsg (const char *format, ...);
    enum {NSIZE = 100}; // max size of variable names
    enum type {_INT, _DOUBLE };
	enum op { PLUS, MINUS, MUL, DIV, PLUS_PLUS, MINUS_MINUS };
	
	typedef int LABEL;  /* symbolic label. Symbolic labels are named
                       L_1, L_2, ... in the generated code 
					   but inside the compiler they may be represented as
					   integers. For example,  symbolic label 'L_3' 
					   is represented as 3.
					 */
    struct exp { /* semantic value for expression */
	    char result[NSIZE]; /* result of expression is stored 
   		   in this variable. If result is a constant number
		   then the number is stored here (as a string) */
	    enum type type;     // type of expression
	};
	
	struct caselist { /* semantic value for 'caselist' */
	    char switch_result[NSIZE]; /* result variable of the switch expression */
        LABEL exitlabel;/* code for each case ends with a jump to exitlabel */				   
    };			   
	
} // code requires

/* this will be the type of all semantic values. 
   yylval will also have this type 
*/
%union {
   char name[NSIZE];
   int ival;
   double dval;
   enum op op;
   struct exp e;
   LABEL label;
   const char *relop;
   enum type type;
   struct caselist cl;
}

%token <ival> INT_NUM
%token <dval> DOUBLE_NUM
%token <relop> RELOP
%token <name> ID
%token <op> ADDOP MULOP INC_OP


%token WHILE IF ELSE DO FOR SWITCH  CASE DEFAULT 
%token BREAK INT DOUBLE INPUT OUTPUT

%nterm <e> expression
%nterm <label> boolexp  start_label exit_label
%nterm <type> type idlist
%nterm <cl> caselist


/* this tells bison to generate better error messages
   when syntax errors are encountered (these error messages
   are passed as an argument to yyerror())
*/
%define parse.error verbose

/* if you are using an old version of bison use this instead:
%error-verbose */

/* enable trace option (for debugging). 
   To request trace info: assign non zero value to yydebug */
%define parse.trace
/* formatting semantic values (when tracing): */
%printer {fprintf(yyo, "%s", $$); } ID
%printer {fprintf(yyo, "%d", $$); } INT_NUM
%printer {fprintf(yyo, "%f", $$); } DOUBLE_NUM

%printer {fprintf(yyo, "result=%s, type=%s",
            $$.result, $$.type == _INT ? "int" : "double");} expression


/* token ADDOP has lower precedence than token MULOP.
   Both tokens have left associativity.

   This solves the shift/reduce conflicts in the grammar 
   because of the productions:  
      expression: expression ADDOP expression | expression MULOP expression   
*/
%left ADDOP
%left MULOP

%%
program: declarations { initStack(&exitLabelsStack); } 
         stmtlist;

declarations: declarations decl;

declarations: %empty;

decl:  type {currentType = $1;} idlist ';' ;

type: INT    { $$= _INT;} |
      DOUBLE { $$ = _DOUBLE; };
	  
idlist:  idlist {$1 = $<type>$;} ',' ID {checkVariableRedef($4); putSymbol($4, currentType);};

idlist:  ID {checkVariableRedef($1); putSymbol($1, currentType);};
			
stmt: assign_stmt  |
      while_stmt   |
      if_stmt      |
      for_stmt     |
      switch_stmt  |
      break_stmt   |
      input_stmt   |
      output_stmt  |
      block_stmt
	  ;

assign_stmt:  ID {
        if(lookup($1) == NULL)
            {
                char msg[3*NSIZE];
                sprintf(msg, "undefined variable %s", $ID);
                yyerror(msg);
                exit(1);
            }
    }
    '=' expression ';'
    {   
        checkVariableDef($1);

        struct symbol *sym = lookup($1);

        char typecast[20] = {0};
        if(sym->type != $4.type)
        {
            switch(sym->type)
            {
                case _INT:
                    sprintf(typecast, "%s<%s>","static_cast", "int");
                    break;
                case _DOUBLE:
                    sprintf(typecast, "%s<%s>", "static_cast","double");
                    break;
            }
        }
        
        emit("%s = %s%s\n", $1, typecast, $expression.result);
    };
    				 
expression : expression ADDOP expression
                {
        		char op[4] = {0};
        		sprintf(op, "%c", $2 == PLUS ? '+' : '-');
        		if(($1.type == _DOUBLE) || ($3.type == _DOUBLE))
        		{
            			sprintf(op, "[%c]", op[0]);
            			struct exp *tempExp = NULL;
            			char resToCast[NSIZE] = {0};

            			if($1.type == _INT)
                			tempExp = &$1;

            			if($3.type == _INT)
                			tempExp = &$3;

            			if(tempExp != NULL)
            			{
                			strcpy(resToCast, tempExp->result);
                			sprintf(tempExp->result, "t%d", newtemp());
                			emit("%s = static_cast<double>%s\n", tempExp->result, resToCast);
            			}
           		 	$$.type = _DOUBLE;
        		}
        		else
            		$$.type = _INT;

        		sprintf($$.result, "t%d", newtemp());

        		emit("%s = %s %s %s\n", $$.result, $1.result, op, $3.result);
    		};

expression : expression MULOP expression
                { 
        		char op[4] = {0};
        		sprintf(op, "%c", $2 == MUL ? '*' : '/');
        		if(($1.type == _DOUBLE) || ($3.type == _DOUBLE))
        		{
            			sprintf(op, "[%c]", op[0]);
            			struct exp *tempExp = NULL;
            			char resToCast[NSIZE] = {0};

            			if($1.type == _INT)
               		 	tempExp = &$1;

            			if($3.type == _INT)
                			tempExp = &$3;

            			if(tempExp != NULL)
            			{
                			strcpy(resToCast, tempExp->result);
                			sprintf(tempExp->result, "t%d", newtemp());
                			emit("%s = static_cast<double>%s\n", tempExp->result, resToCast);
            			}

            			$$.type = _DOUBLE;
        		}
        		else
            		$$.type = _INT;

        		sprintf($$.result, "t%d", newtemp());


        		emit("%s = %s %s %s\n", $$.result, $1.result, op, $3.result);
    		};     
                  
expression :  '(' expression ')' { $$ = $2; }
           |  ID    { 
                        checkVariableDef($1);

                        struct symbol *sym = lookup($1);
               
                        strcpy($$.result, $1); $$.type = sym->type;
                    }           
           |  INT_NUM    { sprintf($$.result, "%d", $1); $$.type = _INT;}
           |  DOUBLE_NUM { sprintf($$.result, "%.2f", $1); $$.type = _DOUBLE;}
           ;

while_stmt: WHILE start_label '('  boolexp {push(&exitLabelsStack, $4);} ')' 
			stmt 
                      { emit("goto L_%d\n", $2);
                        emitlabel($4);
                        pop(&exitLabelsStack);
					  };
for_stmt  : FOR '(' assign_stmt boolexp ';' ID INC_OP ')' stmt
				  ;
 
 
				  
				  						 
start_label: %empty { $$ = newlabel(); emitlabel($$); };

boolexp:  expression RELOP expression 
             {  $$ = newlabel();
			    emit("ifFalse %s %s %s goto L_%d\n", 
			          $1.result, $2, $3.result, $$);
             };

if_stmt:  IF exit_label '(' boolexp ')' stmt
               { emit("goto L_%d\n", $2);
                 emitlabel($4);
               }				 
          ELSE stmt { emitlabel($2); };
		  
exit_label: %empty { $$ = newlabel(); };



switch_stmt:  SWITCH  
              caselist 
              DEFAULT ':' stmtlist 
			  '}' /* the matching '{' is generated by 'caselist' */
			  {emitlabel($2.exitlabel);};


caselist: caselist CASE INT_NUM ':'{$<label>$ = $1.exitlabel;
				     $1.exitlabel = newlabel();
				emit("ifFalse %s == %d goto L_%d\n", $1.switch_result,$3,$1.exitlabel); }
				stmtlist{
					$$.exitlabel = $<label>5;
					emit("goto L_%d\n",$<label>5);
					emitlabel($1.exitlabel);};

				 
caselist: '(' expression ')' '{' {
	if($expression.type != _INT)
        {
            errorMsg("switch quantity not an integer\n");
            exit(1);  
        }
			   strcpy($$.switch_result, $2.result);
                          $$.exitlabel = newlabel(); 
                          };					                  
 

break_stmt: BREAK ';' 
    {
        if(!isEmpty(&exitLabelsStack)) 
            emit("goto L_%d\n", peek(&exitLabelsStack));
        
        else
        {
            errorMsg("break statement not within loop or switch\n");
            exit(1); 
        }
    }; 

	
input_stmt: INPUT '(' ID ')' ';'  
    {   
        checkVariableDef($ID);

        struct symbol *sym = lookup($ID);
        
        switch(sym->type)
        {
            case _INT:
                emit("in %s\n", sym->name);
                break;
            case _DOUBLE:
                emit("[in] %s\n", sym->name);
                break;
        }
    };
             
output_stmt: OUTPUT '(' expression ')' ';' 
    {
        switch($expression.type)
        {
            case _INT:
                emit("out %s\n", $expression.result);
                break;
            case _DOUBLE:
                emit("[out] %s\n", $expression.result);
                break;
        }
    };
                
block_stmt:   '{'  stmtlist '}';

stmtlist: stmtlist stmt { emit("\n"); }
        | %empty
		;				
					 
%%
int main (int argc, char **argv)
{
  extern FILE *yyin; /* defined by flex */
  extern int yydebug;
  
  if (argc > 2) {
     fprintf (stderr, "Usage: %s [input-file-name]\n", argv[0]);
	 return 1;
  }
  if (argc == 2) {
      yyin = fopen (argv [1], "r");
      if (yyin == NULL) {
          fprintf (stderr, "failed to open %s\n", argv[1]);
	      return 2;
	  }
  } // else: yyin will be the standard input (this is flex's default)
  

  yydebug = 0; //  should be set to 1 to activate the trace

  if (yydebug)
      setbuf(stdout, NULL); // (for debugging) output to stdout will be unbuffered
  
  yyparse();
  
  fclose (yyin);
  return 0;
} /* main */

/* called by yyparse() whenever a syntax error is detected */
void yyerror (const char *s)
{
  extern int yylineno; // defined by flex
  
  fprintf (stderr,"line %d:%s\n", yylineno,s);
}

/* temporary variables are represented by numbers. 
   For example, 3 means t3
*/
static
TEMP newtemp ()
{
   static int counter = 1;
   return counter++;
} 


// labels are represented by numbers. For example, 3 means L_3
static
LABEL newlabel ()
{
   static int counter = 1;
   return counter++;
} 

// emit works just like  printf  --  we use emit 
// to generate code and print it to the standard output.

void emit (const char *format, ...)
{
/*  /* uncomment following line to stop generating code when errors
	   are detected */
    /* if (errors > 0) return; */ 
    printf ("    ");  // this is meant to add a nice indentation.
                      // Use emitlabel() to print a label without the indentation.    
    va_list argptr;
	va_start (argptr, format);
	// all the arguments following 'format' are passed on to vprintf
	vprintf (format, argptr); 
	va_end (argptr);
}

/* use this  to emit a label without any indentation */
void emitlabel(LABEL label) 
{
    /* uncomment following line to stop generating code when errors
	   are detected */
    /* if (errors > 0) return; */ 
	
    printf ("L_%d:\n",  label);
}

/*  Use this to print error messages to standard error.
    The arguments to this function are the same as printf's arguments
*/
void errorMsg(const char *format, ...)
{
    extern int yylineno; // defined by flex
	
	fprintf(stderr, "line %d: ", yylineno);
	
    va_list argptr;
	va_start (argptr, format);
	// all the arguments following 'format' are passed on to vfprintf
	vfprintf (stderr, format, argptr); 
	va_end (argptr);
	
	errors++;
} 
    

void checkVariableDef(const char *varId)
{
    struct symbol *sym = lookup(varId);
    if(sym == NULL)
    {
        errorMsg("undefined variable %s\n", varId);
        exit(1);
    }
}

void checkVariableRedef(const char *varId)
{
    struct symbol *sym = lookup(varId);
    if(sym != NULL)
    {
        errorMsg("attempt to redefine variable %s\n", varId);
        exit(1);
    }
}




