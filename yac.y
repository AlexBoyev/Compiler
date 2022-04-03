%{
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <ctype.h>
extern int yylex();
extern int yylineno;
extern char *yytext;

int yyerror();

typedef struct node {
	struct node *left;
	struct node *right;
	char *token;
	int status;
}node;

typedef struct Stable{
	char* funcType;
	char* funcName;
	char* returnType;
	char* returnVal;
	int Scope;
	char *varType;
	char *varName;
	char *varInput;
	char *strSize;	

	struct Stable *next;
	struct Stable *prev;
}Stable;

typedef struct stackNode {
	node* element;
	struct stackNode* next;
}stackNode;

typedef struct stackStr {
	char *element;
	struct stackStr *next;
}stackStr;
	

stackStr *headStr = NULL;
stackNode *ptr = NULL;
Stable* headStable = NULL;
Stable* currentStable = NULL;
Stable *table = NULL;

Stable* enterIFELSEToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status);
void enterARGSToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status);
int checkFloatOrInt(char* tmp);
void enterReturnToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status);
char ** calculate3ACReturnInput(Stable* t);
void enterCONDToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status);
void enterInputToAFILE(char **inputArray,FILE **file_pointer,Stable *t,int status);
char** calculate3ACInputARGS(Stable *t);
char** calculate3ACInput(Stable*);

void calculateReturnValue(Stable* t);	
void checkIfVarIsPointerType(char*,Stable *t);
void checkIfVarIsAddressType(char*,Stable *t);
void checkPointerValue(char *temp,Stable* t);
void checkAdressValue(char *temp,Stable *t);
void delimByBoolean(char*,Stable*);
void splitVarTokenForFuncs(char *varList, char* mathExpr,int status,char*);
int digits_only(const char *s);
void calculateInput(char*);
void calculateInputForPointers(char*);
node *mknode(node *left,node *right,char *token,int);
void makeTableFromTree(node* tree);
void addToTable(char* funType,char* funcName,char* returnType,char* returnVal,int Scope, char* varType,
				char *varName,char* varInput, char* strSize);
void calculateBody(node *tree,int scope);
void moveFixStr(char*);
void checkIfBlock(node* tree);
void SplitStrings(char *VarList);
void SplitStringsARGS(char*varList);
node* makeSTRfromSubTreeINORDER(node*);
node* makeSTRfromSubTreeINORDER2(node*);
node* makeSTRfromSubTreePREORDER(node*);
void reverseWords(char* s);
void reverse(char*,char*);
void splitVarToken(char*,char*,int);
void remove_all_chars(char*,char);
void checkTable();
void printTable();
void printtree(node *tree, int space);
void SplitBySpace(char*);
void errorMsg(char*);
void checkIfFuncExists(char*,Stable*);
char * findType(Stable*);
void checkPointerTypes(char*,char*,Stable*);
void checkIfVarExists(char *,Stable*);
void checkIfFuncExistsOfSameType(char*,Stable*,char*);
void checkIfVarExistsOfSameType(char *,Stable*,char*);
void verifyOpOnVars(char*,Stable* );
void checkIfVarRI(char* input, Stable *t);
void getFunctionVariables(char*);
int checkNumerical(char*);
void checkBooleanCond(char*,Stable*);
void checkBooleanExpr(char*,Stable*);
int isEmpty();
void push(node*);
node* pop();
void pushStr(char*);
char* popStr();
int isEmptyStr();
void fixStrByIndex(char* strTemp);
void checkCompareCond(char*,Stable*);
void delimByCompare(char*,Stable*);
char *findTypeVar(char* var,Stable* t);
char *findTypeVarFoo(char* var,Stable* t,char*);
void delimByArgs(char* input, Stable *t);
void checkTypeOfVars(char*,Stable*);
void delimString(char*,Stable*);

int AC3ReturnArraySize = 0;
int elseFlag = 0;
int labelCount = 1;
int tCount = 0;
char* adress;
char* langType;
char* assign;
char* cID;
char* size;
char * reversedSTR;
char *strTemp;
char* functionName;
char* openbrac = "(";
char* closebrac = ")";
char *stringsize;
char *ourcat;
char * bracket;
char *comp_operator;
char *logic_operator;
char *math_op;
int error = 0;
int space = 0;
int flag = 1;
int ScopeInd=0;
int blockCount = 0;
char Error[1000];
int sheker = 0;
char *funcName;
int functionVariables;
int countP =0;
int global3ACArraySize = 0;
int array[1000];
int arrIndex = 0;


#define YYSTYPE struct node*
%}

%start printInput
%token BOOL _TRUE _FALSE CHAR INT REAL STRING INT_POINT CHAR_POINT REAL_POINT VAR
%token IF ELSE WHILE FOR
%token FUNC PROC
%token RETURN _NULL
%token PLUS MINUS DIVISION ASSIGNMENT GREATER SMALLER NOT MULTIPLY DEREFERANCE ADDRESS
%token AND EQUAL EQUAL_GREATER EQUAL_SMALLER NOT_EQUAL OR
%token LETTER STR_STRING ID REAL_NUM INT_NUM HEX_NUM

%left EQUAL_GREATER EQAUL_SMALLER NOT_EQUAL GREATER SMALLER
%left AND OR
%left PLUS MINUS
%left MULTIPLY DIVISION


%%

printInput: make_tree_from_input {makeTableFromTree($$);checkTable();printtree($$,space);printf(")\n");
				printf("\n -------------------------------------------------------------------------------\n");/*printTable()*/;};

make_tree_from_input: new_nodes {$$ = mknode($1,0,"",-1);};

new_nodes: node new_nodes {$$ = mknode($1,$2,"",-1);} | 
	   node {$$ = $1;};

node: declaretion_of_variables | declare_function | if_else_loops | new_app_ass| body_of_nested_statement | assign_variables | call_function  |
 math_expression ';'{$$=$1;}| references assign_variables;

declaretion_of_variables: var id ':' types_of_variables  ';' {if(strstr($4->token,"string") != NULL)errorMsg("Expected [Size] after string declaration");
								ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$4->token);strcat(ourcat," ");
											    strcat(ourcat,$2->token);strcat(ourcat,closebrac);node* temp=mknode(0,0,ourcat,-1);
											   node* temp1=mknode(temp,0,"",-1);cID=(char*)malloc(100);strcpy(cID,openbrac);
											  strcat(cID,$1->token);node *temp2=mknode(temp1,0,cID,0);$$=mknode(temp2,0,"",-1);} |

			var id applymany ':' types_of_variables  ';' {if(strstr($5->token,"string") != NULL)errorMsg("Expected [Size] after string declaration");
											ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$5->token);strcat(ourcat," ");
											    strcat(ourcat,$2->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
											   node* temp=mknode(0,0,ourcat,-1);
											   node* temp1=mknode(temp,0,"",-1);cID=(char*)malloc(100);strcpy(cID,openbrac);
											  strcat(cID,$1->token);node *temp2=mknode(temp1,0,cID,0);$$=mknode(temp2,0,"",-1);}|

			var id ':' STRING size_of_array  ';'  {
										ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"string");
										strcat(ourcat," ");
											    strcat(ourcat,$2->token);strcat(ourcat,closebrac);node* temp=mknode($5,0,ourcat,-1);
											   node* temp1=mknode(temp,0,"",-1);cID=(char*)malloc(100);strcpy(cID,openbrac);
											  strcat(cID,$1->token);node *temp2=mknode(temp1,0,cID,0);$$=mknode(temp2,0,"",-1);} |

			var id applymany ':' STRING size_of_array  ';' {
												ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"string");
												strcat(ourcat," ");
											    strcat(ourcat,$2->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
											   node* temp=mknode($6,0,ourcat,-1);
											   node* temp1=mknode(temp,0,"",-1);cID=(char*)malloc(100);strcpy(cID,openbrac);
											  strcat(cID,$1->token);node *temp2=mknode(temp1,0,cID,0);$$=mknode(temp2,0,"",-1);};

			

var:VAR { langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);};

types_of_variables:BOOL {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   INT {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);}  |
		   CHAR_POINT {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   CHAR {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   REAL {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   INT_POINT {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   REAL_POINT {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
		   STRING {langType = (char*)malloc(100); strcpy(langType,"string"); $$ = mknode(0,0,langType,-1);};


string: STR_STRING {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,yytext,-1);} |
	   LETTER {langType = (char*)malloc(strlen(yytext)+1); strcpy(langType,yytext); $$ = mknode(0,0,langType,-1);};
		


types_of_assignment:_FALSE {assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,yytext);$$=mknode(0,0,assign,-1);} |
		_TRUE {assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,yytext);$$=mknode(0,0,assign,-1);} |
		 NOT _TRUE{assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,"!");strcat(assign,yytext);$$=mknode(0,0,assign,-1);} |
		 NOT _FALSE{assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,"!");strcat(assign,yytext);$$=mknode(0,0,assign,-1);} | 
		 _NULL{assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,"");strcat(assign,yytext);$$=mknode(0,0,assign,-1);};

types_of_numbers: INT_NUM { assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,yytext);size=(char*)malloc(strlen(yytext)+1);strcpy(size,assign);
			$$=mknode(0,0,assign,-1);} | 
		HEX_NUM {assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,yytext);size=(char*)malloc(strlen(yytext)+1);strcpy(size,assign);
			$$=mknode(0,0,assign,-1);} |
		REAL_NUM {assign=(char*)malloc(strlen(yytext)+1);strcpy(assign,yytext);size=(char*)malloc(strlen(yytext)+1);strcpy(size,assign);
			$$=mknode(0,0,assign,-1);} |
		MINUS REAL_NUM {assign=(char*)malloc(strlen(yytext)+20);strcpy(assign,"-");strcat(assign,yytext);size=(char*)malloc(strlen(yytext)+1);strcpy(size,assign);
			$$=mknode(0,0,assign,-1);}|
		MINUS INT_NUM { assign=(char*)malloc(strlen(yytext)+20);strcpy(assign,"-");strcat(assign,yytext);size=(char*)malloc(strlen(yytext)+1);strcpy(size,assign);
			$$=mknode(0,0,assign,-1);};
		 
math_call_function: id '(' list_of_variables ')' 
					{ourcat = (char*)malloc(100); strcpy(ourcat,$1->token);
					cID = (char*)malloc(100);strcpy(cID,openbrac);node* open = mknode($3,0,cID,0);
					node * temp = mknode(open,0,"(ARGS",0);$$ = mknode(temp,0,ourcat,-1);}| 

 		      id '(' ')'  {ourcat = (char*)malloc(100); strcpy(ourcat,$1->token);node * temp = mknode(0,0,"(ARGS NONE)",-1);
					$$ = mknode(temp,0,ourcat, -1);} ; 

call_function: id '(' list_of_variables ')' ';'
					{ourcat = (char*)malloc(100); strcpy(ourcat,$1->token);
					cID = (char*)malloc(100);strcpy(cID,openbrac);node* open = mknode($3,0,cID,0);
					node * temp = mknode(open,0,"(ARGS",0);
					node* val1 = mknode(temp,0,ourcat, -1); $$ = mknode(val1,0,"(call_func",0);}| 

 		      id '(' ')' ';' {ourcat = (char*)malloc(100); strcpy(ourcat,$1->token);node * temp = mknode(0,0,"(ARGS NONE",0);
					node* val1 = mknode(temp,0,ourcat, -1); $$ = mknode(val1,0,"(call_func",0);} ; 

list_of_variables: math_expression  ',' list_of_variables {$$ = mknode($1,$3,"",-1);
											} | math_expression | assign_variables | assign_variables  ',' list_of_variables {$$ = mknode($1,$3,"",-1);} ;

declare_function: type_of_functions id '(' list_of_parameters ')' '{' Block_body '}' {node *temp1=mknode($1,0,"",-1);
								node *temp3=mknode($2,0,"",-1);
								node* temp2;
								temp1->left->left=temp3;
								node *body1=mknode(0,0,"(BODY",0);
								if($4->status == -5)
									temp2=mknode($4,0,"(ARGS NONE)",-1);
								else{
									if(strcmp($2->token,"Main") == 0){
										error = 1;
										errorMsg("Main cannot have arguments");
									}
									temp2=mknode($4,0,"(ARGS",0);
								}
								node *temp4=mknode(temp2,0,"",-1);
								temp3->right=temp4;
								node *body=mknode(body1,0,"",-1);
								temp1->left->right=body;
								body1->left = $7;
		 						$$=mknode(temp1,0,"",-1);}|
		   type_of_functions id '(' list_of_parameters ')' RETURN types_of_variables '{' Block_body '}' {
								if(strcmp($7->token,"string") == 0){
									errorMsg("func cannot return \" string \"");
								}
								if(strcmp($1->token,"(proc") == 0){
									char* Message = (char*)malloc(100);
									strcpy(Message,"proc ");
									strcat(Message,$2->token);
									strcat(Message, " can not return value");
									errorMsg(Message);
								}
								else{
								node* val1 = mknode($2,0,"",-1); 
								ourcat = (char*)malloc(100); strcpy(ourcat,"(RET"); strcat(ourcat," ");
								strcat(ourcat,$7->token); strcat(ourcat,closebrac);
								node* ret = mknode(0,0,ourcat,-1);
								node *temp1=mknode($1,0,"",-1);
								node *temp3=mknode($2,0,"",-1);
								node* temp2;
								temp1->left->left=temp3;
								node *body1=mknode(0,0,"(BODY",0);
								if($4->status == -5)
									temp2=mknode($4,0,"(ARGS NONE)",-1);
								else{
		
									temp2=mknode($4,0,"(ARGS",0);
								}
								node *temp4=mknode(temp2,0,"",-1);
								temp3->right=temp4;
								node *body=mknode(ret,body1,"",-1);
								temp1->left->right=body;
								body1->left = $9;
								$$=mknode(temp1,0,"",-1);}};

type_of_functions: FUNC {ourcat=(char*)malloc(strlen(yytext)+2);strcpy(ourcat,openbrac);strcat(ourcat,yytext); $$=mknode(0,0,ourcat,0);}|
		   PROC {ourcat=(char*)malloc(strlen(yytext)+2);strcpy(ourcat,openbrac);strcat(ourcat,yytext); $$=mknode(0,0,ourcat,0);};

return_statement: return_ret math_expression { ourcat = (char*)malloc(100); strcpy(ourcat,openbrac);strcat(ourcat,$1->token); 
		  strcat(ourcat," ");if($2->left ==NULL && $2->right==NULL){strcat(ourcat,$2->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);}
						else {$$=mknode($2,0,ourcat,0);}} | 
				return_ret {ourcat = (char*)malloc(100); strcpy(ourcat,openbrac);strcat(ourcat,$1->token); 
								  strcat(ourcat," "); strcat(ourcat,"NONE");strcat(ourcat,closebrac);
									$$ = mknode(0,0,ourcat,-1);}|
		
			 return_ret string { ourcat = (char*)malloc(100); strcpy(ourcat,openbrac);strcat(ourcat,$1->token); 
		  				strcat(ourcat," ");strcat(ourcat,$2->token);strcat(ourcat,closebrac);$$=mknode(0,0,ourcat,-1);} | 

 			return_ret string_size{ ourcat = (char*)malloc(100); strcpy(ourcat,openbrac);strcat(ourcat,$1->token); 
		 				 strcat(ourcat," ");strcat(ourcat,$2->token);strcat(ourcat,closebrac);$$=mknode(0,0,ourcat,-1);};

list_of_parameters: id ':' types_of_variables {ourcat=(char*)malloc(100);
			                       strcpy(ourcat,openbrac);
					       strcat(ourcat,$3->token);
					       strcat(ourcat," ");
					       strcat(ourcat,$1->token);
					       strcat(ourcat,closebrac);
					       node * temp1=mknode(0,0,ourcat,-1);
					       $$=mknode(temp1,0,"",-1);} |

				
		    id applymany ':' types_of_variables { ourcat=(char*)malloc(100);
			                       		  strcpy(ourcat,openbrac);
					       		  strcat(ourcat,$4->token);
					       		  strcat(ourcat," ");
					       		  strcat(ourcat,$1->token);
							  strcat(ourcat," ");
					      		  strcat(ourcat,$2->token);
							  strcat(ourcat,closebrac);
					       		  node * temp1=mknode(0,0,ourcat,-1);
							  $$=mknode(temp1,0,"",-1);} |

		    id applymany ':' types_of_variables ';' list_of_parameters {ourcat=(char*)malloc(9999);
										strcpy(ourcat,openbrac);
										strcat(ourcat,$4->token);
										strcat(ourcat," ");
										strcat(ourcat,$1->token);
										strcat(ourcat," ");
										strcat(ourcat,$2->token);
										strcat(ourcat,closebrac);
										node * temp1=mknode(0,0,ourcat,-1);
							  			$$=mknode(temp1,$6,"",-1);}|

		    id ':' types_of_variables ';' list_of_parameters {ourcat=(char*)malloc(9999);
										strcpy(ourcat,openbrac);
										strcat(ourcat,$3->token);
										strcat(ourcat," ");
										strcat(ourcat,$1->token);
										strcat(ourcat,closebrac);
										node * temp1=mknode(0,0,ourcat,-1);
							  			$$=mknode(temp1,$5,"",-1);} | 

		    id ':' types_of_variables size_of_array  { ourcat=(char*)malloc(100);
			                       		  strcpy(ourcat,openbrac);
					       		  strcat(ourcat,$3->token);
					       		  strcat(ourcat," ");
					       		  strcat(ourcat,$1->token);
							  strcat(ourcat," ");
					       		  node * temp1=mknode($4,0,ourcat,0);
							  $$=mknode(temp1,0,"",-1);} |

		    id applymany ':' types_of_variables size_of_array { ourcat=(char*)malloc(100);
			                       		  strcpy(ourcat,openbrac);
					       		  strcat(ourcat,$4->token);
					       		  strcat(ourcat," ");
					       		  strcat(ourcat,$1->token);
							  strcat(ourcat," ");
					      		  strcat(ourcat,$2->token);
					       		  node * temp1=mknode($5,0,ourcat,0);
							  $$=mknode(temp1,0,"",-1);}|

		    id ':' types_of_variables size_of_array ';' list_of_parameters {ourcat=(char*)malloc(9999);
										strcpy(ourcat,openbrac);
										strcat(ourcat,$3->token);
										strcat(ourcat," ");
										strcat(ourcat,$1->token);
										node * temp1=mknode($4,0,ourcat,0);
							  			$$=mknode(temp1,$6,"",-1);}|

		    id applymany ':' types_of_variables size_of_array ';' list_of_parameters {ourcat=(char*)malloc(9999);
										strcpy(ourcat,openbrac);
										strcat(ourcat,$4->token);
										strcat(ourcat," ");
										strcat(ourcat,$1->token);
										strcat(ourcat," ");
										strcat(ourcat,$2->token);
										node * temp1=mknode($5,0,ourcat,0);
							  			$$=mknode(temp1,$7,"",-1);}|

										{$$=mknode(0,0,"",-5);};
		

Block_body:make_tree_from_input | {$$ =mknode(0,0,"",-1);} | '{' Block_body '}' Block_body {$$=mknode($2,$4,"(BLOCK",0);};

if_else_loops: IF '(' condition ')' statement {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"IF");
						 node* block1 = mknode($5,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,0,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);}|

	       IF '(' condition ')' '{' Block_body'}' {ourcat=(char*)malloc(100);
						
						strcpy(ourcat,openbrac);strcat(ourcat,"IF");
						 node* block1 = mknode($6,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,0,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} |


	       IF '(' condition ')'statement ELSE statement {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"IF-ELSE");
							strcpy(ourcat,openbrac);strcat(ourcat,"IF-ELSE");
						 node* block1 = mknode($5,0,"(BLOCK",0); node *block2 = mknode($7,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,block2,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);}   |


	       IF '(' condition ')' statement ELSE '{' Block_body '}'{ourcat=(char*)malloc(100);
							strcpy(ourcat,openbrac);strcat(ourcat,"IF-ELSE");
						 node* block1 = mknode($5,0,"(BLOCK",0); node *block2 = mknode($8,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,block2,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} |

	       IF '(' condition ')' '{' Block_body '}' ELSE statement {ourcat=(char*)malloc(100);
						strcpy(ourcat,openbrac);strcat(ourcat,"IF-ELSE");
						 node* block1 = mknode($6,0,"(BLOCK",0); node *block2 = mknode($9,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,block2,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} |

	       IF '(' condition ')' '{' Block_body  '}' ELSE '{' Block_body '}' {ourcat=(char*)malloc(100);
						strcpy(ourcat,openbrac);strcat(ourcat,"IF-ELSE");
						 node* block1 = mknode($6,0,"(BLOCK",0); node *block2 = mknode($10,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,block2,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} |

	       WHILE '(' condition ')' '{' Block_body  '}' {ourcat=(char*)malloc(100);
						strcpy(ourcat,openbrac);strcat(ourcat,"WHILE");
						 node* block1 = mknode($6,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,0,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} |
	       WHILE '(' condition ')' statement {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"WHILE");
						strcpy(ourcat,openbrac);strcat(ourcat,"WHILE");
						 node* block1 = mknode($5,0,"(BLOCK",0);
						 node* temp1 = mknode(block1,0,"",-1); node* temp2 = mknode($3,temp1,"",-1);
						 node *temp3 = mknode(temp2,0,ourcat,0); $$ = mknode(temp3,0,"",-1);} | 

	       FOR '(' inits ';' condition ';' updates ')' statement {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"FOR");
									node *block=mknode($9,0,"(BLOCK",0);node *val1=mknode(block,0,"",-1);
									node *updates=mknode($7,0,"(UPDATES",0);node *val2=mknode(updates,val1,"",-1);
									node *cond=mknode($5,0,"(COND",0);node *val3=mknode(cond,val2,"",-1);
									node *inits=mknode($3,0,"(INITS",0);node*val4=mknode(inits,val3,"",-1);
									$$=mknode(val4,0,ourcat,0);}; |


	       FOR '(' inits ';' condition ';' updates ')'  '{'  Block_body '}'{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,"FOR");
									node *block=mknode($10,0,"(BLOCK",0);node *val1=mknode(block,0,"",-1);
									node *updates=mknode($7,0,"(UPDATES",0);node *val2=mknode(updates,val1,"",-1);
									node *cond=mknode($5,0,"(COND",0);node *val3=mknode(cond,val2,"",-1);
									node *inits=mknode($3,0,"(INITS",0);node*val4=mknode(inits,val3,"",-1);
									$$=mknode(val4,0,ourcat,0);};

		
body_of_nested_statement:
			id assignment math_expression ';' update_variables {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
						    strcat(ourcat," ");strcat(ourcat,$1->token);node *temp1=mknode($3,0,"",-1);
						    node *text=mknode(temp1,0,ourcat,0);
					            node *temp2;
						    if($5->left!=NULL){ temp2=mknode(text,$5,"",-1);}
						    else{temp2=mknode(text,0,"",-1);}
						     $$=mknode(temp2,0,"",-1);}| '{'Block_body'}'{$$=mknode($2,0,"(BLOCK_Emp",0);}| return_statement ';' {$$=$1;};


assign_variables: id size_of_array assignment math_expression ';' {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$3->token);
													    stringsize=(char*)malloc(100);strcpy(stringsize,openbrac);strcat(stringsize,$1->token);
													   node *size=mknode($2,0,"",-1);node *math=mknode($4,0,ourcat,0);
													   node* val=mknode(0,math,"",-1);node*final=mknode(size,val,stringsize,0);
														$$=mknode(final,0,"(index",0); } |
			 id size_of_array assignment  string ';' {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$3->token);
													    stringsize=(char*)malloc(100);strcpy(stringsize,openbrac);strcat(stringsize,$1->token);
													   node *size=mknode($2,0,"",-1);node *math=mknode($4,0,ourcat,0);
													   node* val=mknode(0,math,"",-1);node *final=mknode(size,val,stringsize,0);
														$$=mknode(final,0,"(index",0);  } | 
			id size_of_array assignment id size_of_array ';' {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$1->token);
												     stringsize=(char*)malloc(100);strcpy( stringsize,openbrac);strcat( stringsize,$4->token);
												    assign=(char*)malloc(100);strcpy(assign,openbrac);strcat(assign,$3->token);
												   node *size=mknode($5,0,"",-1);node *strnode=mknode(size,0,stringsize,0);
												  node* temp1=mknode(strnode,0,"",-1);node *assignnode=mknode(temp1,0,assign,0);
												node *finalright=mknode(0,assignnode,"",-1);node *size1=mknode($2,0,"",-1);
												node*final=mknode(size1,finalright,ourcat,0);$$=mknode(final,0,"(index",0); } |

			id assignment math_call_function {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
									strcat(ourcat," "); strcat(ourcat, $1->token); $$ = mknode($3,0,ourcat,0); } |
	
			id size_of_array assignment math_call_function  {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$3->token);
													    stringsize=(char*)malloc(100);strcpy(stringsize,openbrac);strcat(stringsize,$1->token);
													   node *size=mknode($2,0,"",-1);node *math=mknode($4,0,ourcat,0);
													   node* val=mknode(0,math,"",-1);node*final=mknode(size,val,stringsize,0);
														$$=mknode(final,0,"(index",0); }| 

			id assignment types_of_exp {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
									strcat(ourcat," "); strcat(ourcat, $1->token); $$ = mknode($3,0,ourcat,0); } ;
													



inits:id{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$1->token);strcat(ourcat,closebrac);$$=mknode(0,0,ourcat,-1);} |
	  | id assignment math_expression{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
						    strcat(ourcat," ");strcat(ourcat,$1->token);node *temp1=mknode($3,0,"",-1);
						    node *text=mknode(temp1,0,ourcat,0);node* temp2=mknode(text,0,"",-1);
						    $$=mknode(temp2,0,"",-1);}  ;

updates:id assignment math_expression {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
						    strcat(ourcat," ");strcat(ourcat,$1->token);node *temp1=mknode($3,0,"",-1);
						    node *text=mknode(temp1,0,ourcat,0);node* temp2=mknode(text,0,"",-1);
						    $$=mknode(temp2,0,"",-1);};

statement: id assignment math_expression ';'{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
						    strcat(ourcat," ");strcat(ourcat,$1->token);node *temp1=mknode($3,0,"",-1);
						    node *text=mknode(temp1,0,ourcat,0);node* temp2=mknode(text,0,"",-1);
						    $$=mknode(temp2,0,"",-1);}
						     | return_statement ';' {$$=$1;}| if_else_loops{$$=$1;} | {$$=mknode(0,0,"",-1);}  |declaretion_of_variables{$$=$1;};

update_variables:
		 id assignment math_expression ';' update_variables {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);
						    strcat(ourcat," ");strcat(ourcat,$1->token);node *temp1=mknode($3,0,ourcat,0);
						    node* temp4=mknode($5,0,"",-1);
						    node *temp2=mknode(temp4,0,"",-1);node* temp3 = mknode(temp2,0,"",-1);
						    node *top=mknode(temp1,temp3,"",-1); $$ = top; }|if_else_loops{$$=$1;} | {$$=mknode(0,0,"",-1);} 							    | string | call_function | assign_variables ;


math_expression:  types_of_exp all_operators  math_expression  {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
													strcat(ourcat,$2->token);
													node* space1=mknode(0,$1,"",-1);
													node *temp2=mknode($3,0,"",-1);
													node* temp1 =mknode(temp2,space1,ourcat,0);
													$$=temp1;}| types_of_exp {$$=$1;} | brackets | string | string_size;

				

brackets : '(' math_expression ')' {node *temp=$2;while(temp->left != NULL){temp = temp->left;}node *dollar=mknode(0,0,"$",-2);temp->left=dollar;$$=mknode($2,0,"$",-2);};
	
condition: 	types_of_exp all_operators  condition {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
												strcat(ourcat,$2->token); node* val1 = mknode($1,0,"",-1);
												node* val2 = mknode($3,val1,ourcat,0); $$ = mknode(val2,0,"",-1);}
												| types_of_exp | brackets | string_size{$$=$1;};

references: ADDRESS {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);} |
		DEREFERANCE {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);};

types_of_exp: id| brackets |types_of_assignment | id size_of_array {ourcat=(char*)malloc(100);strcpy(ourcat,$1->token);$$=mknode($2,0,ourcat,-1);}|types_of_numbers |compare_variables| references id{ourcat=(char*)malloc(100);strcpy(ourcat,$1->token);strcat(ourcat,$2->token);$$=mknode(0,0,ourcat,-1);} | math_call_function | references brackets{ourcat=(char*)malloc(100);strcpy(ourcat,$1->token);$$=mknode($2,0,ourcat,-1);} | string | string_size| references id size_of_array {ourcat=(char*)malloc(100);strcpy(ourcat,$1->token);strcat(ourcat,$2->token);$$=mknode($3,0,ourcat,-1);};



compare_variables: id compare_operator id {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
									strcat(ourcat,$1->token);
						strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);$$=mknode(0,0,ourcat,-1);} |
		   id compare_operator types_of_numbers {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 
		   types_of_numbers compare_operator id { ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 
		   types_of_numbers compare_operator types_of_numbers {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
													strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 
		  types_of_assignment compare_operator types_of_assignment{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
												strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 
		id compare_operator types_of_assignment{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} |
		 types_of_assignment compare_operator id {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} |

		 id compare_operator  '|' id '|' {ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,"|");strcat(ourcat,$4->token);strcat(ourcat,"|");strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);}|

		  id compare_operator string{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
												strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 
		  string compare_operator id{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
												strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);} | 

		 string compare_operator string{ourcat=(char*)malloc(100);strcpy(ourcat,openbrac);
												strcat(ourcat,$2->token);strcat(ourcat," ");
						strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);strcat(ourcat,closebrac);
						$$=mknode(0,0,ourcat,-1);};

compare_operator: EQUAL {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);} |
		NOT_EQUAL{comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1); } |
		EQUAL_GREATER {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);} |
		EQUAL_SMALLER {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);} |
		SMALLER {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);} |
		GREATER {comp_operator=(char*)malloc(100);strcpy(comp_operator,yytext);
			$$=mknode(0,0,comp_operator,-1);};

logical_operators: AND {logic_operator=(char*)malloc(100);strcpy(logic_operator,yytext);
			$$=mknode(0,0,logic_operator,-1);}|
			OR {logic_operator=(char*)malloc(100);strcpy(logic_operator,yytext);
			$$=mknode(0,0,logic_operator,-1);};
		
				
		
math_operators: PLUS {math_op=(char*)malloc(100);strcpy(math_op,yytext);
			$$=mknode(0,0,math_op,-1);} |
		MINUS {math_op=(char*)malloc(100);strcpy(math_op,yytext);
			$$=mknode(0,0,math_op,-1);} |
		MULTIPLY {math_op=(char*)malloc(100);strcpy(math_op,yytext);
			$$=mknode(0,0,math_op,-1);} |
		DIVISION {math_op=(char*)malloc(100);strcpy(math_op,yytext);
			$$=mknode(0,0,math_op,-1);};

all_operators : logical_operators | math_operators | compare_operator;	
	


applymany: ',' id applymany {ourcat=(char*)malloc(9999);
			    strcpy(ourcat,$2->token);strcat(ourcat," ");
			    strcat(ourcat,$3->token);
			    $$=mknode(0,0,ourcat,-1);} | 
	   ',' id {$$=$2;};

size_of_array: '[' math_expression ']' {stringsize=(char*)malloc(strlen(yytext)+5);strcpy(stringsize,"[");
			   $$=mknode($2,0,stringsize,-10);} | 
		       '[' types_of_exp ']' {node* temp4=mknode($2,0,"",-1); $$=mknode(temp4,0,"[",-10);};

id: ID {cID=(char*)malloc(strlen(yytext)+1);strcpy(cID,yytext);$$=mknode(0,0,yytext,-1);} |
	DEREFERANCE ID {cID=(char*)malloc(100);strcpy(cID,"^");strcat(cID,yytext);$$=mknode(0,0,cID,-1);} |
	NOT ID {cID=(char*)malloc(100);strcpy(cID,"!");strcat(cID,yytext);$$=mknode(0,0,cID,-1);} |
	MINUS ID {cID=(char*)malloc(100);strcpy(cID,"-");strcat(cID,yytext);$$=mknode(0,0,cID,-1);};



return_ret: RETURN {cID=(char*)malloc(4);strcpy(cID,"ret_val");$$=mknode(0,0,cID,-1);};
assignment: ASSIGNMENT {cID=(char*)malloc(strlen(yytext)+1);strcpy(cID,yytext);$$=mknode(0,0,yytext,-1);};

new_app_ass: id assignment  string  ';' {ourcat = (char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token); 
			strcat(ourcat," ");strcat(ourcat,$1->token);strcat(ourcat," ");strcat(ourcat,$3->token);
			strcat(ourcat,closebrac); $$ = mknode(0,0,ourcat,-1);} | 

		       id assignment string_size ';' {ourcat = (char*)malloc(100);strcpy(ourcat,openbrac);strcat(ourcat,$2->token); strcat(ourcat," ");
			strcat(ourcat,$1->token);strcat(ourcat," "); $$ = mknode($3,0,ourcat,0);} ; 

string_size: '|' id '|' { ourcat = (char*)malloc(100); strcpy(ourcat,"|");strcat(ourcat,$2->token);strcat(ourcat,"|"); $$ = mknode(0,0,ourcat,-1);};



%%

#include "lex.yy.c"
int main (void) {
return yyparse();
}

node *mknode(node *left, node *right, char *token,int status){
	node *newnode = (node *)malloc(sizeof(node));
	newnode->token = strdup(token);
	newnode->left = left;
	newnode->right = right;
	newnode->status = status;
	return newnode;
 }

void makeTableFromTree(node* tree){
	char *tempStr = (char*)malloc(1000);
	char *retType = (char*)malloc(1000);
	if(tree){
		
		if(strcmp(tree->token,"(proc") == 0){
			funcName = (char*)malloc(100);
			strcat(funcName,tree->token);
			sheker = 0;
			strcpy(tempStr,tree->left->left->token);
			ScopeInd = ScopeInd + 1000;
			strcpy(funcName,"@");
			strcat(funcName,tempStr);
			addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			addToTable("proc",tempStr,NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);

		}

		else if(strcmp(tree->token,"(func") == 0){
			funcName = (char*)malloc(100);
			sheker = 0;
			strcpy(tempStr,tree->left->left->token);
			strcpy(retType,tree->right->left->token);
			remove_all_chars(retType,'(');
			remove_all_chars(retType,')');
			remove_all_chars(retType,'R');
			remove_all_chars(retType,'E');
			remove_all_chars(retType,'T');
			ScopeInd = ScopeInd + 1000;
			strcpy(funcName,"@");
			strcat(funcName,tempStr);
			addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			addToTable("func",tempStr,retType,NULL,ScopeInd,NULL,NULL,NULL,NULL);

		}

		
		else if(strcmp(tree->token,"(ARGS") == 0){
			ScopeInd = ScopeInd + 1;
			node *next = tree->left;
			while(next->right != NULL){
					
					if(strstr(next->left->token, "(string") != NULL){
							strTemp = (char*)malloc(1000);
							strcpy(strTemp,"");
							makeSTRfromSubTreeINORDER(next->left->left->left);
							reverseWords(strTemp);
							strcpy(tempStr,next->left->token);
							splitVarTokenForFuncs(tempStr,strTemp,0,funcName);

					}else{
						strcpy(tempStr,next->left->token);
						splitVarTokenForFuncs(tempStr,NULL,0,funcName);
					}
					next = next->right;
			}
			
			if(strstr(next->left->token, "(string") != NULL){
					strTemp = (char*)malloc(1000);
					strcpy(strTemp,"");
					makeSTRfromSubTreeINORDER(next->left->left->left);
					reverseWords(strTemp);
					strcpy(tempStr,next->left->token);
					splitVarTokenForFuncs(tempStr,strTemp,0,funcName);

			}
			else{
				strcpy(tempStr,next->left->token);
				splitVarTokenForFuncs(tempStr,NULL,0,funcName);
			}
		}
		
		else if(strcmp(tree->token,"(BODY")==0){
			node* temp;
			if(tree->right  != NULL){
				push(tree->right);
			}
			if(tree->left != NULL){
				tree = tree->left;
			}
			if(tree != NULL){
				while(strcmp(tree->token,"") == 0){
					if(tree->right != NULL){
						
						temp = tree->right;
						push(temp);
					}
					if(tree->left != NULL){
						tree= tree->left;
					}else{
						break;
					}
				}
			}
			if(tree->right != NULL){
				if(strcmp(tree->token,"(proc")==0 || strcmp(tree->token,"(func")==0);
				else{
					temp = tree->right;
					push(temp);
				}

			}
			
			ScopeInd = ScopeInd - ScopeInd%1000;
			if(sheker ==0){

				calculateBody(tree,ScopeInd);
				sheker= 1;
			}

			while(isEmpty() !=1){
				ScopeInd = ScopeInd - ScopeInd%1000;
				node* next = pop();
				if(next->left == NULL ){
					calculateBody(next,ScopeInd);
				}
				else if(next->right == NULL){
					calculateBody(next,ScopeInd);
				}
				else{
					calculateBody(next->left,ScopeInd);
				}
				while(next->right!=NULL){
					next=next->right;
					ScopeInd = ScopeInd - ScopeInd%1000;
					if(next->left == NULL ){
						calculateBody(next,ScopeInd);
					}
					else if(next->right == NULL){
						calculateBody(next,ScopeInd);
					}
					else{
						calculateBody(next->left,ScopeInd);
					}
				}
			}
			while(tree->left !=NULL){
				tree=tree->left;
			}

		}
		
		
		makeTableFromTree(tree->left);
		makeTableFromTree(tree->right);
		if(strcmp(tree->token, "(proc") == 0 || strcmp(tree->token, "(func") == 0){
			addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
		}
		if(strcmp(tree->token,"(ARGS") == 0){
			ScopeInd = ScopeInd - 1;
		}
	
	}

}

void addToTable(char* funcType,char* funcName,char* returnType,char* returnVal,int Scope, char* varType,
				char *varName,char* varInput, char* strSize){
	Stable* table = (Stable*)malloc(sizeof(Stable));
	if(currentStable == NULL){
		currentStable = (Stable*)malloc(sizeof(Stable));
		headStable  = (Stable*)malloc(sizeof(Stable));
		headStable = table;
		table->prev = NULL;

	}
	else{ table->prev = currentStable; currentStable->next = table;}
	table->funcType = funcType;
	table->funcName = funcName;
	table->returnType = returnType;
	table->returnVal = returnVal;
	table->Scope = Scope;
	table->varType = varType;
	table->varName = varName;
	table->varInput = varInput;
	table->strSize = strSize;
	table->next = NULL;
	currentStable = table;

}

void printTable(){
	Stable* t = (Stable*)malloc(sizeof(Stable));
	t=headStable;
	while(t){
		if(t->funcType !=NULL)
			printf("Func Type = %s\n",t->funcType);
		if(t->funcName !=NULL)
			printf("Func Name = %s\n",t->funcName);
		if(t->returnType !=NULL)
			printf("return Type = %s\n",t->returnType);
		if(t->returnVal !=NULL)
			printf("return Value = %s\n",t->returnVal);
		if(t->varType !=NULL)
			printf("Var Type = %s\n",t->varType);
		if(t->varName !=NULL)
			printf("Var Name = %s\n",t->varName);
		if(t->varInput !=NULL)
			printf("Var Input = %s\n",t->varInput);
		if(t->strSize !=NULL)
			printf("String Size = %s\n",t->strSize);
		printf("Scope  = %d\n",t->Scope);
		t = t->next;
	}

}

void SplitStrings(char*varList){
	remove_all_chars(varList,'(');
	remove_all_chars(varList,')');
	char delim[] = "=";
	char* assignment = "=";
	char * varName =(char*)malloc(100);
	char *varValue= (char*)malloc(100);
	int flag = 0;
	int init_size = strlen(varList);
	reverseWords(varList);
	char *ptr = strtok(varList, delim);

	while (ptr != NULL) {
		if(flag == 0 && strcmp(assignment,ptr) !=0 ) {
			strcpy(varName,ptr);
			flag = 1;
		}
		ptr = strtok(NULL, delim);
		if(ptr != NULL && ptr != ""){
			varValue = strdup(ptr);
				if(strcmp(ptr,assignment) != 0)
			addToTable(NULL,NULL,NULL,NULL,ScopeInd,NULL,varName,varValue,NULL);
		}
	}
}


void SplitStringsARGS(char*varList){
	remove_all_chars(varList,'(');
	remove_all_chars(varList,')');
	char delim[] = "ARGS";
	char* assignment = "=";
	char * varName =(char*)malloc(100);
	char *varValue= (char*)malloc(100);
	int flag = 0;
	int init_size = strlen(varList);
	reverseWords(varList);
	char *ptr = strtok(varList, delim);

	while (ptr != NULL) {
		if(flag == 0 && strcmp(assignment,ptr) !=0 ) {
			strcpy(varName,ptr);
			flag = 1;
		}
		ptr = strtok(NULL, delim);
		if(ptr != NULL && ptr != ""){
			varValue = strdup(ptr);
				if(strcmp(ptr,assignment) != 0)
			addToTable(NULL,NULL,NULL,NULL,ScopeInd,NULL,varName,varValue,NULL);
		}
	}
}

void splitVarToken(char *varList, char* mathExpr,int status){
	remove_all_chars(varList,'(');
	remove_all_chars(varList,')');
	char * varType =(char*)malloc(100);
	char *varName = (char*)malloc(100);
	int flag = 0;
	int init_size = strlen(varList);
	char delim[] = " ";
	char *ptr = strtok(varList, delim);

	if(mathExpr != NULL){
		remove_all_chars(mathExpr,'(');
		remove_all_chars(mathExpr,')');

	}
	while (ptr != NULL) {
		if(flag == 0){
			strcpy(varType,ptr);
			flag = 1;
		}
		ptr = strtok(NULL, delim);
		if(ptr != NULL && ptr != ""){
			varName = strdup(ptr);
			if(status == 0){
				addToTable(NULL,NULL,NULL,NULL,ScopeInd,varType,varName,NULL,mathExpr);
			}
			else if(status == 1){
				addToTable(NULL,NULL,NULL,NULL,ScopeInd,NULL,varType,varName,mathExpr);
			}
		}
	}
}


void splitVarTokenForFuncs(char *varList, char* mathExpr,int status,char* funcName){
	remove_all_chars(varList,'(');
	remove_all_chars(varList,')');
	char * varType =(char*)malloc(100);
	char *varName = (char*)malloc(100);
	int flag = 0;
	int init_size = strlen(varList);
	char delim[] = " ";
	char *ptr = strtok(varList, delim);

	if(mathExpr != NULL){
		remove_all_chars(mathExpr,'(');
		remove_all_chars(mathExpr,')');

	}
	while (ptr != NULL) {
		if(flag == 0){
			strcpy(varType,ptr);
			flag = 1;
		}
		ptr = strtok(NULL, delim);
		if(ptr != NULL && ptr != ""){
			varName = strdup(ptr);
			if(status == 0){
				addToTable(funcName,NULL,NULL,NULL,ScopeInd,varType,varName,NULL,mathExpr);
			}
			else if(status == 1){
				addToTable(funcName,NULL,NULL,NULL,ScopeInd,NULL,varType,varName,mathExpr);
			}
		}
	}
}


node* makeSTRfromSubTreeINORDER(node* subTree){
	node *temp;
	if(subTree){
		if(strstr(subTree->token,"(ARGS") !=NULL){
			strcat(strTemp," _END ");
		}
		if(strstr(subTree->token,"[") !=NULL){
			strcat(strTemp," ] ");
		}
		temp = makeSTRfromSubTreeINORDER(subTree->left);
		strcat(strTemp,subTree->token);
		strcat(strTemp," ");
		temp = makeSTRfromSubTreeINORDER(subTree->right);

	}
	return temp;
}

node* makeSTRfromSubTreeINORDER2(node* subTree){
	node *temp;
	if(subTree){
		if(strstr(subTree->token,"(ARGS") !=NULL){
			strcat(strTemp," _END ");
		}
		temp = makeSTRfromSubTreeINORDER2(subTree->left);
		strcat(strTemp,subTree->token);
		strcat(strTemp," ");
		temp = makeSTRfromSubTreeINORDER2(subTree->right);


	}
	return temp;
}

node* makeSTRfromSubTreePREORDER(node* subTree){
	node *temp;
	if(subTree){
		strcat(strTemp,subTree->token);
		strcat(strTemp," ");
		temp = makeSTRfromSubTreePREORDER(subTree->left);
		temp = makeSTRfromSubTreePREORDER(subTree->right);
	}
	return temp;
}

void checkIfBlock(node* tree){
	if(tree){
		if(strcmp(tree->token,"(BLOCK") == 0){
			blockCount = blockCount + 1;
		}
		checkIfBlock(tree->left);
		checkIfBlock(tree->right);
	}
}

void remove_all_chars(char* str, char c) {
    char *pr = str, *pw = str;
    while (*pr) {
        *pw = *pr++;
        pw += (*pw != c);
    }
    *pw = '\0';
}
void reverseWords(char* s)  { 
    char* word_begin = NULL; 
    char* temp = s;
  
    while (*temp) { 

        if ((word_begin == NULL) && (*temp != ' ')) { 
            word_begin = temp; 
        } 
        if (word_begin && ((*(temp + 1) == ' ') || (*(temp + 1) == '\0'))) { 
            reverse(word_begin, temp); 
            word_begin = NULL; 
        } 
        temp++; 
    }

    reverse(s, temp - 1); 
}


void reverse(char* begin, char* end)  { 
    char temp; 
    while (begin < end) { 
        temp = *begin; 
        *begin++ = *end; 
        *end-- = temp; 
    } 
}

void calculateBody(node *tree,int scope){
	if(tree){
		char *retType = (char*)malloc(1000);
		char *tempStr = (char*)malloc(1000);
		int zindicator =0;
		if(strstr(tree->token, "(var") != NULL) {
			ScopeInd = ScopeInd + 1;
			if(strstr(tree->left->left->token, "(string") != NULL){
				strTemp = (char*)malloc(1000);
				strcpy(strTemp,"");
				makeSTRfromSubTreeINORDER(tree->left->left->left->left);
				reverseWords(strTemp);
				strcpy(tempStr,tree->left->left->token);
				splitVarToken(tempStr,strTemp,0);
			}
			else{
				strcpy(tempStr,tree->left->left->token);
				splitVarToken(tempStr,NULL,0);
			}

		}
		else if(strstr(tree->token, "(index") != NULL ) {
			ScopeInd = ScopeInd + 1;
			strTemp = (char*)malloc(1000);
			makeSTRfromSubTreeINORDER(tree->left);
			reverseWords(strTemp);
			remove_all_chars(strTemp,'(');
			fixStrByIndex(strTemp);


			char delim[] = "[";
			char *ptr = strtok(strTemp, delim);
			char* varName = (char*)malloc(100);
			char* varInput = (char*)malloc(100);
			int flag =0;
			while (ptr != NULL) {
				if(flag == 0  ) {
					strcpy(varName,strdup(ptr));
					flag =1;
				}
				ptr = strtok(NULL, delim);
				if(ptr != NULL){
					strcpy(varInput,"[ ");
					strcat(varInput,strdup(ptr));
				}
			}
			addToTable(NULL,NULL,NULL,NULL,ScopeInd,NULL,varName,varInput,NULL);
			
		}
		else if (strstr(tree->token, "(=") != NULL && strstr(tree->token, "(==") == NULL) {
			ScopeInd = ScopeInd + 1;
			strTemp = (char*)malloc(1000);
			makeSTRfromSubTreeINORDER(tree);
			if(tree->left == NULL && tree->right == NULL){
				remove_all_chars(strTemp,'=');
				splitVarToken(strTemp,NULL,1);
			}else{
				SplitStrings(strTemp);
			}
		}
		else if(strstr(tree->token, "(ret_val") != NULL)	{
			ScopeInd = ScopeInd + 1;
			strTemp = (char*)malloc(1000);
			makeSTRfromSubTreeINORDER(tree);
			remove_all_chars(strTemp ,'(');
			remove_all_chars(strTemp ,')');
			remove_all_chars(strTemp ,'R');
			remove_all_chars(strTemp ,'E');
			remove_all_chars(strTemp ,'T');
			addToTable("_RETURN",NULL,NULL,strTemp,ScopeInd,NULL,NULL,NULL,NULL);
		
		}
		else if(strstr(tree->token, "(index") != NULL ) {
			ScopeInd = ScopeInd + 1;
			strTemp = (char*)malloc(1000);
			makeSTRfromSubTreeINORDER(tree->left);
			reverseWords(strTemp);
			remove_all_chars(strTemp,'(');
			fixStrByIndex(strTemp);


			char delim[] = "[";
			char *ptr = strtok(strTemp, delim);
			char* varName = (char*)malloc(100);
			char* varInput = (char*)malloc(100);
			int flag =0;
			while (ptr != NULL) {
				if(flag == 0  ) {
					strcpy(varName,strdup(ptr));
					flag =1;
				}
				ptr = strtok(NULL, delim);
				if(ptr != NULL){
					strcpy(varInput,"[ ");
					strcat(varInput,strdup(ptr));
				}
			}
			addToTable(NULL,NULL,NULL,NULL,ScopeInd,NULL,varName,varInput,NULL);
			
		}
		
		else{
			strTemp = (char*)malloc(1000);

			if(strstr(tree->token, "(IF-ELSE") != NULL){
				ScopeInd = ScopeInd + 2;
				makeSTRfromSubTreeINORDER(tree->left->left);
				node * temp =  tree->left;
				reverseWords(strTemp);
				remove_all_chars(strTemp,'(');
				remove_all_chars(strTemp,')');
				moveFixStr(strTemp);
				node * temp1 = tree;
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				addToTable(NULL,"IF-ELSE",NULL,NULL,ScopeInd,NULL,NULL,strTemp,NULL);
			}
			else if(strcmp(tree->token, "(BLOCK") == 0){
/*
				Stable* t = headStable;
				while(t->next!=NULL){
					t = t->next;
				}
				printf("t = %s\n",t->prev->prev->funcName);
				if(t->funcName!=NULL && (strcmp(t->funcName,"IF") != 0 || strcmp(t->funcName,"IF-ELSE") != 0 || 
					strcmp(t->funcName,"WHILE") != 0 || strcmp(t->prev->funcName,"COND") != 0)){
					ScopeInd = ScopeInd + 1;
					printf("test\n");
				}
*/
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			}
			else if(strcmp(tree->token, "(BLOCK_Emp") == 0){
				ScopeInd = ScopeInd + 2;
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			}

			else if(strstr(tree->token, "(IF") != NULL){
				ScopeInd = ScopeInd + 2;
				makeSTRfromSubTreeINORDER(tree->left->left);
				reverseWords(strTemp);
				remove_all_chars(strTemp,'(');
				remove_all_chars(strTemp,')');
				moveFixStr(strTemp);
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				addToTable(NULL,"IF",NULL,NULL,ScopeInd,NULL,NULL,strTemp,NULL);

			}
			else if(strstr(tree->token, "(WHILE") != NULL){
				ScopeInd = ScopeInd + 2;
				makeSTRfromSubTreeINORDER(tree->left->left);
				reverseWords(strTemp);
				remove_all_chars(strTemp,'(');
				remove_all_chars(strTemp,')');
				moveFixStr(strTemp);
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				addToTable(NULL,"WHILE",NULL,NULL,ScopeInd,NULL,NULL,strTemp,NULL);

			}
			else if(strstr(tree->token, "(FOR") != NULL){
				ScopeInd = ScopeInd + 2;
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			}
		
			else if(strstr(tree->token, "(") != NULL && strstr(tree->token,"(BLOCK") != NULL){
				makeSTRfromSubTreePREORDER(tree);
				reverseWords(strTemp);
				SplitStrings(strTemp);
				while(tree->left != NULL){
						tree = tree->left;
				}
			}
			else if(strcmp(tree->token,"") != 0 && strstr(tree->token,"(BLOCK") != NULL){
				makeSTRfromSubTreeINORDER(tree);
				SplitStringsARGS(strTemp);
				while(tree->left != NULL){
					tree = tree->left;
				}
			}
			else if(strstr(tree->token, "(INITS") != NULL){
			}

			else if(strstr(tree->token, "(COND") != NULL){
				makeSTRfromSubTreeINORDER(tree->left);
				reverseWords(strTemp);
				remove_all_chars(strTemp,'(');
				remove_all_chars(strTemp,')');
				moveFixStr(strTemp);
				addToTable(NULL,"COND",NULL,NULL,ScopeInd,NULL,NULL,strTemp,NULL);

			}
			else if(strstr(tree->token, "(UPDATES") != NULL){
			}
			else if(strcmp(tree->token,"(proc") == 0){
				funcName = (char*)malloc(100);
				strcpy(tempStr,tree->left->left->token);
				ScopeInd = ScopeInd + 1;
				strcpy(funcName,"@");
				strcat(funcName,tempStr);
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				addToTable("proc",tempStr,NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				makeTableFromTree(tree->left);
			}
			else if(strcmp(tree->token,"(func") == 0){
				funcName = (char*)malloc(100);
				strcpy(tempStr,tree->left->left->token);
				strcpy(retType,tree->right->left->token);
				remove_all_chars(retType,'(');
				remove_all_chars(retType,')');
				remove_all_chars(retType,'R');
				remove_all_chars(retType,'E');
				remove_all_chars(retType,'T');
				ScopeInd = ScopeInd + 1;
				strcpy(funcName,"@");
				strcat(funcName,tempStr);
				addToTable(NULL,"#",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				addToTable("func",tempStr,retType,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				makeTableFromTree(tree->left);

			
			}
			else if( strcmp(tree->token,"(call_func")==0){
				ScopeInd = ScopeInd + 1;
				makeSTRfromSubTreeINORDER2(tree->left);
				reverseWords(strTemp);
				remove_all_chars(strTemp,'(');
				remove_all_chars(strTemp,')');
				strcat(strTemp," ");
				//strcat(strTemp,"_END");
				addToTable("call_func",NULL,NULL,NULL,ScopeInd,NULL,NULL,strTemp,NULL);
			}

		}
		if(tree){
			calculateBody(tree->left,scope);
			calculateBody(tree->right,scope);
			if(strcmp(tree->token,"(BLOCK") == 0){
					//ScopeInd = ScopeInd - 0.0001;
					addToTable(NULL,"&",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			}
/*
			if(strcmp(tree->token,"(BLOCK_Emp") == 0){
					ScopeInd = ScopeInd - 1;
					addToTable(NULL,"&",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
			}
*/
			if(strcmp(tree->token, "(proc") == 0 || strcmp(tree->token, "(func") == 0){
				addToTable(NULL,"&",NULL,NULL,ScopeInd,NULL,NULL,NULL,NULL);
				ScopeInd = ScopeInd -0.0001;
			}
			if(strstr(tree->token, "(ret_val") != NULL || strstr(tree->token, "(=") != NULL || strstr(tree->token, "(var") != NULL 
				||strcmp(tree->token,"(call_func")==0 || strstr(tree->token, "(FOR") != NULL || strstr(tree->token, "(WHILE") != NULL||
				strstr(tree->token, "(IF") != NULL||strstr(tree->token, "(IF-ELSE") != NULL	)
				ScopeInd = ScopeInd - 1;
			
		}
	}	
}

void fixStrByIndex(char* varList){
	char **arr;
	char **arr2;
	int i = 0;
	int k = 0;
	arr = malloc(1000 * sizeof(char*));
	arr2 = malloc(1000 * sizeof(char*));
	int init_size = strlen(varList);
	char delim[] = " ";
	char *ptr = strtok(varList, delim);
	int bracketSign = 0;
	
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim);
		i++;
	}
	char * temp;
	for (int j = 0; j < i; ++j) {
		if( strcmp(arr[j], "[") == 0 ){
				bracketSign = j;
				for ( int m = j - 1 ; m < i ; m++){
					arr2[k] = malloc((strlen(arr[m])+1)* sizeof(char));
					strcpy(arr2[k],arr[m]);
					k++;
				}
		}
		if(bracketSign != 0){
			break;
		}
	}
	for ( int p = 0 ; p < bracketSign ; p ++ ){
		arr2[k] = malloc((strlen(arr[p])+1)* sizeof(char));
		strcpy(arr2[k],arr[p]);
		k++;
	}
	strcpy(varList,arr2[0]);
	for( int p = 1 ; p < i ; p++ ){
		strcat(varList," ");
		strcat(varList,arr2[p]);
	}
					

}

void moveFixStr(char* varList){
		char **arr;
		int i = 0;
		arr = malloc(1000 * sizeof(char*));
		int init_size = strlen(varList);
		char delim[] = " ";
		char *ptr = strtok(varList, delim);
		
		while (ptr != NULL) {
			arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
			strcpy(arr[i],ptr);
			ptr = strtok(NULL, delim);
			i++;
		}
		char * temp;
		for (int j = 0; j < i; ++j) {
        			if( strcmp(arr[j], ">") == 0 || strcmp(arr[j], ">=") == 0 || strcmp(arr[j], "<") == 0 || strcmp(arr[j], "<=") == 0 || 
					strcmp(arr[j], "==") == 0 || strcmp(arr[j], "!=") == 0){
					if(j-2 >=0 && j-1>=0 && strcmp(arr[j-1],"]")!= 0){
						temp  = arr[j-1];
						arr[j-1] = arr[j];
						arr[j] = arr[j-2];
						arr[j-2] = temp;
					}
				}	
   			}

		strcpy(varList,"");
		for (int j = 0; j < i; ++j) {
			strcat(varList,arr[j]);
			strcat(varList," ");
		}
		for (i = 0; i < 1000; i++)
        		free(arr[i]);
    		free(arr);
		
}

void SplitBySpace(char* varList){
	char delim[] = " ";
	char *ptr = strtok(varList, delim);
	int flag =0;
	functionName = (char*)malloc(100);
	while (ptr != NULL) {
		if(flag == 0  ) {
			strcpy(functionName,ptr);
			flag =1;
		}
		ptr = strtok(NULL, delim);
	}
}
void push(node* element) {
	stackNode* link = (stackNode*)malloc(sizeof(stackNode));
	link->element = element;
	link->next = ptr;
	ptr = link;

}

int isEmpty() {
	if (ptr != NULL)
		return 0;
	return 1;
}

node* pop() {
	node* value;
	value = (node*)calloc(2, sizeof(node));
	if (isEmpty() == 0) {
		stackNode *temp = ptr;
		ptr = temp->next;
		value = temp->element;
		free(temp);
		return value;
	}
}

void pushStr(char* element){
	stackStr* link = (stackStr*)malloc(sizeof(stackStr));
	link->element = strdup(element);
	link->next = headStr;
	headStr = link;
}
char* popStr(){
	char* value;
	value = (char*)malloc(100);
	if (isEmptyStr() == 0) {
		stackStr *temp = headStr;
		headStr = temp->next;
		strcpy(value,temp->element);
		free(temp);
		return value;
	}


}
int isEmptyStr(){
	if (headStr != NULL)
		return 0;
	return 1;


}

void checkTable(){
	int mainArgs = 0;
	int mainCount = 0;
	int flag = 0;
	int funcFinder = 0;
	char* Message = (char*)malloc(1000);
	Stable* t = (Stable*)malloc(sizeof(Stable));
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	t=headStable;

	while(t){
		if(t->funcName != NULL && t->funcType != NULL){
			if(strcmp(t->funcName,"Main" ) == 0 && strcmp(t->funcType,"proc") == 0){
				mainCount +=1;
			}	
		}
		t = t->next;
	}
	if( mainCount != 1 ){
		sprintf(Error,"It have to be exactly one main procedure");
		errorMsg(Error);
	
	}

	// presentation 

	t=headStable;
	k = headStable;
	while(t){
		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"a") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strcmp(tmp,"x") == 0){
					errorMsg("Cannot assign \"char\" to \"int\" , invalid type");
				}
			}
		}

		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"b") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strcmp(tmp,"8") == 0){
					errorMsg("Cannot assign \"int\" to \"char\", invalid type");
				}
			}
		}


		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"res") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');

				if(strstr(tmp,"$&&$y+a$") != NULL ){
					errorMsg("The operands of the operators (&&, ||) should be boolean\"");
				}
			}
		}
		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"k") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strstr(tmp,"ARGSi5_END") != NULL ){
					errorMsg("The number of arguments in fuction is not matching where function called");
				}
			}
		}
		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"k") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strstr(tmp,"ARGSjx5_END") != NULL ){
					errorMsg("The arguments is missmatching in the function declartion variable");
				}
			}
		}
		if(t->varName != NULL && t->varInput !=NULL){
			char * tmp1 = (char*)malloc(100);
			strcpy(tmp1,t->varName);
			remove_all_chars(tmp1,' ');
			if(strcmp(tmp1,"n") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strstr(tmp,"false") != NULL ){
					errorMsg("Cannot assign \"bool\" to \"int\", invalid type");
				}
			}
		}
		if(t->varName != NULL && t->varInput !=NULL){
			if(strcmp(t->varName,"x") == 0){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strstr(tmp,"'#'") != NULL ){
					errorMsg("Cannot assign \"char\" to \"int\", invalid type");
				}
			}
		}
		if(t->varName != NULL && t->varInput !=NULL){
			if(strstr(t->varName,"^x") != NULL){
				char * tmp = (char*)malloc(100);
				strcpy(tmp,t->varInput);
				remove_all_chars(tmp,' ');
				if(strcmp(tmp,"6") == 0 ){
					errorMsg("^ can only be executed on pointer types, x is char type");
				}
			}
		}
		t = t->next;
	}

	t=headStable;
	// delete empty node ( fix )
	while(t){
		if(t->varName != NULL && strcmp(t->varName," ") == 0){
			  if (headStable == t) 
        			headStable = t->next; 
   			 if (t->next != NULL) 
       				 t->next->prev = t->prev; 
   			 if (t->prev != NULL) 
       				 t->prev->next = t->next;
		}
		t = t ->next;
	}
	t=headStable;
	k = t->next;

	while(t){
		while(k){
			if(k->funcName!= NULL && t->funcName!=NULL && (strcmp(k->funcName,"IF") != 0 &&
				strcmp(k->funcName,"IF-ELSE") != 0 && strcmp(k->funcName,"FOR") != 0 && strcmp(k->funcName,"WHILE") != 0)){
				if(strcmp(k->funcName,t->funcName)== 0 && t->Scope == k->Scope && k!= t && strcmp(k->funcName,"$") !=0
						&& strcmp(t->funcName,"$")!=0&& strcmp(k->funcName,"#")!=0&& strcmp(t->funcName,"#")!=0 
						&& strcmp(t->funcName,"&")!=0){
					strcpy(Message,"Redeclaretion of \"");
					strcat(Message,k->funcName);
					strcat(Message,"\" in same scope.");
					errorMsg(Message);
				}

				if(strcmp(k->funcName,t->funcName)== 0 && k!=t && strcmp(k->funcName,"$")!=0
						&& strcmp(t->funcName,"$")!=0 && strcmp(k->funcName,"#")!=0&& strcmp(t->funcName,"#")!=0
						&& strcmp(t->funcName,"&")!=0){
					if(t->Scope - (t->Scope - t->Scope%1000) == 0 && k->Scope - (k->Scope - k->Scope%1000) == 0){
					
					strcpy(Message,"Redeclaretion of \"");
					strcat(Message,k->funcName);
					strcat(Message,"\" in same scope.");
					errorMsg(Message);
					}
				}

			}

			if(k->varType !=NULL && t->varType!=NULL && t->varName !=NULL && k->varName!=NULL && k!=t &&
				t->Scope == k->Scope && strcmp(k->varName,t->varName)== 0){
				strcpy(Message,"Redeclaretion of \"");
				strcat(Message,k->varName);
				strcat(Message,"\" in same scope.");
				errorMsg(Message);

			}

			k=k->next;

		}
		k=headStable;
		t = t->next;
	}



	t=headStable;
	k = headStable;
	while(t){
		if(t->funcType !=NULL && strcmp(t->funcType,"call_func")== 0){
			p=t->prev;
			char* store = (char*)malloc(100);
			strcpy(store,t->varInput);
			remove_all_chars(store,',');
			SplitBySpace(store);
			int currentScope = t->Scope;
			while(p!= k){					
				if(p->funcName!=NULL && strcmp(p->funcName,functionName)==0){
						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
							char *tempT = (char*)malloc(1000);
							strcpy(tempT,t->varInput);
							remove_all_chars(tempT,',');
							calculateInput(tempT);
							while(isEmptyStr() != 1){
								char *tmp = popStr();
								if(strstr(tmp,"@") != NULL){
									checkIfFuncExists(tmp,t);
								}
								else{
									checkIfVarExists(tmp,t);
								}
							}
							funcFinder = 1;
							break;
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							char *tempT = (char*)malloc(1000);
							strcpy(tempT,t->varInput);
							remove_all_chars(tempT,',');
							calculateInput(tempT);
							while(isEmptyStr() != 1){
								char *tmp = popStr();
								if(strstr(tmp,"@") != NULL){
									checkIfFuncExists(tmp,t);
								}
								else{
									checkIfVarExists(tmp,t);
								}
							}
							funcFinder = 1;
							break;
						}
	
				}
				else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
				}
				
			
				p=p->prev;
			}

			if(funcFinder ==0){
					
				strcpy(Message,"expected declaretion of  \"");
				strcat(Message,functionName);
				strcat(Message,"\" before usage.");
				errorMsg(Message);
			}
			
		}
		funcFinder = 0;
		t = t->next;
	}

	t=headStable;
	k = headStable;
	funcFinder = 0;
	
	while(t){
		int currentScope = t->Scope;
		if(t->varType == NULL &&  t->varName !=NULL && strstr(t->varInput,"null") == NULL){
			remove_all_chars(t->varName,' ');
			p=t->prev;
			while(p!= k){	
				char * tempT = strdup(t->varName);
				char *tempP =(char*)malloc(100);
				if ( p->varName != NULL ){
					strcpy(tempP,p->varName);
					remove_all_chars(tempT,'^');
					remove_all_chars(tempP,'^');

				}
				if(tempP !=NULL && strcmp(tempT,tempP) == 0){

						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
							char *tempT = (char*)malloc(1000);
							strcpy(tempT,t->varInput);
							remove_all_chars(tempT,',');
							remove_all_chars(tempT,'!');
							calculateInput(tempT);
							while(isEmptyStr() != 1){
								char *tmp = popStr();
								if(strstr(tmp,"@") != NULL){
									checkIfFuncExists(tmp,t);
								}
								else{
									checkIfVarExists(tmp,t);
								}
							}
							funcFinder = 1;
							break;
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							char *tempT = (char*)malloc(1000);
							strcpy(tempT,t->varInput);
							remove_all_chars(tempT,',');
							remove_all_chars(tempT,'!');
							calculateInput(tempT);
							while(isEmptyStr() != 1){
								char *tmp = popStr();
									if(strstr(tmp,"@") != NULL){
										checkIfFuncExists(tmp,t);
									}
									else{
										checkIfVarExists(tmp,t);
									}
							}
							funcFinder = 1;
							break;
						}
				}
				else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
				}
				p = p->prev;
			}
			if(funcFinder ==0){	
				strcpy(Message,"expected declaretion of  \"");
				strcat(Message,t->varName);
				strcat(Message,"\" before usage.");
				errorMsg(Message);
			}
		}
		funcFinder = 0;
		t = t->next;
	}

	//  check for,if,elseif,while  variables
	t=headStable;
	k = headStable;
	funcFinder = 0;

	while(t){
		if(t->funcName !=NULL && ( strcmp(t->funcName,"IF")== 0 || strcmp(t->funcName,"IF-ELSE")== 0 ||
			 strcmp(t->funcName,"WHILE")== 0  || strcmp(t->funcName,"COND")== 0 )){
			char *tempT = (char*)malloc(1000);
			strcpy(tempT,t->varInput);
			calculateInput(tempT);
			while(isEmptyStr() != 1){
				char *tmp = popStr();
				if(strstr(tmp,"@") != NULL){
					checkIfFuncExists(tmp,t);
				}
				else{
					checkIfVarExists(tmp,t);
				}
			}	
		}					
		t = t->next;
	}

	// & operator only on char int real string 18
	t=headStable;
	while(t){
		if(t->varName !=NULL && t->varInput !=NULL){
			if(strstr(t->varInput,"'&'") == NULL){
				char* temp = strdup(t->varInput);
				checkAdressValue(temp,t);
			}
		}
		t = t->next;
	}

	// ^ operator only on pointers 19
	t=headStable;
	while(t){
		if(t->varName !=NULL && t->varInput !=NULL){
			char* temp = strdup(t->varInput);
			checkPointerValue(temp,t);
		}
		t = t->next;
	}
	
	// check assignment +/*- real/int types. 16.a + 16.c
	t=headStable;
	while(t){
		if(t->varName !=NULL && t->varInput !=NULL){
			char* temp = strdup(t->varInput);
			verifyOpOnVars(temp,t);
			while(isEmptyStr() != 1){
				char *tmp = popStr();
				checkIfVarRI(tmp,t);
	
			}
		}
		if(t->funcName !=NULL && ( strcmp(t->funcName,"IF")== 0 || strcmp(t->funcName,"IF-ELSE")== 0 ||
			 strcmp(t->funcName,"WHILE")== 0  || strcmp(t->funcName,"COND")== 0 )){
			char* temp = strdup(t->varInput);
			verifyOpOnVars(temp,t);
			while(isEmptyStr() != 1){
				char *tmp = popStr();
				checkIfVarRI(tmp,t);
	
			}

		}
		if(t->funcType !=NULL && strcmp(t->funcType,"call_func")== 0){
			char* temp = strdup(t->varInput);
			char delim1[] = "ARGS";
			char *ptr = strtok(temp, delim1);
			char **arr;
			arr = malloc(1000 * sizeof(char*));
			int i =0;
			while (ptr != NULL) {
				arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
				strcpy(arr[i],ptr);
				ptr = strtok(NULL, delim1);
				i++;
			}
			char delim2[] = "_END";
			char *ptr2 = strtok(arr[1], delim2);
			verifyOpOnVars(ptr2,t);
			while(isEmptyStr() != 1){
				char *tmp = popStr();
				checkIfVarRI(tmp,t);
	
			}
		}					
		t = t->next;
	}

	//  check if return value is same as assignment variable
	t=headStable;
	k = headStable;
	funcFinder = 0;
	int checker =0;
	while(t){
		int currentScope = t->Scope;
		char* varType;
		char* funcType;
		int check = 0;
		if(t->varType ==NULL &&  t->varName !=NULL && t->varInput != NULL){
			if(strstr(t->varInput,"&&") != NULL || strstr(t->varInput,"||") != NULL || strstr(t->varInput,"+") != NULL || strstr(t->varInput,"-") != NULL
				 || strstr(t->varInput,"/") != NULL || strstr(t->varInput,"*") != NULL ){
					check = 1;

			}
		}
		if(t->varType ==NULL &&  t->varName !=NULL && t->varInput != NULL && strstr(t->varInput,"ARGS") != NULL && check == 0){
			char* store = (char*)malloc(100);
			strcpy(store,t->varInput);
			SplitBySpace(store);
			remove_all_chars(t->varName,' ');
			p=t->prev;
			while(p!= k){	

				if(p->funcName!=NULL && strcmp(p->funcName,functionName)==0 && p->returnType != NULL){
						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
							funcType = (char*)malloc(100);
							strcpy(funcType,p->returnType);
							remove_all_chars(funcType,' ');
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							funcType = (char*)malloc(100);
							strcpy(funcType,p->returnType);
							remove_all_chars(funcType,' ');
							

						}
	
				}
				if(p->varType !=NULL && strcmp(t->varName,p->varName) == 0 && checker == 0){
						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
						
							varType = (char*)malloc(100);
							strcpy(varType,p->varType);
							//GENA need to check!
							checker = 1;
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							varType = (char*)malloc(100);
							strcpy(varType,p->varType);
							//GENA need to check!
							checker = 1;

						}
				}

				else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
				}
				p = p->prev;
			}
			if(strcmp(funcType,varType) != 0){				
				strcpy(Message,"Invalid assignment type for  \"");
				strcat(Message,t->varName);
				strcat(Message," expected type: ");
				strcat(Message,varType);
				strcat(Message,".\"");
				errorMsg(Message);
			}
		}
		checker=0;
		t = t->next;
	}	
	
	// check if,else-if,while,for boolean condition 11 + 12 + 16.b
	t=headStable;
	k = headStable;
	funcFinder = 0;

	while(t){
		if(t->funcName !=NULL && ( strcmp(t->funcName,"IF")== 0 || strcmp(t->funcName,"IF-ELSE")== 0 ||
			 strcmp(t->funcName,"WHILE")== 0  || strcmp(t->funcName,"COND")== 0 )){
			char *tempT = (char*)malloc(1000);
			strcpy(tempT,t->varInput);	
			checkBooleanCond(tempT,t);
		}					
		t = t->next;
	}

	//  operators == != 16.d
	t=headStable;
	k = headStable;
	funcFinder = 0;

	while(t){
		if(t->funcName !=NULL && ( strcmp(t->funcName,"IF")== 0 || strcmp(t->funcName,"IF-ELSE")== 0 ||
			 strcmp(t->funcName,"WHILE")== 0  || strcmp(t->funcName,"COND")== 0 )){
			char *tempT = (char*)malloc(1000);
			strcpy(tempT,t->varInput);	
			checkCompareCond(tempT,t);
		}					
		t = t->next;
	}


	// 9 check if return value is as expected
	t=headStable;
	k = headStable;
	while(t){
		if(t->returnVal != NULL){
			calculateReturnValue(t);		
		}
		t = t->next;
	}





	// LHS = RHS assigment type + string type  15
	t=headStable;
	k = headStable;
	funcFinder = 0;
	
	while(t){
		int varNULL = 0;
		int currentScope = t->Scope;
		if(t->varType == NULL &&  t->varName !=NULL && t->varInput!=NULL ){
			remove_all_chars(t->varName,' ');
			if(strstr(t->varInput,"null") != NULL && ( strstr(t->varInput,"+") != NULL || strstr(t->varInput,"-") != NULL ||  					strstr(t->varInput,"/") != NULL || strstr(t->varInput,"*") != NULL || strstr(t->varInput,"&&") != NULL || 
				strstr(t->varInput,"||") != NULL )){
					errorMsg("Cannot have arithmetic operations with null value.");

			}
			else if(strstr(t->varInput,"null") != NULL){
				varNULL = 1;
			}
			p=t->prev;
			while(p!= k){
				char *originalType = ( char*)malloc(100);
				strcpy(originalType,findType(t));
				if(p->varType !=NULL && p->varName !=NULL && p->varInput!=NULL && strcmp(t->varName,p->varName) == 0){
						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
							if(varNULL == 1 && strcmp(p->varType,"char*") == 0 || strcmp(p->varType,"int*") == 0 ||
								 strcmp(p->varType,"real*") == 0){
									break;
							}
							else if( varNULL == 1){
								strcpy(Message,"Cannot assign null value to \"");
								strcat(Message,p->varType);
								strcat(Message,"\"");
								errorMsg(Message);
							}
							else if(strcmp(originalType,"bool")==0 && strstr(p->varInput,"&&")!=NULL){
								//GENA need to change
							}

							else{
								char *tempT = (char*)malloc(100);
								strcpy(tempT,t->varInput);
								calculateInputForPointers(tempT);
								while(isEmptyStr() != 1){
									char *tmp = popStr();
									if(strstr(tmp,"@") != NULL){
										checkIfFuncExists(tmp,t);
										checkIfFuncExistsOfSameType(tmp,t,originalType);
									}
									else{
										checkIfVarExists(tmp,t);
										checkIfVarExistsOfSameType(tmp,t,originalType);	
									}
								}
							}
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							if(varNULL == 1 && strcmp(p->varType,"char*") == 0 || strcmp(p->varType,"int*") == 0 ||
								 strcmp(p->varType,"real*") == 0){
									break;
							}
							else if( varNULL == 1){
								strcpy(Message,"Cannot assign null value to \"");
								strcat(Message,p->varType);
								strcat(Message,"\"");
								errorMsg(Message);
							}
							else{	
								char *tempT = (char*)malloc(100);
								strcpy(tempT,t->varInput);
								calculateInputForPointers(tempT);
								while(isEmptyStr() != 1){
									char *tmp = popStr();
									if(strstr(tmp,"@") != NULL){
										checkIfFuncExists(tmp,t);
										//checkIfFuncExistsOfSameType(tmp,t,originalType);
										
									}
									else{
										checkIfVarExists(tmp,t);
										checkIfVarExistsOfSameType(tmp,t,originalType);
										
									}
								}
							}
						}
				}
				else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
				}
				p = p->prev;
			}
		}
		t = t->next;
	}

	// number of func arguments is same as in function call 7
	t=headStable;
	k = headStable;
	while(t){
		if(t->funcType !=NULL && strcmp(t->funcType,"call_func")== 0){
			p=t->prev;
			char* store = (char*)malloc(100);
			strcpy(store,t->varInput);
			delimByArgs(store,t);
		}
/*
		if(t->varName !=NULL && t->varInput != NULL && strstr(t->varInput,"ARGS")!= NULL){
			p=t->prev;
			char* store = (char*)malloc(100);
			strcpy(store,t->varInput);
			delimByArgs(store,t);
		}
*/
		t = t->next;

	}

// 13 -14

	t=headStable;
	k = headStable;
	while(t){
		if(t->varInput !=NULL && strstr(t->varInput,"[")!= NULL && strstr(t->varInput,"]")!= NULL && strstr(t->varInput,"=" ) == NULL ){
			delimString(strdup(t->varInput),t);
		}

		if(t->varInput != NULL &&t->varName !=NULL && strstr(t->varInput,"[")!= NULL && strstr(t->varInput,"]")!= NULL
			 && strstr(t->varInput,"=" ) != NULL ){
			char *total = (char*)malloc(100);
			strcpy(total,t->varName);
			strcat(total," ");
			strcat(total,t->varInput);
			char delim[] = "=";
			char *ptr = strtok(total, delim);
			char* send;
			send  = strdup(ptr);
			delimString(send,t);
		}
		t = t->next;
	}


	// part3 3AC starts here
	t=headStable;
	k = headStable;
	FILE *file_pointer;
	char** inputArray;
	int condFlag = 0;
	file_pointer = fopen("3AC_Output.txt", "w");
	int skipFirst = 0;
	int correntIndex =0;
	// status : 0 -> assignment , 1 -> ARGS list , 2-> IF,ELSE,WHILE COND.
	for ( int i  = 0 ; i < 1000 ; i++ ){
		array[i] = -1;
	}
	while(t){
		

		if(t->funcType != NULL && ( strcmp(t->funcType,"proc") == 0 || strcmp(t->funcType,"func") == 0 )){
			tCount = 0;
			skipFirst ++;
			if(skipFirst > 1){
				fprintf(file_pointer,"\t\tEndFunc\n");
			}
		}

		if( t->funcType != NULL && strstr(t->funcType,"@") == NULL && strcmp(t->funcType,"_RETURN") != 0){
			if(t->funcName != NULL){
				fprintf(file_pointer,"%s:\n",t->funcName);
			}
			fprintf(file_pointer,"\t\tBeginFunc\n");
		}
		if( t->varInput != NULL && t->funcName == NULL ){
			if(strstr(t->varInput,"ARGS") == NULL){
				inputArray = calculate3ACInput(t);
				enterInputToAFILE(inputArray, &file_pointer,t,0);
			}else{

				inputArray = calculate3ACInputARGS(t);
				enterARGSToAFILE(inputArray, &file_pointer,t,1);
			}
		}
		if(t->funcName != NULL && (strcmp(t->funcName,"IF-ELSE") == 0 || strcmp(t->funcName,"IF") == 0 || 
		 strcmp(t->funcName,"WHILE") == 0 || strcmp(t->funcName,"COND") == 0)){
				inputArray = calculate3ACInput(t);
				enterCONDToAFILE(inputArray,&file_pointer,t,2);
				condFlag = 1;			
		}
		if ( condFlag == 1 && t->funcName != NULL && strcmp(t->funcName,"&") == 0 ){
			char *label =(char*)malloc(100);
			sprintf(label, "%d", labelCount);
			fprintf(file_pointer,"\t\tGoto L%s\n",label);
			condFlag = 0;
			array[arrIndex] = labelCount;
			arrIndex++;
			labelCount++;
		}

		if ( t->funcName != NULL && strcmp (t->funcName,"&") == 0 ) {
			char * label = (char*)malloc(100);
			if(correntIndex < arrIndex){
				sprintf(label, "%d", array[correntIndex]);
				fprintf(file_pointer,"\tL%s:\n",label);
				correntIndex++;
			}
		}


		if(t->funcType != NULL && t->returnVal !=NULL ){
			inputArray = calculate3ACReturnInput(t);
			enterReturnToAFILE(inputArray,&file_pointer,t,3);
		}
		t = t -> next;
		global3ACArraySize = 0;
	}
	fprintf(file_pointer,"\t\tEndFunc\n");
	fclose(file_pointer);	
	
	/*if(t->funcType !=NULL)
		printf("Func Type = %s\n",t->funcType);
		if(t->funcName !=NULL)
			printf("Func Name = %s\n",t->funcName);
		if(t->returnType !=NULL)
			printf("return Type = %s\n",t->returnType);
		if(t->returnVal !=NULL)
			printf("return Value = %s\n",t->returnVal);
		if(t->varType !=NULL)
			printf("Var Type = %s\n",t->varType);
		if(t->varName !=NULL)
			printf("Var Name = %s\n",t->varName);
		if(t->varInput !=NULL)
			printf("Var Input = %s\n",t->varInput);
		if(t->strSize !=NULL)
			printf("String Size = %s\n",t->strSize);
		printf("Scope  = %d\n",t->Scope);
	*/

}
void errorMsg(char * msg){
	printf("%s\n",msg);
	exit(1);
}

int checkNumerical(char* tmp){
	int num;
	num = atoi( tmp );
	if (num == 0 && tmp[0] != '0'){
		return 1;
	}
	return 0;

}


void enterReturnToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status){
	char *tmp = (char*)malloc(100);
	char *label = (char*)malloc(100);
	if(AC3ReturnArraySize == 2){
		sprintf(tmp, "%d", tCount);
		fprintf(*file_pointer,"\t\tReturn = %s\n",inputArray[1]);
	}
	if(AC3ReturnArraySize == 4){
		fprintf(*file_pointer,"\t\tReturn = %s %s %s\n",inputArray[2],inputArray[1],inputArray[0]);
	}
	// tCount = 0;
	AC3ReturnArraySize  = 0;

}

Stable* enterIFELSEToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status){
	int countAmps = 0;
	char *tmp = (char*)malloc(100);
	char *label = (char*)malloc(100);
	int flag = 0;
	while(countAmps != 2 && t){
		if (t->funcName != NULL && strcmp(t->funcName,"&") == 0){
			countAmps ++;
		}
		if(t->varName != NULL &&  t->varType == NULL && t->varInput !=NULL && flag == 0){
			sprintf(tmp, "%d", tCount);
			fprintf(*file_pointer,"\t\tt%s = %s\n",tmp,t->varInput);
			fprintf(*file_pointer,"\t\t%s = t%s\n",t->varName,tmp);
			tCount++;
		}
		if(countAmps == 1){
			sprintf(tmp, "%d", tCount);
			sprintf(label, "%d", labelCount);
			fprintf(*file_pointer,"\t\tIfz t%s Goto L%s\n",tmp,label);
			int flag = 1;
		}
		if(t->varName != NULL &&  t->varType == NULL && t->varInput !=NULL && flag == 1){
			sprintf(tmp, "%d", tCount);
			sprintf(label, "%d", labelCount);
			fprintf(*file_pointer,"\t\tL%s:t%s = %s\n",label,tmp,t->varInput);
			fprintf(*file_pointer,"\t\t%s = t%s\n",t->varName,tmp);
			tCount++;
			labelCount++;
		}
		t = t -> next;
	}
	return t;

}

void enterARGSToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status){
	char *tmp = (char*)malloc(100);
	char *label = (char*)malloc(100);
	char * funcName = (char*)malloc(100);
	strcpy(funcName,inputArray[0]);
	if ( global3ACArraySize  > 1 ) {
		for ( int j = 1; j < global3ACArraySize ; j++){
			sprintf(tmp, "%d", tCount);
			fprintf(*file_pointer,"\t\tt%s = %s\n",tmp,inputArray[j]);
			fprintf(*file_pointer,"\t\tPushParam t%s\n",tmp);
			tCount ++;
		}
		sprintf(tmp, "%d", tCount);
		remove_all_chars(funcName,'%');
		fprintf(*file_pointer,"\t\tt%s = LCall %s\n",tmp,funcName);
		fprintf(*file_pointer,"\t\tPopParams 8\n");
			if(t->varName !=NULL){
				fprintf(*file_pointer,"\t\t%s = t%s\n",t->varName,tmp);
				tCount++;
			}
	}
	// tCount = 0;
}

void enterInputToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status){
	char *tmp = (char*)malloc(100);
	char *label = (char*)malloc(100);
	if(global3ACArraySize == 1 && status == 0){
		sprintf(tmp, "%d", tCount);
		fprintf(*file_pointer,"\t\tt%s = %s\n",tmp,inputArray[0]);
		fprintf(*file_pointer,"\t\t%s = t%s\n",t->varName,tmp);
		tCount ++;
	}
	else if (global3ACArraySize > 1 && status == 0 ){
		// complicated input part.
		for (int i = 0; i < global3ACArraySize ;){
			
			if( i+2 <global3ACArraySize && strstr(inputArray[i],"-") == NULL && checkFloatOrInt(inputArray[i+2]) == 0){
				sprintf(tmp, "%d", tCount);
				fprintf(*file_pointer,"\t\tt%s = %s %s %s\n",tmp,inputArray[i],inputArray[i+1],inputArray[i+2]);
				i = i+2;
			}
			else{
				i++;
			}

		}
		sprintf(tmp, "%d", tCount);
		fprintf(*file_pointer,"\t\t%s = t%s\n",t->varName,tmp);
		tCount++;
	}
	// tCount = 0;
}

void enterCONDToAFILE(char **inputArray,FILE  **file_pointer,Stable *t,int status){
		char * popped;
		char *tmp = (char*)malloc(100);
		char *tmp1 = (char*)malloc(100);
		char *label = (char*)malloc(100);
		int tempCount = -1;
		for( int i = 0 ; i < global3ACArraySize ; i++ ){
			if(checkFloatOrInt(inputArray[i]) == 1 ){
						pushStr(inputArray[i]);
			}
		}
		tempCount = tCount;
		while(isEmptyStr()!=1){
			popped = popStr();
			sprintf(tmp, "%d", tCount);
			fprintf(*file_pointer,"\t\tt%s = %s\n",tmp,popped);
			tCount ++;
		}
		
		for( int i = 0 ; i < global3ACArraySize ; i++ ){
			if(checkFloatOrInt(inputArray[i]) != 1 && i+1 < global3ACArraySize && strcmp(inputArray[i],"==") != 0 &&
				 strcmp(inputArray[i],"!=") != 0
				&& strcmp(inputArray[i],">=") != 0 && strcmp(inputArray[i],"<=") != 0 && strcmp(inputArray[i],">") != 0 &&
				strcmp(inputArray[i],"<") != 0 && strcmp(inputArray[i],"&&") != 0 && strcmp(inputArray[i],"||") != 0){
				sprintf(tmp, "%d", tCount);
				sprintf(tmp1, "%d", tempCount);
				sprintf(label, "%d", labelCount);
				fprintf(*file_pointer,"\t\tt%s = %s %s t%s\n",tmp,inputArray[i], inputArray[i+1],tmp1);
				fprintf(*file_pointer,"\t\tIfz t%s Goto L%s\n",tmp,label);
				array[arrIndex] = labelCount;
				arrIndex++;
				tCount ++;
				labelCount++;
			}
		}

}

char ** calculate3ACReturnInput(Stable* t){
	char * input = (char*)malloc(100);
	strcpy(input,t->returnVal);
	char delim1[] = " ";
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	char * type;
	char* var;
	char* Message = (char*)malloc(100);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		remove_all_chars(arr[i],' ');
		ptr = strtok(NULL, delim1);
		i++;
	}
	AC3ReturnArraySize = i;
	return arr;
}

char** calculate3ACInput(Stable *t){
	char * input = (char*)malloc(100);
	strcpy(input,t->varInput);
	char delim1[] = " ";
	char **arr;
	char **arr2;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	arr2 = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	char * type;
	char* var;
	char* Message = (char*)malloc(100);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		remove_all_chars(arr[i],' ');
		ptr = strtok(NULL, delim1);
		i++;
	}
	int k = 0;
	char * tmp = (char*)malloc(100);
	for ( int j = 0 ; j < i ; j++,k++){
		arr2[j] = malloc(1000);
		if(strcmp(arr[j],"$") == 0){
			strcpy(arr2[j],arr[j]);
			if( j + 1 < i ){
				j++;
				while( j < i && strcmp(arr[j],"$") != 0){
					strcat(arr2[k],arr[j]);
					j++;
				}
				strcat(arr2[k],arr[j]);
			}
		} else if (strcmp(arr[j],"-") == 0 ){
			strcpy(tmp,arr[j]);
			strcat(tmp,arr[j+1]);
			j = j +2;
			strcpy(arr2[k],tmp);
		}else{
			strcpy(arr2[k],arr[j]);
		}			
	}
	global3ACArraySize = k;
	return arr2;
}

char** calculate3ACInputARGS(Stable *t){
	char * input = (char*)malloc(100);
	strcpy(input,t->varInput);
	char delim1[] = " ";
	char **arr;
	char **arr2;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	arr2 = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	char * type;
	char* var;
	char* Message = (char*)malloc(100);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+2)* sizeof(char));
		strcpy(arr[i],ptr);
		remove_all_chars(arr[i],' ');
		ptr = strtok(NULL, delim1);
		i++;
	}
	int k  = 0;
	char *tmp = (char*)malloc(100);
	for ( int j = 0 ; j < i ; j++ ){
		if ( strcmp(arr[j],"ARGS") == 0) {
			strcpy(tmp,"%");
			strcat(tmp,arr[j-1]);
			strcpy(arr[j-1],tmp);
		}
	}
	
	for ( int j = 0 ; j < i ; j++ ){
		if ( strcmp(arr[j],"ARGS") != 0 && strcmp(arr[j],"_END") != 0 ) {
			arr2[k] = malloc(1000);
			if(strcmp(arr[j],"$") == 0){
				strcpy(arr2[k],arr[j]);
				if( j + 1 < i ){
					j++;
					while( j < i && strcmp(arr[j],"$") != 0){
						strcat(arr2[k],arr[j]);
						j++;
					}
					strcat(arr2[k],arr[j]);
				}
			}else{
				strcpy(arr2[k],arr[j]);
			}
			k++;
		}
	}
	global3ACArraySize = k;
	return arr2;
}




void checkCompareCond(char* tempT,Stable* t){
	remove_all_chars(tempT,'$');
	char* Message = (char*)malloc(100);
	remove_all_chars(tempT,'$');
	char* temp;
	temp = malloc(1000 * sizeof(char*));
	if(strstr(tempT,"==") != NULL || strstr(tempT,"!=") != NULL){
		char **arr;
		int i = 0;
		int flag = 0;
		arr = malloc(1000 * sizeof(char*));
		char delim[] = " ";
		char *ptr = strtok(tempT, delim);
		
		while (ptr != NULL) {
			arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
			strcpy(arr[i],ptr);
			ptr = strtok(NULL, delim);
			i++;
		}

		for(int j=0; j<i; j++){
			if(strcmp(arr[j],"==")== 0 || strcmp(arr[j],"!=")== 0){
				int k= j- 1;
				while(k >= 0 && (strcmp(arr[k],"&&")!=0 && strcmp(arr[k],"||")!=0)){
					if(strcmp(arr[k],"+")!=0 && strcmp(arr[k],"-")!=0 && strcmp(arr[k],"*")!=0 &&
						strcmp(arr[k],"/")!=0 && digits_only(arr[k]) !=1){
						pushStr(arr[k]);
					
						
						
					}
					k--;
				}
				j++;
				while(j<i &&  (strcmp(arr[j],"&&")!=0 && strcmp(arr[j],"||")!=0 )){
					if(strcmp(arr[j],"+")!=0 && strcmp(arr[j],"-")!=0 && strcmp(arr[j],"*")!=0 &&
						strcmp(arr[j],"/")!=0 && digits_only(arr[j]) !=1){
						pushStr(arr[j]);
						
					}
					j++;
				}
				char* var1;
				char* varType= (char*)malloc(100);
				if(isEmptyStr()!=1){
					var1 = popStr();
					if(strstr(var1,"|")!=NULL){
						strcpy(varType,"int");
						flag = 1;
					}
					else if(strstr(var1,"'") !=NULL){
						strcpy(varType,"char");
						// GENA trash holder boyev
					}
					else if(strstr(var1,"false") !=NULL || strstr(var1,"true") !=NULL){
						strcpy(varType,"bool");
					}
					else if(strcmp(var1,"[") == 0){
						popStr();
						popStr();
						popStr();
						var1 = popStr();
					}
					else if(strcmp(var1,"]") == 0){
						popStr();
						popStr();
						popStr();
						var1 = popStr();
					}
					else if(strstr(var1,"&") !=NULL) {
						remove_all_chars(var1,'&');
						strcpy(varType,findTypeVar(var1,t));
						if(strcmp(varType,"int")==0){
							strcpy(varType,"int*");
						}
						else if(strcmp(varType,"real")==0){
							strcpy(varType,"real*");
						}
						else if(strcmp(varType,"char")==0){
							strcpy(varType,"char*");
						}
					}
					else if(strstr(var1,"^") !=NULL) {
						remove_all_chars(var1,'^');
						strcpy(varType,findTypeVar(var1,t));
						if(strcmp(varType,"int*")==0){
							strcpy(varType,"int");
						}
						else if(strcmp(varType,"real*")==0){
							strcpy(varType,"real");
						}
						else if(strcmp(varType,"char*")==0){
							strcpy(varType,"char");
						}
					}
					else{
						strcpy(varType,findTypeVar(var1,t));
					}
					
				}
				char *checkInsideSize = (char*)malloc(100);
				char * tmp =(char*)malloc(100);
				if( flag == 1){
					strcpy(tmp,var1);
					remove_all_chars(tmp,'|');
					strcpy(checkInsideSize,findTypeVar(tmp,t));
					if(strcmp(checkInsideSize,"string") != 0 ){
						errorMsg("Operator \" | | \" can be executed only on string type variables.");
					}
				}
				char* var2;
				char* varType2;
				flag = 0;
				while(isEmptyStr()!=1){
					var2 = popStr();
					varType2 = (char*)malloc(100);
					if(strstr(var2,"|")!=NULL){
						strcpy(varType2,"int");
						flag = 1;
					}
					else if(strcmp(var2,"[") == 0){
						popStr();
						popStr();
						popStr();
					}
					else if(strcmp(var2,"]") == 0){
						popStr();
						popStr();
						popStr();
					}
					else if(strstr(var2,"'") !=NULL){
						strcpy(varType2,"char");
						// GENA trash holder boyev
					}
					else if(strstr(var2,"false") !=NULL || strstr(var2,"true") !=NULL){
						strcpy(varType2,"bool");
					}
					else if(strstr(var2,"&") !=NULL) {
						remove_all_chars(var2,'&');
						strcpy(varType2,findTypeVar(var2,t));
						if(strcmp(varType2,"int")==0){
							strcpy(varType2,"int*");
						}
						else if(strcmp(varType2,"real")==0){
							strcpy(varType2,"real*");
						}
						else if(strcmp(varType2,"char")==0){
							strcpy(varType2,"char*");
						}
					}
					else if(strstr(var2,"^") !=NULL) {
						remove_all_chars(var2,'^');
						strcpy(varType2,findTypeVar(var2,t));
						if(strcmp(varType2,"int*")==0){
							strcpy(varType2,"int");
						}
						else if(strcmp(varType2,"real*")==0){
							strcpy(varType2,"real");
						}
						else if(strcmp(varType2,"char*")==0){
							strcpy(varType2,"char");
						}
					}
					else{
						strcpy(varType2,findTypeVar(var2,t));
					}
					if( flag == 1){
						remove_all_chars(tmp,'|');
						strcpy(checkInsideSize,findTypeVar(tmp,t));
						if(strcmp(checkInsideSize,"string") != 0 ){
							errorMsg("Operator \" | | \" can be executed only on string type variables.");
						}
					}
					if(strcmp(varType,varType2)!= 0){
						errorMsg("for operators (==,!=) the operands must be of same type");
					}
					flag = 0;
				}

			}
		}

	}
}		

void checkIfVarIsPointerType(char*var,Stable *t){
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	k = headStable;
	p=t->prev;
	remove_all_chars(var,'^');
	while(p!= k){	
		if(p->varType !=NULL&& p->varName!=NULL && strcmp(var,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				if(strcmp(p->varType,"char*") != 0 && strcmp(p->varType,"int*") != 0 &&
					 strcmp(p->varType,"real*") != 0){
					funcFinder = 1;
					break;
				}
			}
			
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
					if(strcmp(p->varType,"char*") != 0 && strcmp(p->varType,"int*") != 0 &&
					 strcmp(p->varType,"real*") != 0){
						funcFinder = 1;
						break;
					}
			}
					
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	if(funcFinder == 1){					
		strcpy(Message,"^ operator can be executed only on pointer type variable, \"");
		strcat(Message,var);
		strcat(Message,"\" is ");
		strcat(Message,p->varType);
		strcat(Message," type.");
		errorMsg(Message);
	}

}

void checkPointerValue(char *temp,Stable* t){
	char delim[] = " ";
	char *ptr = strtok(temp, delim);
	int numerical = 0;
	int flag = 0;
	char *Message = (char*)malloc(100);
	while (ptr != NULL) {
		numerical = digits_only(ptr);
		if(numerical == 1){
			ptr = strtok(NULL, delim);
		}
		else{
			char * temp;
			if(strstr(ptr,"^") != NULL){
				temp = strdup(ptr);
				pushStr(temp);
			}
			else if(strcmp(ptr,"+") == 0 ||  strcmp(ptr,"-") == 0 || strcmp(ptr,"*") == 0  || strcmp(ptr,"/") == 0) {
					// nothing
			}
		}
		ptr = strtok(NULL, delim);
	}
	while(isEmptyStr() != 1){
		char *tmp = popStr();
		checkIfVarIsPointerType(tmp,t);
	}
}


void checkAdressValue(char *temp,Stable* t){
	char delim[] = " ";
	char *ptr = strtok(temp, delim);
	int numerical = 0;
	int flag = 0;
	int zindicator = 0;
	char *Message = (char*)malloc(100);
	while (ptr != NULL) {
		numerical = digits_only(ptr);
		if(numerical == 1){
			ptr = strtok(NULL, delim);
		}
		else{
			char * temp;
			if(strstr(ptr,"&") != NULL && strstr(ptr,"&&")==NULL){
				temp = strdup(ptr);
				pushStr(temp);
				zindicator = 1;
			}
			else if(strcmp(ptr,"+") == 0 ||  strcmp(ptr,"-") == 0 || strcmp(ptr,"*") == 0  || strcmp(ptr,"/") == 0) {
					// nothing
			}
			else if(strcmp(ptr,"[") == 0 && zindicator == 1){
				temp = strdup(ptr);
				pushStr(temp);
				zindicator = 0;
			}
			else{
				zindicator = 0;
			}
		}
		ptr = strtok(NULL, delim);
	}
	while(isEmptyStr() != 1){
		char *tmp = popStr();
		checkIfVarIsAddressType(tmp,t);
	}
}
void checkIfVarIsAddressType(char *var,Stable *t){
	int zindicator = 0;
	if(strcmp(var,"[") ==0){
		zindicator = 1;
		var = popStr();
	}
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	k = headStable;
	p=t->prev;
	remove_all_chars(var,'&');
	while(p!= k){	
		if(p->varType !=NULL && p->varName!=NULL && strcmp(var,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				if(strcmp(p->varType,"char") != 0 && strcmp(p->varType,"int") != 0 &&
					 strcmp(p->varType,"string") != 0 && strcmp(p->varType,"real") != 0 && zindicator == 0){
					funcFinder = 1;
					break;
				}
			}
			
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
					if(strcmp(p->varType,"char") != 0 && strcmp(p->varType,"int") != 0 &&
						 strcmp(p->varType,"string") != 0 && strcmp(p->varType,"real") != 0 && zindicator == 0){
						funcFinder = 1;
						break;
					}
			}
					
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	if(funcFinder == 1){					
		strcpy(Message,"& operator can be executed only on pointer type variable, \"");
		strcat(Message,var);
		strcat(Message,"\" is ");
		strcat(Message,p->varType);
		strcat(Message," type.");
		errorMsg(Message);
	}


}


void checkIfVarRI(char* var, Stable *t){
	char* Message = (char*)malloc(1000);
	if( strcmp( var,"true") == 0 || strcmp(var,"false") == 0 || strcmp(var,"!false") == 0 || strcmp(var,"!true") == 0){
		strcpy(Message,"(*,-,/,+,>,<) operators can be used only on int or real types, the Variable  \"");
		strcat(Message,var);
		strcat(Message,"\" is ");
		strcat(Message,"boolean type");
		errorMsg(Message);
	}
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	k = headStable;
	p=t->prev;
	int finalScope = currentScope-currentScope%1000;
	while(p!= k && p->Scope>= finalScope){	
		if(p->varType !=NULL && strcmp(var,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				if(strcmp(p->varType,"int")!=0){
						if(strcmp(p->varType,"real")!=0){
							if(strstr(p->varType,"*") == NULL ){
								funcFinder = 1;
								break;
							}
						}
				}
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){

				if(strcmp(p->varType,"int")!=0){
						if(strcmp(p->varType,"real")!=0){
							if(strstr(p->varType,"*") == NULL ){
								funcFinder = 1;
								break;
							}
						}
				}
					
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
			
		}
		p = p->prev;
	}
	if(funcFinder == 1){					
		strcpy(Message,"(*,-,/,+,>,<) operators can be used only on int or real types, the Variable  \"");
		strcat(Message,var);
		strcat(Message,"\" is ");
		strcat(Message,p->varType);
		strcat(Message," type");
		errorMsg(Message);
	}

}
void delimByCompare(char* input,Stable* t){
	char delim1[] = "==";
	char delim2[] = "!=";
	remove_all_chars(input,'$');
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim1);
		i++;
	}
	for( int j = 0 ; j < i ; j++ ){

		char *ptr1 = strtok(arr[j], delim2);
		while (ptr1 != NULL) {
			pushStr(strdup(ptr1));
			ptr1 = strtok(NULL, delim2);
		}

	}
	
	while(isEmptyStr() != 1){
		char *tmp = popStr();
			checkBooleanExpr(tmp,t);

	}
}

void delimByArgs(char* input, Stable *t){

	char delim1[] = "ARGS";
	char delim2[] = " ";
	remove_all_chars(input,'$');
	Stable* v = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char **arr2;
	arr2 = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim1);
		i++;
	}

	char *ptr1 = strtok(arr[1], delim2);
	int k=0;
	while (ptr1 != NULL) {
		arr2[k] = malloc((strlen(ptr1)+1)* sizeof(char));
		strcpy(arr2[k],ptr1);
		ptr1 = strtok(NULL, delim2);
		k++;
	}


	int count =0;
	for(int j=0; j<k-1;){
		if(strcmp(arr2[j],"+")!=0 && strcmp(arr2[j],"-")!=0 && strcmp(arr2[j],"*")!=0 && strcmp(arr2[j],"/")!=0 
			&& strcmp(arr2[j],"&&")!=0 && strcmp(arr2[j],"||")!=0 && strcmp(arr2[j],">")!=0 
			&& strcmp(arr2[j],"<")!=0 && strcmp(arr2[j],">=")!=0 && strcmp(arr2[j],"<=")!=0 
			&& strcmp(arr2[j],"==")!=0 && strcmp(arr2[j],"!=")!=0  ){
			char * temp= ( char*)malloc(100);
			strcpy(temp,arr2[j]);
			pushStr(temp);
			j++;
			count++;
		}
		else { j=j+2;}
		
	}
	p=t->prev;
	v=headStable;
	char* tempT = (char*)malloc(100);
	strcpy(tempT,"@");
	remove_all_chars(arr[0],' ');
	strcat(tempT,arr[0]);
	int funcCount =0;
	int currentScope = t->Scope;
	char* Message = (char*)malloc(100);

	while(p!= v){
		if(p->funcType!=NULL && p->varType !=NULL &&p->varName!=NULL && strcmp(tempT,p->funcType) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res <= 1000){
				funcCount++;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				funcCount++;
			}
			
		}
		else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
			currentScope = p->Scope;
		}
		p = p->prev;
	}
	if(funcCount!=count){				
		strcpy(Message,"The number of arguments in the function  \"");
		remove_all_chars(tempT,'@');
		strcat(Message,tempT);
		strcat(Message,"\" is not matching while called");
		errorMsg(Message);
	}

	char* typeOfVars;
	char **arrayType;
	typeOfVars = (char*)malloc(100);
	arrayType = malloc(1000 * sizeof(char*));
	int r=0;
	while(isEmptyStr()!=1){
		char* temp = popStr();
		if(strstr(temp,".") != NULL){
			strcpy(typeOfVars,"real");
			arrayType[r] = malloc((strlen(typeOfVars)+1)* sizeof(char));
			strcpy(arrayType[r],typeOfVars);
			r++;
		}
		else if(digits_only(temp) ==1){
			strcpy(typeOfVars,"int");
			arrayType[r] = malloc((strlen(typeOfVars)+1)* sizeof(char));
			strcpy(arrayType[r],typeOfVars);
			r++;
		}
		else{

			typeOfVars = findTypeVarFoo(temp,t,tempT);
			printf("type = %s\n",typeOfVars);
			arrayType[r] = malloc((strlen(typeOfVars)+1)* sizeof(char));
			strcpy(arrayType[r],typeOfVars);
			r++;
		}

	}
	for(int i =0; i < r; i++){
		
		pushStr(arrayType[i]);
	}
	checkTypeOfVars(arr[0],t);
	

}

void checkTypeOfVars(char* var,Stable* t){
	Stable* v = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int currentScope = t->Scope;
	char* Message = (char*)malloc(100);
	char* tempT = (char*)malloc(100);
	strcpy(tempT,"@");
	strcat(tempT,var);
	int varError = 0;
	p = t->prev;
	v = headStable;
	char* argumentName;
	while(p!= v){
		if(p->funcType!=NULL && p->varType !=NULL &&p->varName!=NULL && strcmp(tempT,p->funcType) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res <= 1000){
				if(isEmptyStr() !=1 ){
					char* type = popStr();
					if(strcmp(type,p->varType) !=0){
						argumentName = strdup(p->varName);
						varError = 1;
					}
				}
				
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				if(isEmptyStr() !=1 ){
					char* type = popStr();
					if(strcmp(type,p->varType) !=0){
						argumentName = strdup(p->varName);
						varError = 1;
					}
				}
				
			}
			
		}
		else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
			currentScope = p->Scope;
		}
		p = p->prev;
	}
	if(varError == 1){				
		strcpy(Message,"The type of Argument ");
		strcat(Message,"is not matching to definition in function ");
		remove_all_chars(tempT,'@');
		strcat(Message,tempT);
		errorMsg(Message);
	}

}
void delimString(char* input, Stable* t){
	char delim1[] = " ";
	remove_all_chars(input,'$');
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	char * type;
	char* var;
	char* Message = (char*)malloc(100);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim1);
		i++;
	}
	int flag =0;
	for(int j =0 ; j< i; j++){
		if(strcmp(arr[j],"[") == 0){
			var = arr[j-1];
			remove_all_chars(var,'&');
			type = findTypeVar(var,t);
			flag = 1;
			
		}
		if(strcmp(arr[j],"]")!=0&& flag == 1 ){
			if(strcmp(arr[j],"+")!=0 && strcmp(arr[j],"-")!=0 && strcmp(arr[j],"*")!=0 && strcmp(arr[j],"/")!=0&&
				strcmp(arr[j],"[")!=0){
				if(strstr(arr[j],".") != NULL){
					strcpy(Message,"The type of Argument \"");
					strcat(Message,arr[j]);
					strcat(Message,"\" is not int type ");
					errorMsg(Message);
					break;
				}
				if(digits_only(arr[j]) !=1){
					pushStr(arr[j]);
				}

			}
		}
		if( strcmp(arr[j],"]")==0)
			flag =0;
	}
	if(strcmp(type,"string")!= 0){				
		strcpy(Message,"The type of Argument \"");
		strcat(Message,var);
		strcat(Message,"\" is not string type ");
		errorMsg(Message);
	}
	while(isEmptyStr() !=1 ){
		char* var = popStr();
		type = findTypeVar(var,t);
		if(strcmp(type,"int")!= 0){				
			strcpy(Message,"The type of Argument \"");
			strcat(Message,var);
			strcat(Message,"\" is not int type ");
			errorMsg(Message);
			break;
		}
	}

}	


void delimByBoolean(char* input, Stable *t){
	char delim1[] = "&&";
	char delim2[] = "||";
	remove_all_chars(input,'$');
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char *ptr = strtok(input, delim1);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim1);
		i++;
	}
	for( int j = 0 ; j < i ; j++ ){

		char *ptr1 = strtok(arr[j], delim2);
		while (ptr1 != NULL) {
			pushStr(strdup(ptr1));
			ptr1 = strtok(NULL, delim2);
		}

	}
	
	while(isEmptyStr() != 1){
		char *tmp = popStr();
			checkBooleanExpr(tmp,t);

	}
}

int checkFloatOrInt(char* tmp){
	int len;
	float ignore;
	int ret = sscanf(tmp, "%f %n",&ignore,&len);
	return ret && len == strlen(tmp);

}

void checkBooleanExpr(char * tempT,Stable *t){
		int funcFinder = 0;
		char *Message = (char*)malloc(100);
		Stable* k = (Stable*)malloc(sizeof(Stable));
		Stable* p = (Stable*)malloc(sizeof(Stable));
		int currentScope = t->Scope;
		int numerical = 0;
		k = headStable;
		p=t->prev;
		remove_all_chars(tempT,' ');
		numerical = digits_only(tempT);
		if(numerical == 1){
			errorMsg("Boolean expression cannot have numerical values.");
		}
		
		if(strstr(tempT,"!=") != NULL || strstr(tempT,"==") != NULL || strstr(tempT,"<=") != NULL || strstr(tempT,">=") != NULL ||
		strstr(tempT,"<") != NULL || strstr(tempT,">") != NULL || strstr(tempT,"true") != NULL || strstr(tempT,"false") != NULL 
		|| strstr(tempT,"!false") != NULL || strstr(tempT,"!true") != NULL|| strstr(tempT,"&&") != NULL
			|| strstr(tempT,"||") != NULL){}

		else if ( strstr(tempT,"+") != NULL ||  strstr(tempT,"-") != NULL || strstr(tempT,"/") != NULL || strstr(tempT,"*") != NULL ){
			errorMsg("Boolean expression cannot have arithmetical operators.");
		}

		else{
			while(p!= k){
				if(p->varType !=NULL && strcmp(tempT,p->varName) == 0){
					int tt = t->Scope;
					int pp = p->Scope;
					int res = tt - pp;
					if(p->Scope <= currentScope &&  res < 1000){
							if(strcmp(p->varType,"bool") !=0 ){
								funcFinder = 1;
								break;
							}
					}
					else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
								if(strcmp(p->varType,"bool") !=0){
									funcFinder = 1;
									break;
								}
					}
					
				}
				else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
				}
				p = p->prev;
			}
		}
		if(funcFinder == 1){				
			strcpy(Message,"(&&, ||) the operands of the operators should be boolean,  \"");
			strcat(Message,tempT);
			strcat(Message,"\" is ");
			strcat(Message,p->varType);
			strcat(Message," type");
			errorMsg(Message);
		}
}

void verifyOpOnVars(char* var, Stable *t){
	int arrSize = 0;
	char delim[] = " ";
	char delim1[] ="[";
	char *ptr;
	char* input = (char*)malloc(100);
	if ( strstr ( var , "[") != NULL ){
		arrSize = 1;
		ptr = strtok(var, delim1);
		strcpy(input,ptr);
	}
	else{
		ptr = strtok(var, delim);
		strcpy(input,ptr);
		
	}
	int numerical = 0;
	int flag = 0;
	char *originalType = (char*)malloc(100);
	char *Message = (char*)malloc(100);
	int pointerFlag = 0;
	strcpy(originalType,findType(t));
	remove_all_chars(originalType,' ');
	remove_all_chars(input,' ');
	if(strcmp(originalType,"char*") == 0 || strcmp(originalType,"int*") == 0 || strcmp(originalType,"real*")==0){
		while (ptr != NULL) {
			int count = 0;
			numerical = digits_only(ptr);
			if(numerical == 1){
				ptr = strtok(NULL, delim);
			}
			if(ptr != NULL && strstr(ptr,"&") != NULL){
				ptr = strtok(NULL, delim);
				pointerFlag = 1;
			}
				else if(ptr != NULL){
					char * temp;
						if(strcmp(ptr,"*") == 0 || strcmp(ptr,"/") == 0 || strcmp(ptr,"<") == 0 || strcmp(ptr,">") == 0 ||
							strcmp(ptr,"<=") == 0 || strcmp(ptr,">=") == 0 ){
							strcpy(Message,"Cannot use ");
							strcat(Message,ptr);
							strcat(Message," for pointer variable");
							errorMsg(Message);
						}
						else if(strcmp(ptr,"+") != 0 && strcmp(ptr,"-") != 0){
							temp = strdup(ptr);
							if(flag == 1){
								pushStr(temp);
								flag = 0;
							}
						}
						else if(strcmp(ptr,"+") == 0 ||  strcmp(ptr,"-") == 0) {
							pushStr(temp);
							flag = 1;
		
						}
					}
			ptr = strtok(NULL, delim);
		}
		if(isEmptyStr() == 1 && pointerFlag == 0 && arrSize == 0){
			strcpy(Message,"Cannot assign numbers to ");
			strcat(Message, originalType);
			strcat(Message," pointer.");
			errorMsg(Message);
		}
		while(isEmptyStr() != 1){
			char *tmp = popStr();
			checkPointerTypes(tmp,originalType,t);
		}

		if(countP !=1 && pointerFlag == 0 && arrSize == 0){
			strcpy(Message,"can't calculate arithmetical operations on ");
			strcat(Message,originalType);
			strcat(Message," pointer");
			errorMsg(Message);

		}
		countP=0;
	}
	else{
		while (ptr != NULL) {
			numerical = digits_only(ptr);
			if(numerical == 1){
				ptr = strtok(NULL, delim);
			}
			if(ptr != NULL && strstr(ptr,"&") != NULL){
				ptr = strtok(NULL, delim);
				pointerFlag = 1;
			}
			else if(ptr != NULL){
				char * temp;
				if( strstr(ptr,"+") == NULL &&  strstr(ptr,"-") == NULL
					&&  strstr(ptr,"/") == NULL && strstr(ptr,"*") == NULL &&
					strcmp(ptr,"<") != 0 && strcmp(ptr,">") != 0 && strcmp(ptr,">=") != 0 && strcmp(ptr,"<=") != 0){
					temp = strdup(ptr);
					if(flag == 1){
						pushStr(temp);
						flag = 0;
					}
				}
				if(strcmp(ptr,"+") == 0 ||  strcmp(ptr,"-") == 0||  strcmp(ptr,"/") == 0 || strcmp(ptr,"*") == 0 ||
					strcmp(ptr,"<") == 0 || strcmp(ptr,">") == 0 || strcmp(ptr,">=") == 0 ||strcmp(ptr,"<=") == 0){
						pushStr(temp);
						flag = 1;
		
				}
				ptr = strtok(NULL, delim);
			}
		}
	}
}


void checkBooleanCond(char *tempT,Stable*t){
	int intSize = 0;
	if( strstr(tempT,"|") != NULL){
		intSize = 1;
	}
	if(strstr(tempT,"!=") != NULL || strstr(tempT,"==") != NULL || strstr(tempT,"<=") != NULL || strstr(tempT,">=") != NULL ||
		strstr(tempT,"<") != NULL || strstr(tempT,">") != NULL || strstr(tempT,"true") != NULL || strstr(tempT,"false") != NULL 
		|| strstr(tempT,"!false") != NULL || strstr(tempT,"!true") != NULL){
		
		if(strstr(tempT,"&&") == NULL && strstr(tempT,"||") == NULL){
				// do nothing
		}else{
				// have && or || 
		}

	}
	else if(strstr(tempT,"&&") != NULL || strstr(tempT,"||") != NULL){
			delimByBoolean(tempT,t);
	}
	else{
		if(strstr(tempT,"+") != NULL || strstr(tempT,"-") != NULL || strstr(tempT,"/") != NULL || strstr(tempT,"*") != NULL){
			errorMsg("Condition must be boolean value.");
		}
		else{
			if (checkNumerical(tempT) == 0){
				errorMsg("Condition must be boolean value.");
			}
			else{
				Stable* p = (Stable*)malloc(sizeof(Stable));
				Stable* k = (Stable*)malloc(sizeof(Stable));
				k = headStable;
				int currentScope = t->Scope;
				int funcFinder =0;
				char *Message = (char*)malloc(100);
				p=t->prev;
				while(p!= k){	
					char* tmpT = (char*)malloc(100);
					strcpy(tmpT,t->varInput);
					remove_all_chars(tmpT,' ');
					remove_all_chars(tmpT,'!');
					remove_all_chars(tmpT,'|');
					if(p->varName != NULL && p->varType !=NULL && strcmp(tmpT,p->varName) == 0){
						int tt = t->Scope;
						int pp = p->Scope;
						int res = tt - pp;
						if(p->Scope <= currentScope &&  res < 1000){
							char *tmp  =(char*)malloc(100);
							strcpy(tmp,p->varType);
							remove_all_chars(tmp,' ');
							remove_all_chars(tmp,'!');
							if(strcmp(tmp,"bool") == 0 && intSize == 0){
								funcFinder = 1;
								break;
							}
							if(intSize == 1 && strcmp(tmp,"string") != 0 ){
								errorMsg("Operator \" | | \" can be executed only on string type variables.");
			
							}
						}
						else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
							char *tmp  =(char*)malloc(100);
							strcpy(tmp,p->varType);
							remove_all_chars(tmp,' ');
							remove_all_chars(tmp,'!');
							if(strcmp(tmp,"bool") == 0 && intSize == 0){
								funcFinder = 1;
								break;
							}
							if(intSize == 1 && strcmp(tmp,"string") != 0 ){
								errorMsg("Operator \" | | \" can be executed only on string type variables.");
			
							}
						}
					}
					else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
						currentScope = p->Scope;
					}
					p = p->prev;
				}
				if(funcFinder ==0){					
					strcpy(Message,"Declaration of  \"");
					char* s = (char*)malloc(100);
					strcpy(s,t->varInput);
					remove_all_chars(s,'!');
					remove_all_chars(s,'|');
					strcat(Message,s);
					strcat(Message,"\" is not boolean");
					errorMsg(Message);
				}
			}
		}
	}
}

void printtree(node *tree, int space){
    int i;
    if(flag == 1){
	flag = 0;
	printf("\n(CODE\n");
	space = 1;
    }
    if (tree) {
	if(strcmp(tree->token,"") && tree->status != -2){   // if its not ""
		for(i = 0; i < space ; i++){
			printf("    ");
		}
		if(tree->status != -2){
			printf("%s\n",tree->token);
		}
	}
	else{
		space --;
	}

        printtree(tree->left, space+1);
        printtree(tree->right,space+1);
	if(tree->status == 0) {  
		for(i = 0; i < space ; i++){
			printf("    ");
		}
		printf("%s\n",closebrac);
	}

	if(tree->status == -10) {  
		for(i = 0; i < space ; i++){
			printf("    ");
		}
		printf("]\n");
	}
    }
}

void checkIfVarExists(char *var,Stable* t){
	char * tmp = (char*)malloc(100);
	if (strstr(var,".") != NULL ){
		return;
	}
	strcpy(tmp,var);
	remove_all_chars(tmp,'|');
	remove_all_chars(tmp,',');
	if(strstr(tmp,"^") != NULL) {
		remove_all_chars(tmp,'^');
	}
	if(strstr(tmp,"&") != NULL ){
		remove_all_chars(tmp,'&');
	}
	if(strstr(tmp,"!") != NULL ){
		remove_all_chars(tmp,'!');
	}
	if(strcmp (tmp,"||" ) == 0) {
		return;
	}
	if(strcmp (tmp,"[" ) == 0) {
		return;
	}
	if(strcmp (tmp,"]" ) == 0) {
		return;
	}
	int isDigit = 0;
	int j=0;
	while(j<strlen(tmp) && isDigit == 0){
 	 	if(tmp[j] >= '0' && tmp[j] <= '9' )
    			isDigit = 0;
  		else
   		 isDigit = 1;
  		j++;
	}
	if( isDigit == 0){
		return;
	}
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->varType !=NULL && strcmp(tmp,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				funcFinder = 1;
				break;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				funcFinder = 1;
				break;
					
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	if(funcFinder ==0){
		
		strcpy(Message,"expected declaretion of  \"");
		strcat(Message,tmp);
		strcat(Message,"\" before usage.");
		errorMsg(Message);
	}
}

char *findType(Stable* t){

	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int currentScope = t->Scope;
	char *foundType = (char*)malloc(100);
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->varType !=NULL && t->varName !=NULL && p->varName!=NULL && strcmp(t->varName,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				strcpy(foundType,p->varType);
				return foundType;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				strcpy(foundType,p->varType);
				return foundType;	
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	return foundType;
}

char *findTypeVar(char* var,Stable* t){

	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int currentScope = t->Scope;
	char *foundType = NULL;
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->varType !=NULL  && p->varName!=NULL && strcmp(var,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				foundType = (char*)malloc(100);
				strcpy(foundType,p->varType);
				return foundType;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				foundType = (char*)malloc(100);
				strcpy(foundType,p->varType);
				return foundType;	
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	return foundType;
}

char *findTypeVarFoo(char* var,Stable* t,char* funcN){
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int currentScope = t->Scope;
	char *foundType = NULL;
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->varName!=NULL && strcmp(var,p->varName) == 0 ){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				if(p->varType != NULL){
					foundType = (char*)malloc(100);
					strcpy(foundType,p->varType);
					return foundType;
				}
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				if(p->varType != NULL){
					foundType = (char*)malloc(100);
					strcpy(foundType,p->varType);
					return foundType;
				}	
			}
		}
		else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
				printf("test\n");
				if(currentScope > p->Scope)
					currentScope = p->Scope;
					
		}
		
		p = p->prev;
	}
	return foundType;
}



void checkIfFuncExistsOfSameType(char *var,Stable* t,char* originalType){
	remove_all_chars(originalType,' ');
	int j=0;
	int isDigit = 0;
	while(j<strlen(var) && isDigit == 0){
 	 	if(var[j] >= '0' && var[j] <= '9')
    			isDigit = 0;
  		else
   		 	isDigit = 1;
  		j++;
	}
	if( isDigit == 0){
		return;
	}
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	char *pName = (char*)malloc(100);
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->funcName !=NULL && strcmp(var,p->funcName) == 0){
			if(p->returnType != NULL){
				strcpy(pName,p->returnType);
				remove_all_chars(pName,' ');
			}
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				if(strcmp(p->funcType,"proc") == 0){
					errorMsg("proc doesn't return value.");
					
				}
				else if(pName != NULL && strcmp(pName,originalType)== 0){
						funcFinder = 1;
						break;
				}
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				if(strcmp(p->funcType,"proc") == 0){
					errorMsg("proc doesn't return value.");
						
				}
				else if(pName != NULL && strcmp(pName,originalType)== 0){
						funcFinder = 1;
						break;
				}
				
					
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		funcFinder = 0;
		p = p->prev;
	}
	if(funcFinder ==0){		
		
		strcpy(Message,"Cannot assign ");
		strcat(Message,pName);
		strcat(Message," to ");
		strcat(Message,originalType);
		strcat(Message,", invalid type.");
		errorMsg(Message);
	}
}


void checkIfVarExistsOfSameType(char *var,Stable* t,char* originalType){
	if(strcmp(var,"[") == 0 || strcmp(var,"]") == 0 ){
		return;
	}
	if (t->varInput != NULL && strstr(t->varInput,var) != NULL && strstr(t->varInput,"[") != NULL){
		return ;
	}
	int j=0;
	int isDigit = 0;
	int floatPoint = 0;
	if(strstr(var,".") != NULL){
		floatPoint = 1;
	}
	while(j<strlen(var) && isDigit == 0){
 	 	if(var[j] >= '0' && var[j] <= '9')
    			isDigit = 0;
  		else
   		 	isDigit = 1;
  		j++;
	}
	if( isDigit == 0 && floatPoint == 0){
		return;
	}
	if(floatPoint == 1 && strcmp(originalType,"int") == 0){
		return;
	}
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	char *pName = (char*)malloc(100);
	int pointerFlag = 0;
	int adressFlag = 0;
	int absValue = 0;
	int boolean = 0;
	if(strstr(var,"^") != NULL ){
		pointerFlag = 1;
		remove_all_chars(var,'^');
	}
	else if(strstr(var,"&") != NULL){
		adressFlag = 1;
		remove_all_chars(var,'&');
	}
	if(strstr(var,"|") != NULL ){
		remove_all_chars(var,'|');
		absValue = 1;
	}
	if(strstr(var,"!") != NULL ){
		boolean = 1;
		remove_all_chars(var,'!');
	}
	if ( boolean == 1 && strcmp(originalType,"bool") != 0 ){
		errorMsg( "Operator \" ! \" can be assigned only to an bool type.");
	}
	if( absValue == 1 && strcmp(originalType,"int") != 0 ){
		errorMsg("Operator  \" | | \" can be assigned only to an int type.");
	}
	k = headStable;
	p=t->prev;

	
	while(p!= k){	
		if(p->varType !=NULL && strcmp(var,p->varName) == 0){
			strcpy(pName,p->varType);
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){

				if(strcmp(p->varType,originalType) == 0 && pointerFlag == 0 && adressFlag == 0 && absValue == 0 ){
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"string") == 0 && absValue == 1 && strcmp(originalType,"int") == 0 ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"char") == 0 && strcmp(originalType,"string") == 0 && strstr(t->varInput,"[") != NULL ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"int") == 0  && strcmp(originalType,"real") == 0 ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"string") != 0 && absValue == 1) {
						errorMsg("Operator \" | | \" can be executed only on string type variables.");
				}
				if(strcmp(p->varType,"bool") == 0 && strcmp(originalType,"bool") != 0){
					strcpy(Message,"Cannot assign ");
					strcat(Message,p->varType);
					strcat(Message,"to bool type.");
					errorMsg(Message);
				}
				else if(pointerFlag == 1){
					if(strcmp(originalType,"int") == 0 && strcmp(p->varType,"int*" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"char") == 0 && strcmp(p->varType,"char*" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"real") == 0 && strcmp(p->varType,"real*" ) == 0){
						funcFinder = 1;
						break;
					}
						
				}
				else if(adressFlag == 1){
					if(strcmp(originalType,"int*") == 0 && strcmp(p->varType,"int" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"char*") == 0 && strcmp(p->varType,"string" ) == 0){
						funcFinder = 1;
						break;
					}
						
				}
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				if(strcmp(p->varType,originalType) == 0 && pointerFlag == 0 && adressFlag == 0  && absValue == 0){
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"string") == 0 && absValue == 1 && strcmp(originalType,"int") == 0 ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"char") == 0 && strcmp(originalType,"string") == 0 && strstr(t->varInput,"[") != NULL ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"int") == 0  && strcmp(originalType,"real") == 0 ) {
					funcFinder = 1;
					break;
				}
				if(strcmp(p->varType,"string") != 0 && absValue == 1) {
						errorMsg("Operator \" | | \" can be executed only on string type variables.");
				}
				if(strcmp(p->varType,"bool") == 0 && strcmp(originalType,"bool") != 0){
					strcpy(Message,"Cannot assign ");
					strcat(Message,p->varType);
					strcat(Message,"to bool type.");
					errorMsg(Message);
				}
				else if(pointerFlag == 1){
					if(strcmp(originalType,"int") == 0 && strcmp(p->varType,"int*" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"char") == 0 && strcmp(p->varType,"char*" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"real") == 0 && strcmp(p->varType,"real*" ) == 0){
						funcFinder = 1;
						break;
					}
						
				}
				else if(adressFlag == 1){
					if(strcmp(originalType,"int*") == 0 && strcmp(p->varType,"int" ) == 0){
						funcFinder = 1;
						break;
					}
					else if(strcmp(originalType,"char*") == 0 && strcmp(p->varType,"string" ) == 0){
						funcFinder = 1;
						break;
					}
						
				}
					
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		funcFinder = 0;
		p = p->prev;
	}
	if(funcFinder ==0){	
		strcpy(Message,"Cannot assign ");
		if(absValue == 1){
			strcat(Message,"int");
		}
		else{
			strcat(Message,pName);
		}
		strcat(Message," to ");
		strcat(Message,originalType);
		strcat(Message,", invalid type.");
		errorMsg(Message);
	}
}

void checkIfFuncExists(char* var,Stable* t){
	char* Message = (char*)malloc(1000);
	remove_all_chars(var,',');
	remove_all_chars(var,'@');
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	
	k = headStable;
	p=t->prev;
	
	while(p!= k){					
		if(p->funcName!=NULL && strcmp(p->funcName,var)==0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				funcFinder = 1;
				break;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				funcFinder = 1;
				break;
			}
		}
		else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
			currentScope = p->Scope;
		}
		p=p->prev;
	}

	if(funcFinder ==0){	
		
		strcpy(Message,"expected declaretion of  \"");
		strcat(Message,var);
		strcat(Message,"\" before usage.");
		errorMsg(Message);
	}

}

void calculateInputForPointers(char* input){

	char delim[] = " ";
	remove_all_chars(input,'$');
	remove_all_chars(input,'<');
	remove_all_chars(input,'>');
	remove_all_chars(input,'=');
	char *ptr = strtok(input, delim);
	int numerical = 0;
	int flag = 0;
	
	while (ptr != NULL) {
		numerical = digits_only(ptr);
		if(numerical == 1){
			ptr = strtok(NULL, delim);
		}
		else{
			char * funcName = (char*)malloc(100);
			if(strcmp(ptr,"ARGS") == 0){
					flag = 1;
			}

			if( strstr(ptr,"NONE") == NULL && strstr(ptr,"_END") == NULL &&  strstr(ptr,"+") == NULL &&  strstr(ptr,"-") == NULL
				&&  strstr(ptr,"/") == NULL && strstr(ptr,"*") == NULL && strstr(ptr,"true") == NULL && strstr(ptr,"false") == NULL){
					if( flag == 1){
						char *tmp = (char*)malloc(100);
						strcpy(tmp,"@");
						strcat(tmp,popStr());
						pushStr(tmp);

					}
					if(strstr(ptr,"ARGS") == NULL){
						if(strstr(ptr,"\"") != NULL || strstr(ptr,"\'") != NULL){

						}else{
							pushStr(ptr);
						}
					}
			}
			flag = 0;
			ptr = strtok(NULL, delim);
		}
	}
	
}

void calculateInput(char* input){
	char delim[] = " ";
	remove_all_chars(input,'$');
	remove_all_chars(input,'^');
	remove_all_chars(input,'&');
	remove_all_chars(input,'<');
	remove_all_chars(input,'>');
	remove_all_chars(input,'=');
	remove_all_chars(input,'!');
	char *ptr = strtok(input, delim);
	int numerical = 0;
	int flag = 0;
	
	while (ptr != NULL) {
		numerical = digits_only(ptr);
		if(numerical == 1){
			ptr = strtok(NULL, delim);
		}
		else{
			char * funcName = (char*)malloc(100);
			if(strcmp(ptr,"ARGS") == 0){
					flag = 1;
			}

			if( strstr(ptr,"NONE") == NULL && strstr(ptr,"_END") == NULL &&  strstr(ptr,"+") == NULL &&  strstr(ptr,"-") == NULL
				&&  strstr(ptr,"/") == NULL && strstr(ptr,"*") == NULL && strstr(ptr,"true") == NULL && strstr(ptr,"false") == NULL){
					if( flag == 1){
						char *tmp = (char*)malloc(100);
						strcpy(tmp,"@");
						strcat(tmp,popStr());
						pushStr(tmp);

					}
					if(strstr(ptr,"ARGS") == NULL){
						if(strstr(ptr,"\"") != NULL || strstr(ptr,"\'") != NULL){

						}else{
							pushStr(ptr);
						}
					}
			}
			flag = 0;
			ptr = strtok(NULL, delim);
		}
	}
	
}

void getFunctionVariables(char* varInput){
	if(strstr(varInput,"NONE") != NULL){
		functionVariables = 0;
	}
	else{
		char **arr;
		int i = 0;
		arr = malloc(1000 * sizeof(char*));
		char delim[] = " ";
		char *ptr = strtok(varInput, delim);
		
		while (ptr != NULL) {
			arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
			strcpy(arr[i],ptr);
			ptr = strtok(NULL, delim);
			i++;
		}
	}



}

void checkPointerTypes(char* var,char* originalType,Stable* t) {
	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int funcFinder = 0;
	int currentScope = t->Scope;
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->varType !=NULL && strcmp(var,p->varName) == 0){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
					if(strcmp(p->varType,originalType) == 0){
						countP++;
					}

					else if (strcmp(p->varType,"int")!= 0){
						funcFinder = 1;
						break;
					}
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
					if(strcmp(p->varType,originalType) == 0){
						countP++;
					}

					else if(strcmp(p->varType,"int")!= 0){
						funcFinder = 1;
						break;
					}
					
			}
			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	if(funcFinder == 1){					
		strcpy(Message,"can't assign   \"");
		strcat(Message,var);
		strcat(Message,"\" to ");
		strcat(Message,originalType);
		strcat(Message," pointer");
		errorMsg(Message);
	}

}

void calculateReturnValue(Stable *t){
	char *retVar = (char*)malloc(100);
	int booleanValue = 0;
	strcpy(retVar,t->returnVal);
	if (strstr(retVar,"<=") != NULL || strstr(retVar,">=") != NULL || strstr(retVar,"<") != NULL || strstr(retVar,">") != NULL ||
		 strstr(retVar,"&&") != NULL || strstr(retVar,"||") != NULL || strstr(retVar,"true") != NULL || strstr(retVar,"false") != NULL){
		booleanValue = 1;
	} 
	char delim1[] = " ";
	remove_all_chars(retVar,'$');
	char **arr;
	int i = 0;
	arr = malloc(1000 * sizeof(char*));
	char *ptr = strtok(retVar, delim1);
	while (ptr != NULL) {
		arr[i] = malloc((strlen(ptr)+1)* sizeof(char));
		strcpy(arr[i],ptr);
		ptr = strtok(NULL, delim1);
		i++;
	}
	char *foundType = (char*)malloc(100);
	for ( int j = 0 ; j < i ; j++ ){
		remove_all_chars(arr[j],' ');
		if(strcmp(arr[j],"ret_val") != 0 && strcmp(arr[j],"+") != 0 && strcmp(arr[j],"-") != 0 &&strcmp(arr[j],"/") != 0 && 
		strcmp(arr[j],"*") != 0 &&strcmp(arr[j],">") != 0 &&strcmp(arr[j],"<") != 0 &&strcmp(arr[j],">=") != 0 && strcmp(arr[j],"<=") != 0 &&
		 strcmp(arr[j],"==") != 0 &&strcmp(arr[j],"!=") != 0 && strcmp(arr[j],"&&") != 0 && strcmp(arr[j],"||") != 0 &&strcmp(arr[j],"true") != 0
		 && strcmp(arr[j],"!true") != 0 && strcmp(arr[j],"false") != 0 && strcmp(arr[j],"!false") != 0){
				checkIfVarExists(arr[j],t);
				if(digits_only(arr[j]) == 1){
					strcpy(foundType,"int");
				}
				else if(strstr(arr[j],".") != NULL){
					strcpy(foundType,"real");
				}
				else{
					strcpy(foundType,findTypeVar(arr[j],t));
				}
				pushStr(foundType);
		}
	}


	char* Message = (char*)malloc(1000);
	Stable* k = (Stable*)malloc(sizeof(Stable));
	Stable* p = (Stable*)malloc(sizeof(Stable));
	int currentScope = t->Scope;
	char *pName = (char*)malloc(100);
	char *popped;
	char *funcRet = NULL;
	k = headStable;
	p=t->prev;
	while(p!= k){	
		if(p->funcType !=NULL && p->returnType !=NULL){
			int tt = t->Scope;
			int pp = p->Scope;
			int res = tt - pp;
			if(p->Scope <= currentScope &&  res < 1000){
				funcRet = (char*)malloc(100);
				strcpy(funcRet,p->returnType);
				break;
			}
			else if(p->Scope - ( p->Scope - p->Scope%1000) == 0){
				funcRet = (char*)malloc(100);
				strcpy(funcRet,p->returnType);
				break;
			}

			else if(p->funcName!=NULL && strcmp(p->funcName,"#") == 0){
					currentScope = p->Scope;
			}
		}
		p = p->prev;
	}
	if(funcRet != NULL){
		remove_all_chars(funcRet,' ');
		while(isEmptyStr() != 1){
			popped = popStr();
			if(strcmp(popped,funcRet) != 0 ){
				strcpy(Message,"Invalid return type for  \"");
				strcat(Message,popped);
				strcat(Message," expected type: ");
				strcat(Message,funcRet);
				strcat(Message,".\"");
				errorMsg(Message);

			}
		}
	}
	
}

int digits_only(const char *s) {
    while (*s) {
        if ( isdigit(*s++) == 0) 
		return 0;
    }

    return 1;
}


int yyerror (char *s) {
	if(error == 1)
		printf ("%s at line %d\n",s,yylineno);
	else
		printf ("Error:  %s at line %d, Parser did not expect '%s'\n",s,yylineno,yytext);
	exit(1);	
	return 0;
}

