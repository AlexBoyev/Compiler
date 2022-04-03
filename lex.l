%{
#include <stdlib.h>
#include <stdio.h>
extern int yylineno;
%}
%x comment
%%
"/%" 	{BEGIN(comment);}
<comment>"%/" {BEGIN(INITIAL);}
<comment>. {}
<comment>\n {}
bool {return BOOL;}
true {return _TRUE;}
false { return _FALSE;}
char {return CHAR;}
int {return INT;}
real {return REAL;}
string {return STRING;}
"int*" {return INT_POINT;}
"char*" {return CHAR_POINT;}
"real*" {return REAL_POINT;}
if {return IF;}
else {return ELSE;}
while {return WHILE;}
for {return FOR;}
var {return VAR;}
func {return FUNC;}
proc {return PROC;}
return {return RETURN;}
null {return _NULL;}
"+" {return PLUS;}
"-" {return MINUS;}
"/" {return DIVISION;}
"=" {return ASSIGNMENT;}
">" {return GREATER;}
"<" {return SMALLER;}
"!" {return NOT;}
"*" {return MULTIPLY;}
"^" {return DEREFERANCE;}
"&" {return ADDRESS;}
"&&" {return AND;}
"==" {return EQUAL;}
">=" {return EQUAL_GREATER;}
"<=" {return EQUAL_SMALLER;}
"!=" {return NOT_EQUAL;}
"||" {return OR;}

(0|[1-9][0-9]*) { return INT_NUM; }
[0-9]*\.[0-9]+([eE][-+]?[0-9]+)? {return REAL_NUM; }
0[x|X][0-9A-F]+ {return HEX_NUM; }
[a-zA-Z][0-9a-zA-Z]* {return ID;}

[\'][^\'][\'] {return LETTER;}
[\"][^\"]*[\"] {return STR_STRING;}
[ \t\f\v]+ /*skip tabs,white spaces*/
[\n] {yylineno = yylineno+1;}
. {return yytext[0];};

%%
