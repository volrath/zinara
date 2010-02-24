package zinara.lexer;
/* JFlex example: part of Java language lexer specification */

import java_cup.runtime.*;

import zinara.parser.*;

/**
 * This class is a simple example lexer.
 */
%%

%class Scanner
%public
%unicode
%cup
%line
%column

%{
  private Symbol symbol(int type) {
    return new Symbol(type, yyline, yycolumn);
  }
  private Symbol symbol(int type, Object value) {
    return new Symbol(type, yyline, yycolumn, value);
  }
%}

LineTerminator = \r|\n|\r\n
InputCharacter = [^\n]
WhiteSpace     = {LineTerminator} | [ \t\f]
//EmptyLine      = ^\ *[\n]*$
Letter         = [a-zA-Z]
Digit          = [0-9]
Alphanumeric   = [a-zA-Z0-9_\']

Comment = {MultipleComment} | {SimpleComment}

MultipleComment   = "/." [^.] ~"./" | "/." "."+ "./"
SimpleComment     = "//" {InputCharacter}* {LineTerminator}

Identifier  = {Letter} {Alphanumeric}*
Number      = {Digit}+


%%

 {Comment}                       {}
 {WhiteSpace}                    {}
// {EmptyLine}                     {}


 "main"                          { return symbol(sym.MAIN); }
 "end"                           { return symbol(sym.END); }
 {LineTerminator}                { return symbol(sym.SEMI); }


 "("                             { return symbol(sym.LPAREN); }
 ")"                             { return symbol(sym.RPAREN); }
 "["                             { return symbol(sym.LBRACKET); }
 "]"                             { return symbol(sym.RBRACKET); }
 "{"                             { return symbol(sym.LBRACET);}
 "}"                             { return symbol(sym.RBRACET);}


 "int"                           { return symbol(sym.INTEGER); }
 "float"                         { return symbol(sym.FLOAT); }
 "char"                          { return symbol(sym.CHAR); }
 "string"                        { return symbol(sym.STRING); }
 "bool"                          { return symbol(sym.BOOL); }
 "var"                           { return symbol(sym.VAR); }
 "def"                           { return symbol(sym.DEF); }
 ":"                             { return symbol(sym.DOUBLEDOT); }
 "copy"                          { return symbol(sym.COPY); }
 ","                             { return symbol(sym.COMMA);}
 

 "+"                             { return symbol(sym.PLUS);}
 "-"                             { return symbol(sym.UMINUS);}
 "/"                             { return symbol(sym.DIVIDE);}
 "%"                             { return symbol(sym.MOD);}
 "^"                             { return symbol(sym.PLUS);}


 ">"                             { return symbol(sym.GT);}
 "<"                             { return symbol(sym.LT);}
 ">="                            { return symbol(sym.GTE);}
 "<="                            { return symbol(sym.LTE);}
 "=="                            { return symbol(sym.SHEQ);}
 "<=>"                           { return symbol(sym.DEEQ);}
 "AND"                           { return symbol(sym.AND);}
 "OR"                            { return symbol(sym.OR);}
 "&"                             { return symbol(sym.SAND);}
 "|"                             { return symbol(sym.SOR);}
 "!"                             { return symbol(sym.NOEQ);}


 "for"                           { return symbol(sym.FOR);}
 "endfor"                        { return symbol(sym.ENDFOR);}
 "while"                         { return symbol(sym.WHILE);}
 "endwhile"                      { return symbol(sym.ENDWHILE);}
 "cycle"                         { return symbol(sym.CYCLE);}
 "on"                            { return symbol(sym.ON);}
 "do"                            { return symbol(sym.DO);}
 "endcycle"                      { return symbol(sym.ENDCYCLE);}
 "if"                            { return symbol(sym.IF);}
 "endif"                         { return symbol(sym.ENDIF);}


 "<<"                            { return symbol(sym.LTLT);}
 ">>"                            { return symbol(sym.GTGT);}
 "++"                            { return symbol(sym.PLUSPLUS);}
 "="                             { return symbol(sym.ASIG);}
 "return"                        { return symbol(sym.RETURN);}
 "print"                         { return symbol(sym.PRINT);}
 "read"                          { return symbol(sym.READ);}


 "true"                          { return symbol(sym.TRUE); }
 "false"                         { return symbol(sym.FALSE); }
 [0-9]+\.[0-9]*                  { return symbol(sym.FLOAT_V); }
 [0-9]*\.[0-9]+                  { return symbol(sym.FLOAT_V); }
 [0-9]+                          { return symbol(sym.INTEGER_V); }
 {Letter}{Alphanumeric}*         { return symbol(sym.IDENTIFIER); }


 .*     { throw new Error("Illegal character <"+yytext()+">"); }
