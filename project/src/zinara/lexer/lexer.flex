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
%cupdebug
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
InputCharacter = [^\n\r]
WhiteSpace     = [ \t\f]
EmptyLine      = [\ ]* {LineTerminator}
Letter         = [a-zA-Z]
Digit          = [0-9]
Alphanumeric   = [a-zA-Z0-9]

Comment = {MultipleComment} | {SimpleComment}

MultipleComment   = "/\." ~"\./" {WhiteSpace}* {LineTerminator}?
SimpleComment     = "//" {InputCharacter}* {LineTerminator}

Identifier  = {Letter} {Alphanumeric}*
Number      = {Digit}+

%%

{Comment}                        {}
{WhiteSpace}                     {}
^{EmptyLine}                     {}

 "main:" "\ "* {LineTerminator}     { return symbol(sym.MAIN); }
 "endmain" "\ "* {LineTerminator}?  { return symbol(sym.ENDMAIN); }

 {LineTerminator}                { return symbol(sym.SEMI); }

 "("                             { return symbol(sym.LPAREN); }
 ")"                             { return symbol(sym.RPAREN); }
 "["                             { return symbol(sym.LBRACKET); }
 "]"                             { return symbol(sym.RBRACKET); }
 "."                             { return symbol(sym.DOT); }
 ".."                            { return symbol(sym.DOTDOT); }
 "{"                             { return symbol(sym.LBRACET);}
 "}"                             { return symbol(sym.RBRACET);}

 "Int"                           { return symbol(sym.INTEGER); }
 "Float"                         { return symbol(sym.FLOAT); }
 "Char"                          { return symbol(sym.CHAR); }
 "String"                        { return symbol(sym.STRING); }
 "Bool"                          { return symbol(sym.BOOL); }
 "joined to"                     { return symbol(sym.JOINED); }
 "newtype"                       { return symbol(sym.NEWTYPE); }
 "aliastype"                     { return symbol(sym.ALIASTYPE); }
 "var"                           { return symbol(sym.VAR); }
 "def"                           { return symbol(sym.DEF); }
 "set_variant"                   { return symbol(sym.SET_VARIANT); }
 ":" "\ "* {LineTerminator}      { return symbol(sym.DOUBLEDOTTERM); }
 ":"                             { return symbol(sym.DOUBLEDOT); }
 "copy"                          { return symbol(sym.COPY); }
 ","                             { return symbol(sym.COMMA);}

 //retorno de una funcion
 "->"                            { return symbol(sym.LITTLE_ARROW);}

 "+"                             { return symbol(sym.PLUS);}
 "-"                             { return symbol(sym.MINUS);}
 "*"                             { return symbol(sym.TIMES); }
 "/"                             { return symbol(sym.DIVIDE);}
 "%"                             { return symbol(sym.MOD);}
 "^"                             { return symbol(sym.POW);}

 ">"                             { return symbol(sym.GT);}
 "<"                             { return symbol(sym.LT);}
 ">="                            { return symbol(sym.GTE);}
 "<="                            { return symbol(sym.LTE);}
 "=="                            { return symbol(sym.SHEQ);}
 "<=>"                           { return symbol(sym.DEEQ);}

 "and"                           { return symbol(sym.AND);}
 "or"                            { return symbol(sym.OR);}
 "&"                             { return symbol(sym.SAND);}
 "|"                             { return symbol(sym.SOR);}
 "xor"                           { return symbol(sym.XOR); }
 "!"                             { return symbol(sym.NOEQ);}

 "for"                           { return symbol(sym.FOR);}
 "in"                            { return symbol(sym.IN);}
 "endfor"                        { return symbol(sym.ENDFOR);}
 "as"                            { return symbol(sym.AS); }
 "enddef"                        { return symbol(sym.ENDDEF);}
 "while"                         { return symbol(sym.WHILE);}
 "endwhile"                      { return symbol(sym.ENDWHILE);}
 "cycle"                         { return symbol(sym.CYCLE);}
 "on"                            { return symbol(sym.ON);}
 "do"                            { return symbol(sym.DO);}
 "default"                       { return symbol(sym.DEFAULT);}
 "endcycle"                      { return symbol(sym.ENDCYCLE);}
 "if"                            { return symbol(sym.IF);}
 "elif"                          { return symbol(sym.ELIF);}
 "else"                          { return symbol(sym.ELSE);}
 "endif"                         { return symbol(sym.ENDIF);}
 "end"                           { return symbol(sym.END);}
 "continue"                      { return symbol(sym.CONTINUE);}
 "break"                         { return symbol(sym.BREAK);}

 "<<"                            { return symbol(sym.LTLT);}
 ">>"                            { return symbol(sym.GTGT);}
 "++"                            { return symbol(sym.PLUSPLUS);}
 "="                             { return symbol(sym.ASIG);}
 "return"                        { return symbol(sym.RETURN);}
 "print"                         { return symbol(sym.PRINT);}
 "read"                          { return symbol(sym.READ);}

 "True"                          { return symbol(sym.TRUE); }
 "False"                         { return symbol(sym.FALSE); }
 
 {Number}+                       { return symbol(sym.INTEGER_V,new Integer(Integer.parseInt(yytext()))); }
 {Number}"."{Number}+            { return symbol(sym.FLOAT_V,new Float(Float.parseFloat(yytext()))); }
 {Number}+"."                    { return symbol(sym.FLOAT_V,new Float(Float.parseFloat(yytext()+"0"))); }
 "."{Number}+                    { return symbol(sym.FLOAT_V,new Float(Float.parseFloat("0"+yytext()))); }
 \'[^\n\r]\'                     { return symbol(sym.CHAR_V,new Character(yytext().charAt(1))); }
 \"[^\n\r]*\"                    { return symbol(sym.STRING_V,yytext()); }
 {Letter} [a-zA-Z\'_0-9]*        { return symbol(sym.IDENTIFIER,yytext()); }

 .                               { throw new Error("Illegal character <"+yytext()+">"); }
