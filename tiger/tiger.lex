type svalue = Tokens.svalue
type pos = int
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos

val stringStart = ref 0
val currentString = ref ""
fun appendString s = currentString := !currentString ^ s

val commentDepth = ref 0

fun nextLine pos = (lineNum := !lineNum + 1; linePos := pos :: !linePos)
fun err p1 = ErrorMsg.error p1

fun eof () = let
    val pos = hd(!linePos)
    val commentError = "Unclosed Comment Detected."
in (if !commentDepth <> 0
    then err pos commentError else ();
    Tokens.EOF(pos, pos))
end


 %%
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s COMMENT STRING STRING_ESCAPE STRING_LONG_ESCAPE STRING_CONTROL;
digit = [0-9];
digits = {digit}+;
alpha = [a-zA-Z];
alphas = {alpha}+;

%%
<INITIAL>\n	=> (nextLine (yypos); continue());
<INITIAL>(" "|\t|\r)  => (continue());

<INITIAL>"."    => (Tokens.DOT (yypos, yypos + 1));
<INITIAL>","	=> (Tokens.COMMA (yypos, yypos + 1));
<INITIAL>":"    => (Tokens.COLON (yypos, yypos + 1));
<INITIAL>";"    => (Tokens.SEMICOLON (yypos, yypos + 1));
<INITIAL>"+"    => (Tokens.PLUS (yypos, yypos + 1));
<INITIAL>"-"    => (Tokens.MINUS (yypos, yypos + 1));
<INITIAL>"*"    => (Tokens.TIMES (yypos, yypos + 1));
<INITIAL>"/"    => (Tokens.DIVIDE (yypos, yypos + 1));
<INITIAL>"="    => (Tokens.EQ (yypos, yypos + 1));
<INITIAL>"<>"   => (Tokens.NEQ (yypos, yypos + 2));
<INITIAL>"<"    => (Tokens.LT (yypos, yypos + 1));
<INITIAL>"<="   => (Tokens.LE (yypos, yypos + 2));
<INITIAL>">"    => (Tokens.GT (yypos, yypos + 1));
<INITIAL>">="   => (Tokens.GE (yypos, yypos + 2));
<INITIAL>"&"    => (Tokens.AND (yypos, yypos + 1));
<INITIAL>"|"    => (Tokens.OR (yypos, yypos + 1));
<INITIAL>":="   => (Tokens.ASSIGN (yypos, yypos + 2));
<INITIAL>"("    => (Tokens.LPAREN (yypos, yypos + 1));
<INITIAL>")"    => (Tokens.RPAREN (yypos, yypos + 1));
<INITIAL>"["    => (Tokens.LBRACK (yypos, yypos + 1));
<INITIAL>"]"    => (Tokens.RBRACK (yypos, yypos + 1));
<INITIAL>"{"    => (Tokens.LBRACE (yypos, yypos + 1));
<INITIAL>"}"    => (Tokens.RBRACE (yypos, yypos + 1));

<INITIAL>for    => (Tokens.FOR  (yypos, yypos + 3));
<INITIAL>do     => (Tokens.DO   (yypos, yypos + 2));
<INITIAL>else   => (Tokens.ELSE (yypos, yypos + 4));
<INITIAL>end    => (Tokens.END  (yypos, yypos + 3));
<INITIAL>if     => (Tokens.IF   (yypos, yypos + 2));
<INITIAL>in     => (Tokens.IN   (yypos, yypos + 2));
<INITIAL>let    => (Tokens.LET  (yypos, yypos + 3));
<INITIAL>nil    => (Tokens.NIL  (yypos, yypos + 3));
<INITIAL>of     => (Tokens.OF   (yypos, yypos + 2));
<INITIAL>then   => (Tokens.THEN (yypos, yypos + 4));
<INITIAL>to     => (Tokens.TO   (yypos, yypos + 2));
<INITIAL>type   => (Tokens.TYPE (yypos, yypos + 4));
<INITIAL>var  	=> (Tokens.VAR  (yypos, yypos + 3));
<INITIAL>array  => (Tokens.ARRAY (yypos, yypos + 5));
<INITIAL>break  => (Tokens.BREAK (yypos, yypos + 5));
<INITIAL>while  => (Tokens.WHILE (yypos, yypos + 5));
<INITIAL>function   => (Tokens.FUNCTION (yypos, yypos + 8));

<INITIAL>{digits}	=> (Tokens.INT (valOf (Int.fromString yytext), yypos,
                                    yypos + size yytext));

<INITIAL>{alpha}({alpha}|{digit}|"_")* => (Tokens.ID (yytext, yypos, yypos + size yytext));


<INITIAL>"\""   => (YYBEGIN STRING; currentString := ""; stringStart := yypos; continue ());
<STRING>"\\"    => (YYBEGIN STRING_ESCAPE; continue ());
<STRING>"\""    => (YYBEGIN INITIAL;
                    Tokens.STRING (!currentString, !stringStart, yypos + 1));
<STRING>\n      => (err (hd(!linePos)) "Unclosed String."; nextLine (yypos); 
                    YYBEGIN INITIAL; continue ());
<STRING>.       => (appendString yytext; continue ());
<STRING_ESCAPE>("\\"|"\"")  => (appendString yytext; YYBEGIN STRING; continue ());
<STRING_ESCAPE>\n           => (YYBEGIN STRING_LONG_ESCAPE; nextLine (yypos); continue ());
<STRING_ESCAPE>n            => (appendString "\n"; YYBEGIN STRING; continue ());
<STRING_ESCAPE>t            => (appendString "\t"; YYBEGIN STRING; continue ());
<STRING_ESCAPE>^            => (YYBEGIN STRING_CONTROL; continue ());
<STRING_ESCAPE>{digit}{3}   => (appendString (String.str (chr (valOf (Int.fromString yytext))));
                                YYBEGIN STRING; continue ());
<STRING_ESCAPE>.            => (err (hd(!linePos)) ("Illegal Escape Expression: " ^ yytext);
                                YYBEGIN STRING; continue ());

<STRING_LONG_ESCAPE>"\\"    => (YYBEGIN STRING; continue ());
<STRING_LONG_ESCAPE>(" "|\t|\f)+  => (continue ());
<STRING_LONG_ESCAPE>\n      => (nextLine (yypos); continue ());
<STRING_LONG_ESCAPE>.       => (err (hd(!linePos)) ("Improper Multi-line String: " ^ yytext); continue ());
<STRING_CONTROL>.   => (appendString (String.str (chr (ord (String.sub(yytext, 0)) - 64)));
                        YYBEGIN STRING; continue ());

<INITIAL>"/*"   => (YYBEGIN COMMENT; commentDepth := !commentDepth + 1; continue ());
<COMMENT>"/*"   => (commentDepth := !commentDepth + 1; continue ());
<COMMENT>"*/"   => (commentDepth := !commentDepth - 1;
                    if !commentDepth = 0 then YYBEGIN INITIAL else (); continue ());
<COMMENT>\n     => (nextLine (yypos); continue ());
<COMMENT>.      => (continue ());


<INITIAL>.       => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());
