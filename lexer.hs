module Lexer (
Token(..),
Symbol_T(..),
Operator_T(..),
Keyword_T(..),
lexi,
c,
d,
e
) where

import Prelude hiding (EQ)

-- Tipi

-- Parole chiavi del linguaggio
data Keyword_T = LET | IN | END | LETREC | AND | IF | THEN | ELSE | LAMBDA
    deriving (Show,Eq)

-- Funzioni =, <=, head, tail, tupla, elemento singolo
data Operator_T = EQ | LEQ | CAR | CDR | CONS | ATOM
    deriving (Show,Eq)

-- Simboli (, ), =, +, -, *, /, ,, $ 
data Symbol_T = LPAREN | RPAREN | EQUALS | PLUS | MINUS | TIMES | DIVISION |VIRGOLA| DOLLAR
    deriving (Show,Eq)

data Token = Keyword Keyword_T | Operator Operator_T | Id String |
    Symbol Symbol_T | Number Integer | String String | Bool Bool | Nil |PROG_OK
    deriving (Show,Eq)



-- Funzioni di supporto

-- Testa se il carattere è un carattere valido per iniziare un identificatore, un operatore o una keyword
isAlphaChar c = c `elem` (['a' .. 'z'] ++ ['A' .. 'Z'])

-- Riconosce se c è un carattere numerico o no
isDigitChar c = c `elem` ['0' .. '9']

-- Testa se il carattere è un carattere valido per comporre un identificatore, un operatore o una keyword (ad eccezione del primo carattere)
isIdChar c = isAlphaChar c || isDigitChar c

-- Testa se il carattere è un separatore
isSeparator c = c `elem` "()=$,"

-- Testa se è uno spazio o accapo
isSpace c = c `elem` [' ', '\n', '\f', '\r', '\t']

isSymbol c = c `elem` "()=+-*/,"


{- data una stringa X la confronta con le parole chiavi e con gli operatori
   del Lisp Kit e se è una di queste cose, restituisce la corrispondente
   coppia token_lexema, altrimenti la considera un identificatore e
   restituisce la coppia (ID, STRINGA(X)) -}
-- Ricevo una parola e guardo se è una parola chiave, una funzione o una variabile
extractWord :: String -> Token
extractWord w = case w of
    "let"     -> Keyword LET --Parole chiavi
    "in"      -> Keyword IN
    "end"     -> Keyword END
    "letrec"  -> Keyword LETREC
    "and"     -> Keyword AND
    "if"      -> Keyword IF
    "then"    -> Keyword THEN
    "else"    -> Keyword ELSE
    "lambda"  -> Keyword LAMBDA
    
    "eq"      -> Operator EQ -- Funzioni
    "leq"     -> Operator LEQ
    "car"     -> Operator CAR
    "cdr"     -> Operator CDR
    "cons"    -> Operator CONS
    "atom"    -> Operator ATOM
    
    "true"    -> Bool True 
    "false"   -> Bool False
    
    "nil"     -> Nil
    
    otherwise -> Id w -- Variabili

--Ricevo un carattere e guardo se è uno dei simboli del linguaggio
toSymbol :: Char -> Symbol_T
toSymbol c = case c of
    '(' -> LPAREN
    ')' -> RPAREN
    '+' -> PLUS
    '-' -> MINUS
    '*' -> TIMES
    '/' -> DIVISION
    '=' -> EQUALS
    ',' -> VIRGOLA
    


{- Funzioni che implementano direttamente gli stati dell'automa. Osserva che
   non c'è ricorsione. Il passaggio dallo stato iniziale e principale I ad un
   altro stato è realizzato con un'invocazione. Poi si ritorna sempre a I e
   quindi basta il normale ritorno della funzione. -}

-- Stato N per riconoscere i numeri
{- n input numero segno
   n è la stringa in input
   numero è il numero elaborato finora
   segno è il segno del numero, true sse è negativo (rilevato da I) -}
--Continuo a chiamarla finché trovo cifre e aggiornando il numero da passare in ingresso. Termino quindi ritornando un Number
n :: String -> Integer -> Bool -> (Token, String)
n "" _ _ = error "Unexpected end of string"
n input@(c:l) num sign
    | isDigitChar c =
        let d = read [c] :: Integer
        in n l (num*10 + d) sign
    | otherwise = (Number((if sign then -1 else 1) * num), input)

-- Stato SC per riconoscere le stringhe tra virgolette
{- sc input stringa
   stringa è la stringa elaborata finora -}
--Continuo a chiamarla finché non trovo un ", concatenando man mano i caratteri. termino quindi ritornando una String
sc :: String -> String -> (Token, String)
sc "" _ = error "Unexpected end of string"
sc ('"':l) res = (String res, l)
sc (c:l) res = sc l (res ++ [c])

-- Stato S per raccogliere le stringhe che possono corrispondere ad identificatori, operatori prefissi o keyword
{- s input stringa
   stringa è l'identificatore elaborato finora -}
--Continuo a chiamarla finché trovo lettere, concatenando man mano i caratteri. Termino quindi chiamando extractWord, che si occuperà di ritornare un Id, una Keyword o un Operator
s :: String -> String -> (Token, String)
s "" _ = error "Unexpected end of string"
s input@(c:l) res
    | isIdChar c = s l (res ++ [c])
    | otherwise = (extractWord(res), input)


--Scorre ricorsivamente l'input
i :: String -> [Token]
i "" = error "Unexpected end of string"
i "$" = [(Symbol DOLLAR)]
i (' ':l) = i l
i input@(f:l)
    | isSymbol f = (Symbol $ toSymbol f) : (i l) --Guardo se è un simbolo del linguaggio. Se non lo è, può essere un numero, una parola o una keyword
    | otherwise = --Se non ho un simbolo speciale, ho un numero, una stringa o un identificatore
        let --Call chiama n, s o sc a seconda del valore del carattere che sto esaminando (", lettera, ~/cifra)
            call :: Char -> (Token, String)
            call '"' = sc l "" --Se ho ", allora sto per esaminare una stringa e chiamo sc (che è la funzione per gestire la stringa)
            call '~' = n l 0 True --Se ho ~, allora sto per esaminare un numero negativo e chiamo n (che è la funzione per gestire dei numeri)
            call f --Se non vale nessuno dei casi precedenti, non ho simboli, ma numeri o lettere 
                | isDigitChar f = n input 0 False --Ho un numero positivo e chiamo n (che è la funzione per gestire dei numeri)
                | isAlphaChar f = s input "" --Ho una lettera, quindi ho un identificatore e chiamo s (che è la funzione per gestire degli identificatori)
            call _ = error ("Lexical error starting with " ++ input)
            (tkl, tl) = call f
        in tkl : (i tl)


-- Funzione principale per l'analisi lessicale
lexi :: String -> [Token]
lexi = i

c = "letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X- 1 )and G = lambda ( H L ) if  eq ( L,  nil ) then L else cons( H(car( L ) ), G ( H, cdr ( L ) )) in G ( FACT, cons(1, cons(2, cons(3, nil))) ) end $";
d = "let x=cons(\"ab\", cons(\"cd\", nil)) in if true then cons(\"01\", x) else nil end $";
e = "let x=5 and y=6 in x+y+x end $";