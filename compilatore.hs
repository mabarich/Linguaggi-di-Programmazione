--Compilatore LKC --> SECD completo gennaio 2015
module Compilatore(
comp_one,
Secdexpr(..),
)
where

import Analizzatore_sint_2 hiding(LKC) 
data LKC = ETY | -- segnala epsilon productions
		   VAR String | NUM Integer | STRI String | BOO Bool |
		   NIL | ADD LKC LKC | SUB  LKC LKC | MULT  LKC LKC |
		   REM LKC LKC | DIV  LKC LKC | EQC LKC LKC | LEQC LKC LKC |
		   CARC LKC | CDRC LKC |CONSC LKC LKC | ATOMC LKC |
		   IFC LKC LKC LKC | LAMBDAC [LKC] LKC | CALL LKC [LKC] |
		   LETC LKC [(LKC,LKC)] | LETRECC LKC [(LKC,LKC)]
		   deriving(Show, Eq) --Mi dava problemi, quindi ho dovuto rimetterlo

data Secdexpr = Add | Sub |  Mult | Div | Rem | Eq | Leq | 
                Car | Cdr | Cons | Atom | Join | Rtn | Stop | Push |
                Ap | Rap | Ld (Integer, Integer) |
                Ldc LKC|
                Sel [Secdexpr] [Secdexpr]|
                Ldf [Secdexpr]
                deriving(Show, Eq)
				

-- funzioni per il calcolo dell'indirizzo di una variabile nell'ambiente 
-- Prende una lista e ricerca ricorsivamente una stringa al suo interno, ritornandone la sua posizione
position::String -> [LKC]-> Integer
position x [] = error "position: non trova la variabile"
position x ((VAR z):y) = if z==x then 0 else 1 + (position x y)
position x _ = error "position: trovata non VAR"

-- Cerca ricorsivamente se una stringa è contenuta o meno in una lista
member::String ->[LKC]->Bool
member x  [] = False 
member x ((VAR z):y) = if x == z then True else member x y
member x _ = error ("member: trovata non VAR"++ x)

-- Cerca ricorsivamente nell'ambiente una stringa e ne ritorna l'indirizzo nel formato (pos1, pos2)
location:: String->Integer-> [[LKC]]-> (Integer, Integer) 
location x _ []= error ("location non trova VAR"++ x)
location x ct (n:m) =   if (member x n) then (ct, (position x n)) else  (location x (ct+1) m)
 
-- ??
sexpr_reverse::[a]->[a]
sexpr_reverse []= []
sexpr_reverse (a:b)= (sexpr_reverse b) ++ [a]

--togliere variabili / espressioni da una lista di Binders
-- Da [(VAR "X", NUM 1),(VAR "Y", NUM 2), ...] a [VAR "X", VAR "Y", ...]
vars::[(a,b)]->[a]
vars []= [] 
vars ((x,y):r)= (x : (vars r))

-- Da [(VAR "X", NUM 1), (VAR "Y", NUM 2), ...] a [NUM 1, NUM 2, ...]
exprs::[(a,b)]->[b]
exprs []= [] 
exprs((x,y):r)= (y:(exprs r))

-- Analizza una lista di espressioni LKC, chiamando comp su ognuna
complist:: [LKC]-> [[LKC]] -> [Secdexpr]->[Secdexpr]
complist [] _ c = ((Ldc NIL):c) 
complist (x:y) n c = complist y n (comp x n (Cons:c))

-- Analizza una singola espressione LKC
-- e=programma da tradurre, n=ambiente statico, c=traduzione già fatta
comp:: LKC -> [[LKC]] -> [Secdexpr]->[Secdexpr]
comp e n c =  case e of (VAR x) -> ((Ld (location x 0 n)):c) -- Se ho una variabile, cerco il suo valore e lo carico in cima allo stack
                        (NUM x)-> (Ldc (NUM x)):c -- Se ho una costante, la carico in cima allo stack
                        (BOO x)-> (Ldc (BOO x)):c -- Come NUM  
                        (STRI x)-> (Ldc (STRI x)):c -- Come NUM   
                        NIL -> (Ldc NIL):c -- Come NUM   
                        (ADD x y)-> comp y n (comp x n (Add:c)) -- Chiamo comp in ordine, aggiornando man mano tra traduzione fatta
                        (SUB x y)-> comp y n (comp x n (Sub:c)) -- Come ADD
                        (MULT x y)-> comp y n (comp x n (Mult:c)) -- Come ADD
                        (DIV x y)-> comp y n (comp x n (Div:c)) -- Come ADD
                        (REM x y)-> comp y n (comp x n (Rem:c)) -- Come ADD
                        (EQC x y)-> comp y n (comp x n (Eq:c)) -- Come ADD
                        (LEQC x y)-> comp y n (comp x n (Leq:c)) -- Come ADD
                        (CARC x)-> comp x n (Car:c) -- Come ADD
                        (CDRC x)-> comp x n (Cdr:c) -- Come ADD
                        (CONSC x y)-> comp y n (comp x n (Cons:c)) -- Come ADD  
                        (ATOMC x)-> comp x n (Atom:c) -- Come ADD   
                        (IFC x y z)-> let thenp=(comp y n [Join]) -- Ramo true. Termino col Join la traduzione perché devo sistemare Control e Dump
                                          elsep=(comp z n [Join]) -- Ramo false. Termino col Join la traduzione perché devo sistemare Control e Dump
                                      in comp x n  ((Sel thenp elsep):c) -- Devo analizzare la guardia per metterla sullo stack
                        (LAMBDAC x y)-> (Ldf (comp y (x:n) [Rtn])):c  -- Crea la chiusura della funzione. Metto i parametri nell'ambiente e l'ultima istruzione è un Return
                        (LETC x y)-> complist (exprs(y)) n ((Ldf(comp x (vars(y):n) [Rtn])):Ap:c) -- LAMBDAC (metto le variabili locali in cima all'ambiente, come per i parametri e metto anche una Apply)+CALL (chiusura per il corpo). Uso exprs e vars perché ho i binders nella forma [(VAR "X", NUM 1), (VAR "Y", NUM 2), ...]                                 
                        (LETRECC x y)-> Push:complist (exprs(y)) (vars(y):n) ((Ldf(comp x (vars(y):n) [Rtn])):Rap:c) --Come LETC, solo che usa RecursiveApply
                        (CALL x y)-> complist y n (comp x n (Ap:c)) -- Apply, che serve per eseguire la funzione. Comp per il nome e complist per i parametri
                        _ -> [];

 
--esempi di prova

--c="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X*FACT(  X - 1 ) and G = lambda ( H L ) if  eq ( nil, L ) then L else c--ons( H(car( L ) ), G ( H, cdr ( L ) )) in G ( FACT, cons(1 ,cons(2, cons(3, nil))) ) end $"



--d= "let x= 5 and y= 6 in x*3 + y * 2* x + x*y end $"

comp_one x = comp x [] []