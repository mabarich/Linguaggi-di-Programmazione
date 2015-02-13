--INTERPRETE SECD COMPLETO in Haskell, Gennaio 2015
module Interprete(
interprete,
Valore(..),
fin,
k,
) where

import Lexer
import Compilatore --hiding (LKC)
import Analizzatore_sint_2 --hiding (LKC)
data LKC = ETY | -- segnala epsilon productions
		   VAR String | NUM Integer | STRI String | BOO Bool |
		   NIL | ADD LKC LKC | SUB  LKC LKC | MULT  LKC LKC |
		   REM LKC LKC | DIV  LKC LKC | EQC LKC LKC | LEQC LKC LKC |
		   CARC LKC | CDRC LKC |CONSC LKC LKC | ATOMC LKC |
		   IFC LKC LKC LKC | LAMBDAC [LKC] LKC | CALL LKC [LKC] |
		   LETC LKC [(LKC,LKC)] | LETRECC LKC [(LKC,LKC)]
		   deriving(Show, Eq)



--tipo che modella gli R-valori delle variabili. Si tratta dei valori da mettere nella pila S e nell'ambiente dinamico E. In 
--particolare CLO modella le chiusure.  *)

--OGA= place holder per l'ambiente *)
data Valore = V  LKC| OGA | --Valori|Segnaposti
              CLO [Secdexpr] [[Valore]]| --Chiusure (Corpo della funzione, Ambiente al momento della creazione)
              VLISTA [Valore] --Liste
              deriving(Show,Eq)

--datatype dei valori del Dump *)
data Dump = CONTR  [Secdexpr] | --Lista di espressioni del programma 
            TRIPLA [Valore][[Valore]][Secdexpr] | DUMMY --tripla se devo salvare sia lo stack, sia l'ambiente, sia il programma come nel caso di una chiamata di funzione
            deriving(Show,Eq)


--funzione che crea l'ambiente dinamico ricorsivo necessario per il trattamento della ricorsione. Serve nel caso Rap
lazyE::[Valore]-> [Valore]->[Valore] 
lazyE [] _ = [] 
lazyE (a:b) c = ((lazyClo a c):(lazyE b c))

lazyClo:: Valore -> [Valore]->Valore
lazyClo (CLO a b) c = (CLO a ((lazyE c c):b))
lazyClo(V x) _= (V x) 
lazyClo(VLISTA x) _= (VLISTA x)
lazyClo x _= error ("LazyClo trova valore incompatibile" ++ (show x))


--funzioni per la ricerca degli R-valori dati i loro indirizzi: usate da Ld *)
--Scarta ricorsivamente n-1 elementi, ritornandomi l'ennesimo
index::Integer ->[a]->a
index n  s= if n==0 then (head s) else (index (n-1) (tail s))  

--Ritorna il valore in posizione(a,b) dell'ambiente. 
--Prima scorre la lista principale, ritornando la lista in cui è presente l'elemento, e poi scorre quest'ultima
locate::(Integer, Integer)-> [[Valore]]->Valore
locate  (a,b)  e = (index b (index a e));
      
--Ritorna il valore effettivo del numero scartando NUM
extract_int (V (NUM x)) = x 
extract_int x = error ("trovato altro da intero" ++ (show x))

--funzioni per le liste di Valori VLISTA 
--Head
vhd (VLISTA (a:b)) = a 
vhd (VLISTA [])  = error "vhd trovata lista vuota"
vhd _ = error "vhd non trova VLISTA"

--Tail
vtl (VLISTA (a:b)) = VLISTA b  
vtl (VLISTA [])  = error "vtl trovata lista vuota";
vtl _ = error "vtl non trova VLISTA"

--True se riceve un elemento singolo (un V)
vatom (V k)= V (BOO True)
vatom _ = V (BOO False)     
                            
bool2s_espressione:: Bool ->LKC            
bool2s_espressione b = if b then (BOO True) else (BOO False)

--test di uguaglianza per il tipo Valore, si adatta ai tipi dei parametri con cui è invocata
eqValore::Valore -> Valore -> Bool
eqValore a@(V _) b = (eqV a b)
eqValore a@(VLISTA _) b = (eqVLISTA a b)
eqValore a  b = error ("uguaglianza tra chiusure"++ (show a) ++ (show b))

eqVLISTA::Valore -> Valore ->Bool
eqVLISTA (VLISTA []) (VLISTA [])= True 
eqVLISTA (VLISTA(a:b)) (VLISTA (c:d)) = (eqValore a c) && (eqVLISTA (VLISTA b) (VLISTA d))
eqVLISTA _ _= False


eqV (V a) (V b)= a==b
eqV _ _= False

 
--FUNZIONE PRINCIPALE   *)
--Stack, Enviroment, Control, Dump
--Passo ricorsivamente istruzione per istruzione e modifico SECD in base al tipo dell'istruzione analizzata
interprete:: [Valore] -> [[Valore]]-> [Secdexpr]-> [Dump]-> Valore
interprete s e c d = case (head c) of 
    Ld(b, n) -> let x = (locate (b,n) e)  in (interprete (x:s) e (tail c) d) --Prende (b,n) dall'ambiente e lo mette in cima allo stack
    Ldc k    -> case k of 
                        NIL -> (interprete ((VLISTA []):s) e (tail c) d) --Come prima, solo che metto una Lista sullo stack
		        _   -> (interprete ((V k):s) e (tail c) d) --Come prima, solo che mette un V e non direttamente il parametro
    Add -> let operand1 = extract_int (head s) 
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(NUM (operand1 + operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con la somma, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza
                         
    Sub -> let operand1 = extract_int (head s) 
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(NUM (operand1 - operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con la differenza, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza

    Mult -> let operand1 = extract_int (head s) 
                operand2 = extract_int(head (tail s))
            in  (interprete ((V(NUM (operand1 * operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con il prodotto, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza

    Div -> let operand1 = extract_int (head s) 
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(NUM (operand1 `div` operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con il quoziente, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza

    Rem -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(NUM (operand1 `mod` operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con il resto, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza

    Leq -> let operand1 = extract_int (head s)
               operand2 = extract_int(head (tail s))
           in  (interprete ((V(bool2s_espressione (operand1 <= operand2))):(tail (tail s))) e (tail c)  d) --Estrae i primi due elementi dallo stack e li sostituisce con un booleano, lasciando inalterari dump ed enviroment. (tail (tail s)) perché non li ho estratti in precedenza

    Eq -> case s of (w1:w2:w3) -> (interprete ((V (bool2s_espressione (eqValore w1 w2))):w3) e (tail c) d) --Estrae i primi due elementi dallo stack e li sostituisce con un booleano, lasciando inalterari dump ed enviroment. Uso il pattern matching, quindi non mi serve fare (tail (tail s))
		    _-> error "manca un argomento in Eq"
    
    Car -> (interprete ((vhd(head s) ):(tail s)) e (tail c) d) --Mette il primo valore della lista in cima allo stack al posto della lista stessa

    Cdr -> (interprete ((vtl(head s) ):(tail s)) e (tail c) d) -- Mette la coda della lista in cima allo stack al posto della lista stessa

    Cons -> case head (tail s) of (VLISTA x)-> (interprete  (VLISTA ((head s):x):(tail (tail s))) e (tail c) d) --Unisco i primi due elementi dello stack in un'unica lista
                                  _ -> error "CONS: il secondo argomento non e' una lista"
    
    Atom ->  (interprete ((vatom (head s)):(tail s)) e (tail c) d)

    Sel sl1 sl2 -> case head s of  (V (BOO True)) -> (interprete (tail s) e sl1 ((CONTR (tail c)):d)) --Salvo nel dump il programma corrente ed eseguo la parte true se in cima alla pila c'era un true
                                   (V (BOO False)) -> (interprete (tail s) e sl2 ((CONTR (tail c)):d)) --Salvo nel dump il programma corrente ed eseguo la parte false se in cima alla pila c'era un false
                                   _ -> error "non c'e' bool su s quando si esegue SEL"

    Join -> case (head d) of (CONTR c1) -> (interprete s e c1 (tail d)) --Ripristino il programma estraendolo dal dump
                             _ -> error "JOIN: il dump non contiene controllo"

    Ldf sl -> (interprete ((CLO sl e):s) e (tail c) d) --Crea la chiusura con l'ambiente corrente ed il codice da eseguire e la mette in cima allo stack

    Ap -> case (head s) of (CLO c1 e1) -> case (head (tail s)) of VLISTA x -> (interprete [] (x:e1) c1 ((TRIPLA (tail(tail s)) e (tail c)):d)) --Cambio di contesto. Salvo stack, enviroment e controllo nel dump, svuoto lo stack, sostituisco il programma e aggiungo i parametri (che stavano sotto la chiusura) all'enviroment della chiusura
                                                                  _  -> error "AP senza lista dei parametri"
                                            
                           _  -> error "AP senza chiusura su s"

    Rtn ->  case (head d) of (TRIPLA s1 e1 c1) -> (interprete ((head s):s1) e1 c1 (tail d)) --Ripristino l'enviroment, il programma e lo stack precedenti, aggiungendo il risultato della funzione allo stack
 			     _ ->  error  "RTN: non trovata TRIPLA su dump"   
                               
    Rap -> case (head s) of (CLO c1 e1) ->  case e1 of ([OGA]:re) -> case (head (tail s)) of (VLISTA vl2) -> (interprete [] ((lazyE vl2 vl2):re) c1 ((TRIPLA (tail (tail s)) (tail e) (tail c)):d))
                                                                                             _ -> error "manca lista dei parametri dopo OGA";
                                                       _ -> error "manca [OGA] sull'ambiente di chiusura ric"
                            _  -> error "RAP: non trovata chiusura su s"
                                   
    Push ->(interprete s  ([OGA]:e)  (tail c)  d) --Segnaposto nell'ambiente
     

    Stop -> (head s) --Ritorna la cima dello stack al termine dell'esecuzione
		                       
   



-- Mostra che si puo' usare letrec anche con binders non-funzionali. Le var a sinistra non devono apparire a destra 

--e = "let z=2 in letrec x= 2+z and y= 2*z in x*y*z end end $"

-- distribuisce FACT su una lista di interi *)

--val S="letrec  FACT = lambda ( X ) if  eq ( X, 0 ) then 1 else  X * FACT(  X - 1 )"^
--" and G = lambda ( H  L ) if  eq ( nil, L ) then L else cons( H(car( L ) ), G ( H , cdr ( L ) ))"^
--" in G ( FACT, cons( 6 ,cons( 7, cons( 8 , nil))) ) end $";

--(*considera liste di liste Z e produce una lista semplice che contiene tanti interi quante sono le liste contenute in Z e l'intero 
--corrispondente ad una lista contenuta in Z è la somma dei fattoriali dei suoi elementi: f2=fattoriale, f1=calcola somma dei fattori--ali degli elementi di una 
--lista di interi e f0 distribuisce f1 sulle liste contenute in Z *)

f="letrec f0 = lambda ( x ) letrec f1 = lambda(y) letrec f2=lambda (z) if eq(z , 1) then 1 else z * f2( z - 1 ) in if eq( y , nil ) then 0 else f2 ( car ( y ) ) + f1 ( cdr (y)) end  in if eq(x , nil) then nil else cons (f1 ( car ( x )),f0 ( cdr ( x ) ) ) end in f0( cons (cons (3 , cons (3 , nil)), cons( cons (3 , nil), nil))) end $"


--(* esempio di funzione che restituisce una funzione locale *)

--g="let f1 = lambda() letrec f2=lambda (z) if eq(z , 1) then 1 else z * f2( z - 1 ) in f2 end in let x=f1() in x(8) end end $"

--fin semplifica la chiamata di interprete
fin se=(interprete [] [] (se ++ [Stop]) [])

--k esegue la sequenza di passi sulla stringa f e da il risultato finale
k()= fin(comp_one(prog_one(lexi(f))))

ex = "let x=5 and y=6 in x+y+x end $";
test=do
		(l, tl)<-prog_one(lexi(ex))
		fin(comp_one(tl))