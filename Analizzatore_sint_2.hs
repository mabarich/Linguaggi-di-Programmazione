module Analizzatore_sint_2(
progdoll,d,prog_one) where

import Lexer
import Prelude hiding (EQ,exp)

data Exc a = Raise Exception | Return a
type Exception = String

instance Show a => Show (Exc a) where
 show (Raise e)= "ERRORE:" ++ e
 show (Return x) = "RAGGIUNTO:" ++ (show x)

instance Monad Exc where
 return x  = Return x
 (Raise e) >>= q   = Raise e
 (Return x) >>= q  = q x 

raise :: Exception -> Exc a
raise e = Raise e

data LKC = ETY | -- segnala epsilon productions
		   VAR String | NUM Integer | STRI String | BOO Bool |
		   NIL | ADD LKC LKC | SUB  LKC LKC | MULT  LKC LKC |
		   REM LKC LKC | DIV  LKC LKC | EQC LKC LKC | LEQC LKC LKC |
		   CARC LKC | CDRC LKC |CONSC LKC LKC | ATOMC LKC |
		   IFC LKC LKC LKC | LAMBDAC [LKC] LKC | CALL LKC [LKC] |
		   LETC LKC [(LKC,LKC)] | LETRECC LKC [(LKC,LKC)]
		   deriving(Show, Eq)

-- Queste funzioni guardano se un token corrisponde ad un particolare simbolo del linguaggio
-- Siccome in prog devo sapere quale tra i due costrutti LETC e LETRECC creare, e visto che il metodo è unico, ritorno una stringa da controllare per sapere che Return fare
rec_key::[Token]-> Exc([Token], String)
rec_key ((Keyword LET):b)    = Return (b, "LET")
rec_key ((Keyword LETREC):b) = Return (b, "LETREC")
rec_key (a:b)                = Raise ("trovato " ++ show(a) ++", atteso LET o LETREC")
rec_key  x                   = Raise ("ERRORE STRANO"  ++  show(x))

rec_in::[Token]->Exc([Token])
rec_in ((Keyword IN):b)= Return b
rec_in (a:b)           = Raise ("trovato " ++ show(a) ++ ", atteso IN")

rec_end::[Token]->Exc([Token])
rec_end ((Keyword END):b)= Return b
rec_end (a:b)            = Raise ("trovato " ++ show(a) ++ ", atteso END")


rec_then ((Keyword THEN):b)= Return b
rec_then (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso THEN")


rec_else ((Keyword ELSE):b)= Return b
rec_else (a:b)             = Raise ("trovato " ++ show(a) ++ ", atteso ELSE")


rec_lp ((Symbol LPAREN):b)=Return b
rec_lp (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso (")


rec_rp ((Symbol RPAREN):b)=Return b
rec_rp (a:b)              = Raise ("trovato " ++ show(a) ++ ", attesa )")


rec_virg ((Symbol VIRGOLA):b)=Return b
rec_virg (a:b)               = Raise ("trovato " ++ show(a) ++ ", attesa ,")



rec_equals ((Symbol EQUALS):b)= Return b
rec_equals (a:b)              = Raise ("trovato " ++ show(a) ++ ", atteso =")


--Metodo principale per la stampa
progdoll::[Token] -> String
progdoll x= show (prog x)

prog_one::[Token] -> Exc ([Token],LKC)
prog_one x= prog x

--Per ognuno dei seguenti metodi, chiamo nell'ordine corretto le funzioni che controllano se ho un terminale o un non terminale nel posto atteso
prog:: [Token] -> Exc ([Token],LKC)
--Prog ::= let Bind in Exp end | letrec Bind in Exp end
--Insieme di binding ed espressioni 
prog a 	= do 
			(x, tx)<-rec_key a --Guardo se ho un "let" o un "letrec". Gli faccio ritornare anche una stringa perche' in base all'inizio del programma devo sapere se ritornare un LETC o un LETRECC
			(y, ty)<-bind x --Guardo se ho uno o più binding
			z<-rec_in y --Guardo se ho "in"
			(w, tw)<-exp z --Guardo se ho una o più espressioni
			k<-rec_end w --Guardo se ho "end"
			Return (k, (if tx=="LET" then (LETC tw ty) else (LETRECC tw ty)))
   
 
exp::[Token]->Exc([Token],LKC)
--Exp ::= Prog | lambda ( Seq_Var ) Exp | ExpA | OPP ( Seq_Exp ) | if Exp then Exp else Exp
--Tutte le espressioni che possono ritornare un valore. Queste espressioni possono essere un sottoprogramma, delle funzioni anonime, delle operazioni, delle funzioni o dei blocchi if-then-else. Guardo caso per caso
--Casi sottoprogramma
exp a@((Keyword LET):b)    = (prog a)
exp a@((Keyword LETREC):b) = (prog a)
--Caso funzione anonima
exp ((Keyword LAMBDA):b)   = do
										n <- rec_lp  b
										(x, tx) <- seq_var n
										z <- rec_rp x
										(k, tk) <- exp z
										Return (k, (LAMBDAC tx tk)) 
--Casi funzioni
exp ((Operator CONS):b)    = do
										x<-rec_lp b
										(y, ty)<-exp x
										z<-rec_virg y
										(w, tw)<-exp z
										k<-rec_rp w
										Return (k, (CONSC ty tw)) 
exp ((Operator LEQ):b)     = do
										x<-rec_lp b
										(y, ty)<-exp x
										z<-rec_virg y
										(w, tw)<- exp z
										k<-rec_rp w
										Return (k, (LEQC ty tw)) 
exp ((Operator EQ):b)= 		do
										x<-rec_lp b
										(y, ty)<-exp x
										z<-rec_virg y
										(w, tw)<-exp z
										k<-rec_rp w
										Return (k, (EQC ty tw))
exp ((Operator CAR):b)= 	do
									(w,tw) <- exp b
									Return (w,(CARC tw))
exp ((Operator CDR):b)= 	do
									(w,tw) <- exp b
									Return (w,(CDRC tw))
exp ((Operator ATOM):b)= 	do	
									(w,tw) <- exp b
									Return (w,(ATOMC tw))
--Caso blocco if-then-else
exp ((Keyword IF):b)        = do
										(x,tx)<- exp b
										y<-rec_then x
										(z,tz)<-exp y
										w<-rec_else z
										(k,tk)<-exp w
										Return (k, IFC tx tz tk)
--Il caso di default lo uso per le operazioni
exp x                       =  expa x


bind::[Token]->Exc([Token],[(LKC,LKC)])
--Bind ::= var = Exp X
--variabile1=valore1. X indica ulteriori variabili (and variabile2=valore2 and variabile3=valore3)
bind ((Id a):b)            	=  do
										x<-rec_equals b
										(y, ty)<-exp x
										(k, tk)<-funx y --funx mi ritorna la lista pronta con le variabili successive, a cui devo concatenare la variabile corrente
										Return (k, if tk==[(ETY, ETY)] then [(VAR a, ty)] else [(VAR a, ty)]++tk) --Se da x mi arriva una lista [(ETY, ETY)], non la stampo e creo qua la lista da ritornare
--Se mi aspetto un binding ma non ho subito il nome di una variabile, do errore
bind (a:_)                  = Raise ("BINDER CON "++ show(a) ++" A SINISTRA")


funx::([Token])->Exc([Token],[(LKC,LKC)])
--X ::= and Bind | epsilon
--Concatenazione di altre variabili 
funx ((Keyword AND):b)     = bind b
funx a@((Keyword IN):b)    = Return (a,[(ETY, ETY)]) --Caso base. Uso a@ perché non posso consumare ora l'"in", quindi devo tenerlo
funx (a:_)                 = Raise ("DOPO BINDERS; TROVATO"++show(a))


--ExpA ::= T E1
--T e' il primo termine, mentre E1 contiene l'operazione da fare, il secondo termine e ulteriori termini e ulteriori operazioni. Ad esempio 2+(3+(4+(5)))
expa a = do
           	(x, tx)<- funt a
           	fune1 (x,tx)--Gli passo la traduzione del primo termine, perché devo gestire i due termini assieme e non in funzioni diverse

--T ::= F T1
--Guarda se ho un numero per l'oprazione con F. Per mescolare +,- con *,/ ho T1
funt a = do
           	(x, tx)<-funf a
           	funt1 (x,tx)



fune1::([Token], LKC) -> Exc([Token], LKC) 	
--E1 ::= OPA T E1 | epsilon
--Contiene l'operazione da fare, il secondo termine e ulteriori termini e operazioni da	aggiungere dopo	
--Caso somma
fune1 ((Symbol PLUS):b, tprec)	= do
											(x,tx)<- funt b
											(k,tk)<-fune1(x,tx)
											Return (k, (ADD tprec tk))--Costruisco l'albero con la traduzione precedente e la traduzione di tutto cio' che ho dopo
--Caso sottrazione
fune1 ((Symbol MINUS):b, tprec)	= do
											(x,tx)<-funt b
											(k,tk)<-fune1(x,tx)
											Return (k, (SUB tprec tk))--Costruisco l'albero con la traduzione precedente e la traduzione di tutto cio' che ho dopo
fune1 (x,tprec)		= Return (x,tprec)--Ho epsilon, quindi non devo aggiungere altro (e non posso costriure nulla perche' ho solo una traduzione)


funt1::([Token], LKC) -> Exc([Token], LKC) 
--T1 ::= OPM F T1 | epsilon
--Contiene l'operazione da fare, il secondo termine e ulteriori termini e operazioni da	aggiungere dopo	
--Caso moltiplicazione
funt1 ((Symbol TIMES):b, tprec)   = do
											(x,tx)<-funf b
											(k,tk)<-funt1(x,tx)
											Return (k, (MULT tprec tk))--Costruisco l'albero con la traduzione precedente e la traduzione di tutto cio' che ho dopo 
--Caso divisione
funt1 ((Symbol DIVISION):b, tprec)= do
											(x,tx)<-funf b
											(k,tk)<-funt1(x,tx)
											Return (k, (DIV tprec tk))--Costruisco l'albero con la traduzione precedente e la traduzione di tutto cio' che ho dopo 	
funt1 (x,tprec)                   = Return (x,tprec)--Ho epsilon, quindi non devo aggiungere altro (e non posso costriure nulla perche' ho solo una traduzione)


--F ::= var Y | exp_const | ( ExpA )
--F serve per costanti (ad esempio i termini da usare per +,-,*,/). Le chiamate di funzione (var è il nome della funzione e Y sono i parametri) vengono gestite da fX
funf (a:b)                 = if (exp_const a) then trad_exp_const2(a:b)--passo sia la testa sia la coda perché il return vero e proprio lo faccio in trad_exp_const2
                                              else fX (a:b)

--Continuazione di funf. Qui guardo se ho una chiamata di funzione
fX ((Id a):b)              = do
										(x,tx)<-fuy b --Lista dei parametri																	
										if tx == [ETY] then Return (x,(VAR a)) 
										else Return (x, (CALL (VAR a) tx)) --CALL nome [parametri]. Il nome della funzione va messo come "var x"
										
fX ((Symbol LPAREN):b)     = do
									  (x,tx)<- expa b
									  k<-rec_rp x
									  Return (k,tx)							  
fX (a:_)                   = Raise ("ERRORE in fX, TROVATO"++ show(a))



--Fa i return giusti in base al tipo del Token che sta in cima alla lista che riceve in ingresso. Usati per semplificare i return del primo caso di funf
trad_exp_const2::[Token] -> Exc([Token],LKC)
trad_exp_const2 ((Number a):b)  =  Return (b, NUM a)
trad_exp_const2 (Nil:b)         =  Return (b, NIL)
trad_exp_const2 ((Bool a):b)    =  Return (b, BOO a)
trad_exp_const2 ((String a):b)  =  Return (b, STRI a)

--Riconosce se un numero, una stringa, un booleano o un Nil
exp_const::Token ->Bool
exp_const (Number _)  =  True
exp_const Nil         =  True
exp_const (Bool _)    =  True
exp_const (String _)  =  True 
exp_const  _          = False


--Y ::= ( Seq_Exp ) | epsilon
--Y rappresenta la lista di parametri per una chiamata di funzione
fuy ((Symbol LPAREN):b)      =  do
										 (x, tx)<-seq_exp b
										 k<-rec_rp x
										 Return (k,tx)
--Epsilon
fuy x                        = Return (x, [ETY])


seq_var::[Token]-> Exc([Token],[LKC])
--Seq_Var ::= var Seq_Var | epsilon
--Rappresenta una lista di variabili per una funzione anonima. Ritorna una lista perche' il costrutto LAMBDAC si aspetta una lista come parametro
seq_var ((Id a):b)             = do
							(z,tz)<-seq_var b
							Return (z, [(VAR a)]++tz)--Mi ritorna la lista delle variabili successive, da concatenare alla variabile attuale
seq_var a@((Symbol RPAREN):b ) = Return (a, [])
seq_var (a:_)                  = Raise ("NON HO TROVATO Id o ); TROVATO INVECE" ++ show(a))



seq_exp::[Token]-> Exc([Token],[LKC])
--Seq_Exp ::= Exp V | epsilon
--Rappresenta una lista di espressioni da usare come parametri. Mi serve un separatore perche' altrimenti potrei considerare "a (b)" sia come una funzione sia come due esprezzioni. Ritorna una lista perche' il costrutto CALL si aspetta una lista come parametro
--Epsilon. In questo caso dovrei trovare una ), quindi faccio il controllo
seq_exp a@((Symbol RPAREN):b) = Return (a, [])
seq_exp a = do 
			(x,tx)<-exp a
			(z,tz)<-funV x--Mi ritorna la lista delle espressioni successive, da concatenare alla variabile attuale
			Return (z, ([tx]++tz))
			


funV::[Token]->Exc([Token],[LKC])
--V ::= ,Seq_Exp|epsilon
--La grammatica accetta anche (a,b,), quindi faccio un controllo
funV (c@((Symbol VIRGOLA):(Symbol RPAREN):b))       	=	Raise ("ERRORE in V, TROVATO"++ show(c))
funV ((Symbol VIRGOLA): b)       						=  do
															 seq_exp b
--Epsilon. Come prima, anche in questo caso mi aspetto di trovare una ), quindi controllo
funV a@((Symbol RPAREN):b)								= Return (a, [])
funV (a:_)                								= Raise ("NON HO TROVATO , o ); TROVATO INVECE" ++ show(a))

testc = progdoll (lexi c)
testd = progdoll (lexi d)
teste = progdoll (lexi e)
