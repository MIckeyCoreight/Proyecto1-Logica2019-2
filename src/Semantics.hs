module Semantics where

import Syntax
import Data.List

type Estado = [VarP]

--Recibe una lista con el estado de las variables proposicionales
--y evalua una proposici車n con ese estado.
interp :: Estado -> Prop -> Bool
interp e phi = case phi of
    TTrue -> True
    FFalse -> False
    V x -> elem x e
    Neg p -> not (interp e p)
    Conj p q -> (interp e p) || (interp e q)
    Disy p q -> (interp e p) && (interp e q)
    Imp p q -> not (interp e p) || (interp e q)
    Equiv p q -> (interp e p) == (interp e q)

--Recibe una proposici車n y nos devuelve una lista con todos los estados posibles para la misma.
estados :: Prop -> [Estado]
estados phi = subconj (vars phi)

--Recibe una proposici車n y nos regresa una lista con las variables proposicionales
--que vuelven verdadera nuestra proposici車n.
modelos :: Prop -> [Estado]
modelos phi = [e | e <- estados phi, interp e phi]

--Recibe una proposici車n y nos dice si era una tautolog赤a.
tautologia :: Prop -> Bool
tautologia phi = (modelos phi) == (estados phi)

--Recibe un estado y una proposici車n y nos regresa la interpretaci車n del mismo
--es decir si eval迆a a verdadero o falso la proposici車n con el estado dado.
satisfen :: Estado -> Prop -> Bool
satisfen = interp

--Recibe una proposici車n y nos dice si es satisfacible.
satisf :: Prop -> Bool
satisf phi = modelos phi /= []

--Recibe un estado y una proposici車n y nos dice si es insatisfacible
--con la proposici車n dada.
insatisfen :: Estado -> Prop -> Bool
insatisfen e phi = not (interp e phi)

--Recibe una proposici車n y nos dice si era una contradicci車n.
contrad :: Prop -> Bool
contrad phi = modelos phi == []

--Recibe un conjunto de proposiciones y nos regresa una lista con todos los posibles estados
estadosConj :: [Prop] -> [Estado]
estadosConj l = estados (pega l)

--Recibe un conjunto de proposiciones y nos regresa una lista con los estados
--que hacen que el conjunto de f車rmulas eval迆e a verdadero.
modelosConj :: [Prop] -> [Estado]
modelosConj gamma = modelos (pega gamma)

--Recibe un estado y un conjunto de proposiciones y nos dice si el conjunto
--es satisfacible con el estado dado.
satisfenConj :: Estado -> [Prop] -> Bool
satisfenConj e gamma = satisfen e (pega gamma)

--Recibe un conjunto de estados y determina si es satisfacible.
satisfConj :: [Prop] -> Bool
satisfConj gamma = satisf (pega gamma)

--Recibe un estado y un conjunto de f車rmulas y determina si el conjunto
--es satisfacible con el estado dado
insatisfenConj :: Estado -> [Prop] -> Bool
insatisfenConj e gamma = insatisfen e (pega gamma)

--Recibe un conjunto de f車rmulas y nos dice si es satisfacible o no.
insatisfConj :: [Prop] -> Bool
insatisfConj gamma = contrad (pega gamma)

--Recibe dos proposiciones y determina si son equivalentes
--utilizando la funci車n tautolog赤a y enviando como parametro
--las proposiciones unidas con el operador de equivalencia.
equiv :: Prop -> Prop -> Bool
equiv p q = tautologia (Equiv p q)

--Recibe un conjunto de proposiciones y una proposici車n y determina
--si la proposici車n es consecuencia l車gica del primer conjunto recibido
--utilizando el principio de la deduci車n.
consecuencia :: [Prop] -> Prop -> Bool
consecuencia gamma phi = insatisfConj ((Neg phi):gamma)

--Recibe un conjunto de proposiciones y una proposici車n consecuencia 
--y nos dice si el argumento es correcto utilizando el principio de 
--deducci車n.
argcorrecto :: [Prop] -> Prop -> Bool
argcorrecto gamma phi = consecuencia gamma phi

--Recibe un conjunto de proposiciones y nos devuelve el conjunto de proposiciones
--unidas con el operador conjunci車n.
pega :: [Prop] -> Prop
pega [] = TTrue
pega [x] = x
pega (x:xs) = Conj x (pega xs)

--Recibe una proposici車n y nos regresa una lista con las variables at車micas 
--sin repetici車n.
vars :: Prop -> [VarP]
vars phi = case phi of
    TTrue -> []
    FFalse -> []
    V x -> [x]
    Neg p -> vars p
    Conj p q -> union (vars p) (vars q)
    Disy p q -> union (vars p) (vars q)
    Imp p q -> union (vars p) (vars q)
    Equiv p q -> union (vars p) (vars q)


--Dada una lista devuelve una lista con las sublistas de la original.
subconj :: [a] -> [[a]]
subconj [] = [[]]
subconj (x:xs) = xs' ++ map (x:) xs'
    where xs' = subconj xs
