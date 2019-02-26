module Tableux where

import Syntax

data Tableux = Empty
             | Uno Prop Tableux
             | Dos Tableux Tableux

--Recibe un Tableux y desarrolla las ramas según estaba construído.
--(expande verticalmente el arbol con la conjunción o añade dos ramas
--cuando aparece el operador conjunción).
expand :: Tableux -> Tableux
expand tab = case tab of
    Empty -> Empty
    Uno phi t -> case phi of
        Conj p q -> expand (Uno p (Uno q t))
        Disy p q -> expand (Dos (Uno p t) (Uno q t))
        _ -> Uno phi (expand t)
    Dos t1 t2 -> Dos (expand t1) (expand t2)

--Recibe una proposición y la desarrolla como Tableaux.
trans :: Prop -> Tableux
trans phi = expand (Uno phi Empty)


--Recibe un Tableaux  y un conjunto de variables proposicionales
--nos dice si el tableaux tiene un camino que no contenga a ninguna
-- de las negaciones las variables en la lista dada, realiza un recorrido
--DFS.
satisf_aux :: Tableux -> [VarP] -> Bool
satisf_aux tab l = case tab of
    Empty -> True
    Uno phi t -> case phi of
        TTrue -> satisf_aux t l
        FFalse -> False
        V x -> if elem (-x) l
            then False
            else satisf_aux t (x:l)
        Neg (V x) -> if elem x l
            then False
            else satisf_aux t ((-x):l)
    Dos t1 t2 -> (satisf_aux t1 l) || (satisf_aux t2 l)

--Recibe una proposición y determina si es satisfacible o no utilizando
--el método de Tableux.
satisf_tab :: Prop -> Bool
satisf_tab phi = satisf_aux (trans (fnn phi)) []
