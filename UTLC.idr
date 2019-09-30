module UTLC

import Data.Vect

-- an alias to names.
Name : Type
Name = String

-- Terms
data Term = TmVar (Nat, Nat) | TmAbs (Name, Term) | TmApp (Term, Term)

-- A Binding is just a name
data Binding = NameBind

-- A Context is just a list of Names and their bindings
Context : Nat -> Type
Context n = Vect n (Name, Binding)

-- Commands
data Command = Eval Term | Bind (Name, Binding)

--- Useful context management things ---
emptycontext : Context 0
emptycontext = Nil

ctxlength : (Context n) -> Nat
ctxlength x = Data.Vect.length x



addBinding : (ctx : Context n) -> (name: Name) -> (bind: Binding) -> Context (S n)
addBinding ctx name bind = (name, bind) :: ctx

addName : (ctx: Context n) -> (name : Name) -> Context (S n)
addName ctx name = addBinding ctx name NameBind

isNameBound : (ctx : Context n) -> (name : Name) -> Bool
isNameBound [] name = False
isNameBound ((n, bind) :: xs) name =
    if n == name then
        True
    else
        isNameBound xs name

pickFreshName : (ctx: Context n) -> (name: Name) -> (Context (S n), Name)
pickFreshName ctx name =
    if isNameBound ctx name then
        pickFreshName ctx (name ++ "'")
    else
        ((name, NameBind)::ctx, name)

total indexToName : (ix : Nat) ->  (ctx : Context n) -> {auto smaller : LTE (S ix) n} -> Name
indexToName Z ((name, _) :: xs) = name
indexToName (S k) (x :: xs) {smaller} =
    indexToName k xs {smaller=(fromLteSucc smaller)}

nameToIndex : (ctx: Context n) -> (name: Name) -> Maybe Nat
nameToIndex [] name = Nothing
nameToIndex (x :: xs) name =
    if fst x == name then
        Just (length xs)
    else
        nameToIndex xs name


--shifting
total tmap : (onvar : Nat -> Nat -> Nat -> Term) -> (c: Nat) -> (t: Term) -> Term
tmap onvar c (TmVar (x, n)) = onvar c x n
tmap onvar c (TmAbs (x, t2)) = TmAbs(x, tmap onvar (c +1) t2)
tmap onvar c (TmApp (t1, t2)) = TmApp(tmap onvar c t1, tmap onvar c t2)

total termShiftAbove : (d: Nat) -> (c: Nat) -> (t: Term) -> Term
termShiftAbove d c t = tmap (\c, x, n => if x>=c then TmVar(x+d, n+d) else TmVar(x, n+d)) c t

total termShift : (d : Nat) -> (t: Term) -> Term
termShift d t = termShiftAbove d 0 t