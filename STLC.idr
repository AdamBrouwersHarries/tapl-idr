module STLC

-- Types
data Ty = TyArr (Ty, Ty) | TyBool

-- Terms

-- A Binding is either just a name, or a variable with a type
data Binding = NameBind | VarBind ty

-- A Context is just a list of strings and their bindings
Context : Type
Context = List (String, Binding)

-- Add a binding to a context
addBinding : (ctx : Context) -> (name: String) -> (bind: Binding) -> Context
addBinding ctx name bind = (name, bind) :: ctx
