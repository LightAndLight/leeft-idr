module Lift

import Data.Vect

%default total

data Ty
  = TArr Ty Ty
  | TUnit

data Tele : {n : Nat} -> Vect n Ty -> Ty -> Ty -> Type where
  TeleDone : Tele [] out out
  TeleMore : Tele xs y out -> Tele (x :: xs) y (TArr x out)

teleToNat : Tele a b c -> Nat
teleToNat TeleDone = Z
teleToNat (TeleMore a) = S (teleToNat a)

data Tm : {n : Nat} -> Vect n Ty -> Ty -> Type where
  Var : Elem ty vs -> Tm vs ty
  Name : String -> Tm vs a
  Lam
     : {n : Nat}
    -> {vs : Vect n Ty}
    -> (tele : Tele vs ty res)
    -> Tm (vs ++ vs') ty
    -> Tm vs' res
  App : {a, b : Ty} -> Tm vs (TArr a b) -> Tm vs a -> Tm vs b

ClosedTm : Ty -> Type
ClosedTm = Tm []

data Def : Type where
  MkDef : String -> (ty : Ty) -> ClosedTm ty -> Def

supply : Stream String
supply = ("t"++) . show <$> iterate S Z

insertElem
   : {n : Nat}
  -> {vs : Vect n Ty}
  -> Elem ty (vs ++ vs')
  -> Elem ty (vs ++ v :: vs')
insertElem {n=Z} {vs = []} prf = There prf
insertElem {n=(S k)} {vs = (x :: xs)} Here = Here
insertElem {n=(S k)} {vs = (x :: xs)} (There later) = There (insertElem {n=k} later)

deassocBinders : Tm (a ++ b ++ c) ty -> Tm ((a ++ b) ++ c) ty
deassocBinders {a} {b} {c} tm = rewrite sym (vectAppendAssociative a b c) in tm

assocBinders : Tm ((a ++ b) ++ c) ty -> Tm (a ++ b ++ c) ty
assocBinders {a} {b} {c} tm = rewrite vectAppendAssociative a b c in tm

mutual
  expandScopeLam
     : (tele : Tele vs ret ty)
    -> (tm : Tm (vs ++ vs') ret)
    -> Tm (vs ++ (v :: vs')) ret
  expandScopeLam tele (Var ix) = Var (insertElem ix)
  expandScopeLam tele (Name s) = Name s
  expandScopeLam tele (Lam tele' tm) = ?h1_3
  expandScopeLam tele (App f x) = App ?h11 ?h22

  expandScope : Tm vs ty -> Tm (v :: vs) ty
  expandScope (Var x) = Var (There x)
  expandScope (Name x) = Name x
  expandScope (Lam tele x) = Lam tele (expandScopeLam tele x)
  expandScope (App x y) = App (expandScope x) (expandScope y)

             {-
expandScopeLam
   : (tele : Tele vs r ty)
  -> Tm (vs ++ vs') r
  -> Tm (vs ++ v :: vs') r
expandScopeLam {v} {vs} {vs'} tele (Var x) =
  Var (insertElem {v} {vs} {vs'} x)
expandScopeLam tele (Name x) = Name x
expandScopeLam tele (Lam k x) =
  Lam k {vs=vs1} {tele=?hhh} $
  assocBinders $
  expandScopeLam {v} {vs'} (k + n) {vs=(vs1 ++ vs)} $
  assert_smaller (Lam k x) (deassocBinders x)
expandScopeLam tele (App x y) = App (?h1 x) (expandScopeLam ?hhh y)


-- ripAndTearLam : Tm (vs ++ v :: vs') ty -> 

ripAndTear : Tm (v :: vs) ty -> Tm vs (TArr v ty)
ripAndTear {v} (Var Here) =
  Lam {vs=[v]} 1 $ Var Here
ripAndTear {v} (Var (There later)) =
  Lam {vs=[v]} 1 $ Var (There later)
ripAndTear {v} (Name x) = Lam {vs=[v]} 1 (Name x)
ripAndTear {v} {vs} (Lam n x) = ?hh
ripAndTear {v} {vs} {ty} (App {a} x y) =
  Lam {vs=[v]} 1 $
  App (App (expandScope x') (Var Here)) (App (expandScope y') (Var Here))
  where
    x' : Tm vs (TArr v (TArr a ty))
    x' = ripAndTear x

    y' : Tm vs (TArr v a)
    y' = ripAndTear y

liftLambdas : Stream String -> Tm vs ty -> (Stream String, Tm vs ty, List Def)
liftLambdas supply (Var ix) = (supply, Var ix, [])
liftLambdas supply (Name x) = (supply, Name x, [])
liftLambdas supply (Lam n x) =
  case liftLambdas supply x of
    (supply', x', defs) =>
      case supply' of
        s :: supply'' => (supply'', Name s, ?h :: defs)
liftLambdas supply (App x y) =
  case liftLambdas supply x of
    (supply', x', defs1) =>
      case liftLambdas supply' y of
        (supply'', y', defs2) => (supply'', App x' y', defs1 ++ defs2)
-}
