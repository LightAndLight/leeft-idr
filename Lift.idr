module Lift

import Data.HVect
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

deleteElem
  : (n : Nat)
  -> {vs : Vect n Ty}
  -> Elem ty (vs ++ v :: vs')
  -> Maybe (Elem ty (vs ++ vs'))
deleteElem Z {vs = []} Here = Nothing
deleteElem Z {vs = []} (There later) = Just later
deleteElem (S k) {vs = (x :: xs)} Here = Just Here
deleteElem (S k) {vs = (x :: xs)} (There later) = There <$> deleteElem k later

deassocBinders : Tm (a ++ b ++ c) ty -> Tm ((a ++ b) ++ c) ty
deassocBinders {a} {b} {c} tm = rewrite sym (vectAppendAssociative a b c) in tm

assocBinders : Tm ((a ++ b) ++ c) ty -> Tm (a ++ b ++ c) ty
assocBinders {a} {b} {c} tm = rewrite vectAppendAssociative a b c in tm

expandScope : Tm (vs ++ vs') ty -> Tm (vs ++ v :: vs') ty
expandScope (Var x) = Var (insertElem x)
expandScope (Name x) = Name x
expandScope (Lam tele x) =
  Lam tele $
  assocBinders $
  expandScope $
  assert_smaller (Lam tele x) (deassocBinders x)
expandScope (App x y) = App (expandScope x) (expandScope y)

chooseElem : Elem x (xs ++ ys) -> Either (Elem x xs) (Elem x ys)
chooseElem {xs = []} {ys = (x :: xs)} prf = Right prf
chooseElem {xs = (x :: xs)} {ys = ys} Here = Left Here
chooseElem {xs = (x :: xs)} {ys = ys} (There later) =
  case chooseElem later of
    Left prf => Left (There prf)
    Right prf => Right prf

freeVars
   : Tm (vs ++ vs') ty
  -> List (DPair Ty (Tm vs'))
freeVars (Var x) =
  case chooseElem x of
    Left prf => []
    Right prf => [(_ ** Var prf)]
freeVars (Name x) = []
freeVars (Lam tele y) =
  freeVars $
  assert_smaller (Lam tele y) (deassocBinders y)
freeVars (App x y) = freeVars x ++ freeVars y

testTm : Tm [TUnit] (TArr TUnit TUnit)
testTm =
  Lam (TeleMore TeleDone) $
  Var (There Here)

widenElemR : Elem x xs -> Elem x (xs ++ ys)
widenElemR Here = Here
widenElemR (There prf) = There (widenElemR prf)

widenElemL : Elem y ys -> Elem y (xs ++ ys)
widenElemL {xs = []} prf = prf
widenElemL {xs = (x :: xs)} prf = There (widenElemL {xs} prf)

assocElem : Elem x ((a ++ b) ++ c) -> Elem x (a ++ b ++ c)
assocElem {a} {b} {c} prf = rewrite vectAppendAssociative a b c in prf

shift : Tm (a ++ c) ty -> Tm (a ++ b ++ c) ty
shift (Var x) =
  case chooseElem x of
    Left prf => Var (widenElemR prf)
    Right prf => Var (assocElem (widenElemL prf))
shift (Name x) = Name x
shift (Lam tele x) =
  Lam tele $
  assocBinders $
  shift $
  assert_smaller (Lam tele x) (deassocBinders x)
shift (App x y) = App (shift x) (shift y)

shift_ : Tm b ty -> Tm (a ++ b) ty
shift_ = shift {a=[]}

instantiate
   : Tm (vs ++ vs') v
  -> Tm (vs ++ v :: vs') ty
  -> Tm (vs ++ vs') ty
instantiate sub (Var x) =
  case chooseElem x of
    Left prf => Var (widenElemR prf)
    Right prf =>
      case prf of
        Here => sub
        There prf' => Var (widenElemL prf')
instantiate sub (Name x) = Name x
instantiate sub (Lam tele x) =
  Lam tele $
  assocBinders $
  instantiate (deassocBinders (shift_ sub)) $
  assert_smaller (Lam tele x) (deassocBinders x)
instantiate sub (App x y) = App (instantiate sub x) (instantiate sub y)

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
