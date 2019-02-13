-- See https://github.com/idris-lang/Idris-dev/issues/3194

module TypeNotInType

%default total

-- define dependent pair type locally to avoid Idris bug that fails to check
-- type level constraints across module boundaries:
data MPair : (a : Type) -> (P : a -> Type) -> Type where
  MkMPair : .{P : a -> Type} -> (x : a) -> (pf : P x) -> MPair a P

data Tree: Type where
  Sup: (a: Type) -> (f: a -> Tree) -> Tree
  
A: Tree -> Type
A (Sup a _) = a

F: (t: Tree) -> A t -> Tree
F (Sup _ f) = f

Normal: Tree -> Type
Normal t = (MPair (A t) (\y => F t y = Sup (A t) (F t))) -> Void

NT: Type
NT = MPair Tree (\t => Normal t)

P: NT -> Tree
P (MkMPair x _) = x

R: Tree
R = Sup NT P

Lemma: Normal R
Lemma (MkMPair (MkMPair y1 y2) z) =
  y2 (
    replace
      {P = (\y3 => (MPair (A y3) (\y => (F y3 y = Sup (A y3) (F y3)))))}
      (sym z) (MkMPair (MkMPair y1 y2) z))

Russel: Void
Russel = Lemma (MkMPair (MkMPair R Lemma) Refl)

{-
The last line above gives the error message:

Working on: .\TypeNotInType.idr.b1
Old domain: (5,5)
New domain: (5,4)
Involved constraints: 
  ConstraintFC {uconstraint =
     .\TypeNotInType.idr.b1 <= .\TypeNotInType.idr.o1,
     ufc = TypeNotInType.idr:41:10-47}
  ConstraintFC {uconstraint =
    .\TypeNotInType.idr.b1 < .\TypeNotInType.idr.c1,
    ufc = TypeNotInType.idr:9:6-10}
  ConstraintFC {uconstraint =
    .\TypeNotInType.idr.b1 <= .\TypeNotInType.idr.o1,
    ufc = TypeNotInType.idr:41:10-47}
  ConstraintFC {uconstraint =
    .\TypeNotInType.idr.d1 <= .\TypeNotInType.idr.b1,
    ufc = TypeNotInType.idr:9:6-10}
-}
