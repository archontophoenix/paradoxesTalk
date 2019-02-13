-- See https://github.com/idris-lang/Idris-dev/issues/3194

module TypeInType

%default total

data Tree: Type where
  Sup: (a: Type) -> (f: a -> Tree) -> Tree
  
A: Tree -> Type
A (Sup a _) = a

F: (t: Tree) -> A t -> Tree
F (Sup _ f) = f

Normal: Tree -> Type
Normal t = (y: A t ** (F t y = Sup (A t) (F t))) -> Void

NT: Type
NT = (t: Tree ** Normal t)

P: NT -> Tree
P (x ** _) = x

R: Tree
R = Sup NT P

Lemma: Normal R
Lemma ((y1 ** y2) ** z) =
  y2 (
    replace
      {P = (\y3 => (y: A y3 ** F y3 y = Sup (A y3) (F y3)))}
      (sym z) ((y1 ** y2) ** z))

Russel: Void
Russel = Lemma ((R ** Lemma) ** Refl)
