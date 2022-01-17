
and :: Bool -> Bool -> Bool
and True True = True
and _    _    = False

andM :: Monad m => m (Bool m ->m Bool m ->m Bool m)
andM

{-# ANN and2 Fail #-}
and2 :: Bool -> Bool -> Bool
and2 True True = True
and2 _    _    = fail


-- Tag Fail (Bool -> Bool -> Bool) ~ Bool -> k
--

applied :: Bool -> Bool
applied = and2 True

data List m a = Nil | Cons (m a) (m (List m a))

and2M :: Eff Fail (Bool (Eff Fail) ->(Eff Fail) Bool (Eff Fail) -> (Eff Fail) Bool (Eff Fail))
and2M

class Eq a where
  (==) :: a -> a -> Bool

data EqDict a = Dict (a -> a -> Bool)

class Eq a where
  (==) :: a -> a -> Tag ND Bool


class EqM a where
  (==#) :: Monad m => m ((->) m a ((->) m a (BoolM m)))

data EqMDict a = DictM (forall m. Monad m => (a -> a -> Bool))



extern:
not :: m ((-->) m (BoolM m) (BoolM m))

lokal:
true :: Bool -- m (BoolM m)

test = not true
m ((-->) m (BoolM m) (BoolM m)) ~ Bool -> a
=>
Bool -> Bool ~ Bool -> a

Idee: Sigaturen von gelifteten Funktionen sind nicht polymorph in der Monade, sondern sind konkret für die Effektmonade instanziiert, wobei z.B. die Effektsignatur polymorph bleiben darf.

extern:
not :: (Eff sig) ((-->) (Eff sig) (BoolM (Eff sig)) (BoolM (Eff sig)))

lokal:
true :: Bool -- m (BoolM m)

test = not true
(Eff sig) ((-->) (Eff sig) (BoolM (Eff sig)) (BoolM (Eff sig))) ~ Bool -> a
=>
Bool -> Bool ~ Bool -> a

Dadurch lässt sich dann die Monade abschälen, weil sie eindeutig unterscheidbar ist.

data Bool  --> data Bool$
data BoolM --> data BoolM$

extern:
negate :: (Num n, ND :< sig) => (Eff sig) ((-->) (Eff sig) n n)

lokal:
true :: Bool -- m (BoolM m)

instance (TypeError "Fehler") => (a :< sig)

{-# ANN test (Open ND) #-}
test :: (ND :< sig)
test = negate 1

-- List a
-- m (List (m a)) -- data List = Nil | Cons a
-- m (List a)-- data List = Nil | Cons (m a)
-- f @(Int)

extern:
id :: (Eff sig) ((-->) (Eff sig) a a)


use :: Eff sig (BoolM (Eff ND))
use = id (_ :: Eff ND (BoolM (Eff ND))

Frage: Will man sowohl offene als auch geschlossene Effektsignaturen angeben können?