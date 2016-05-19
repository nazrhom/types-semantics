module Exercise1 where

{- Rogier Wuijts 4001184
-}


---------------------
------ Prelude ------
---------------------

data Bool : Set where
  True : Bool
  False : Bool

data Nat : Set where
  Zero : Nat 
  Succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ k + m = Succ (k + m)

_*_ : Nat -> Nat -> Nat
Zero * n = Zero
(Succ k) * n = n + (k * n)

data List (a : Set) : Set where
  Nil : List a
  Cons : a -> List a -> List a

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a 0
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (Succ n)

head : {a : Set} {n : Nat}-> Vec a (Succ n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : Nat} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x

cong : {a b : Set} {x y : a} -> (f : a -> b) -> x == y -> f x == f y
cong f Refl = Refl

data Unit : Set where
  unit : Unit

data Empty : Set where

magic : {a : Set} -> Empty -> a
magic ()

data Pair (a b : Set) : Set where
  _,_ : a -> b -> Pair a b

data Fin : Nat -> Set where
  Fz : forall {n} -> Fin (Succ n)
  Fs : forall {n} -> Fin n -> Fin (Succ n)

data Maybe (a : Set) : Set where
  Just : a -> Maybe a
  Nothing : Maybe a

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} x = Nil
pure {Succ n} x = Cons x (pure x)

infixl 5 _<*>_
_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons x x₁ <*> Cons x₂ x₃ = Cons (x x₂) (x₁ <*> x₃)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap x Nil = Nil
vmap x (Cons x₁ x₂) = Cons (x x₁) (vmap x x₂)


----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil yss = Nil
madd (Cons xss xss₁) (Cons yss yss₁) = Cons (pure (λ x y → x + y) <*> xss <*> yss) (madd xss₁ yss₁)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = Cons (Cons 1 (pure 0)) (vmap (Cons 0) idMatrix)

tail : {n : Nat} {a : Set} -> Vec a (Succ n) -> Vec a n
tail (Cons x xs) = xs

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {_} {Zero} xs = Nil
transpose {Zero} {Succ m} Nil = Cons Nil (transpose Nil)
transpose {Succ n} {Succ m} xs = Cons (vmap head xs) (transpose (vmap tail xs))
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.
--plan is defined below in order to use embed

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget {Zero} ()
forget {Succ n} Fz = Zero
forget {Succ n} (Fs x) = Succ (forget x)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed {Zero} ()
embed {Succ n} Fz = Fz
embed {Succ n} (Fs f) = Fs (embed f)

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.

f2n : (n : Nat) -> Fin (Succ n)
f2n Zero = Fz
f2n (Succ n) = Fs (f2n n)

plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} =  Cons (f2n n) (vmap embed plan )

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct {Zero} ()
correct {Succ n} Fz = Refl
correct {Succ n} (Fs i) = cong Succ (correct i)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero = Equal
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ m) (Succ .m) | Equal = Equal
cmp (Succ .(m + Succ k)) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = k
difference m .m | Equal = 0
difference .(m + Succ k) m | GreaterThan k = k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero = Refl
plusCommutes Zero (Succ m) = cong Succ (plusCommutes Zero m)
plusCommutes (Succ n) m = trans (cong Succ (plusCommutes n m)) (plusSucc m n) 


timesZero : (n : Nat) -> (n * 0) == 0
timesZero Zero = Refl
timesZero (Succ n) = timesZero n

lemmaPlus : {n1 n2 m1 m2 : Nat} -> n1 == n2 -> m1 == m2 -> (n1 + m1) == (n2 + m2)
lemmaPlus Refl Refl = Refl

plusAssociative  : (n m k : Nat) -> (n + (m + k)) == ((n + m) + k)
plusAssociative Zero m k = Refl
plusAssociative (Succ n) m k = cong Succ (plusAssociative n m k)

extraLemma : (x1 x2 x3 m k : Nat) -> x1 == (x2 + x3) -> ((m + k) + x1) ==  ((m + x2) + (k + x3))
extraLemma _ m k Zero n Refl = trans (plusCommutes n (m + k))
                             ( trans (sym (plusAssociative m k n))
                                     (lemmaPlus {m} Refl (plusCommutes k n)))
extraLemma .(x2 + x3) x2 x3 (Succ m) k Refl = cong Succ (extraLemma (x2 + x3) x2 x3 m k Refl)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k = extraLemma (n * (m + k)) (n * m) (n * k) m k (distributivity n m k)

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

-- reductio ad absurdum
raa : {a : Set } -> Empty -> a
raa ()

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil} = Base
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListEmpty : {a : Set} {xs : List a} -> SubList Nil xs
SubListEmpty {xs = Nil} = Base
SubListEmpty {xs = Cons x xs} = Drop SubListEmpty

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base sub2 = sub2
SubListTrans (Keep sub1) (Keep sub2) = Keep (SubListTrans sub1 sub2) 
SubListTrans (Keep sub1) (Drop sub2) = Drop (SubListTrans (Keep sub1) sub2)
SubListTrans (Drop sub1) (Keep sub2) = Drop (SubListTrans sub1 sub2)
SubListTrans (Drop sub1) (Drop sub2) = SubListTrans sub1 (Drop (SubListTrans (Drop SubListRefl) sub2))

-- Sublist property still hold when removing elements from the fisrt list
dropSub : {a : Set} {xs ys : List a} {x : a} -> SubList (Cons x xs) (ys) ->  SubList xs ys
dropSub {ys = Nil}()
dropSub (Keep sub) = Drop sub
dropSub (Drop sub) = Drop (dropSub sub)

-- Sublist property still holds when  removing the head of both lists
reverseDrop  : {a : Set} {xs ys : List a} {x : a} -> SubList (Cons x xs) (Cons x ys) ->  SubList xs ys
reverseDrop (Keep sub) = sub
reverseDrop (Drop sub) = dropSub sub 

-- Cons x xs can never be a sublist of xs.
impossible : {a : Set} {xs : List a} {x : a} -> SubList (Cons x xs) xs -> Empty
impossible {xs = Nil} ()
impossible {xs = Cons x xs} (Keep sub) = impossible sub
impossible {xs = Cons x xs} (Drop sub) = impossible (dropSub sub)

SubListAntiSym  : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base sub2 = Refl
SubListAntiSym {xs = Cons x xs} {ys = Cons .x ys} (Keep sub1) sub2 = cong (Cons x) (SubListAntiSym sub1 (reverseDrop sub2))
SubListAntiSym (Drop sub1) sub2 with (SubListAntiSym  sub1 (dropSub sub2) )
SubListAntiSym (Drop sub1) sub2 | Refl = (raa (impossible sub2))


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Base : forall {n} -> LEQ Zero n
  Rec  : forall {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Base
leqRefl (Succ n) = Rec (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Base leq2 = Base
leqTrans (Rec leq1) (Rec leq2) = Rec (leqTrans leq1 leq2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Base Base = Refl
leqAntiSym (Rec leq1) (Rec leq2) = cong Succ (leqAntiSym leq1 leq2)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= {Zero} {Zero} leq1 = Refl
leq<= {Zero} {Succ m} leq1 = Refl
leq<= {Succ n} {Zero} ()
leq<= {Succ n} {Succ m} (Rec leq1) = leq<= leq1

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m eq1 = Base
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) eq1 = Rec (<=leq n m eq1) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p l = l p

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle p = p (Inr (\q -> p (Inl q )))

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

id : {a : Set} -> a -> a
id a = a

step1 : doubleNegation -> excludedMiddle
step1 dn  = dn (\p -> p (Inr (\q -> p (Inl q)))) 

step2 : excludedMiddle -> impliesToOr
step2 em pq = orCase (\p -> Inr (pq p)) (\np -> Inl np) em

step3 : impliesToOr -> doubleNegation
step3  ito {P} dn = orCase (\np -> raa (dn np) ) id (ito id)

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

--magic
step4 : impliesToOr -> piercesLaw
step4 ito pqp =  orCase
                 (\npq -> orCase
                          (λ l -> (raa (npq (λ p -> raa (l p)))))
                          id (ito id))
                 id (ito pqp)


----------------------
----- Exercise 9 -----
----------------------

-- Given the following data type for expressions

data Expr : Set where
  Add : Expr -> Expr -> Expr
  Val : Nat -> Expr

-- We can write a simple evaluator as follows
eval : Expr -> Nat
eval (Add l r) = eval l + eval r
eval (Val x) = x

-- The first added Nat is how larger this stack must be before the Cmds
-- The second added Nat is how larger the stack is after the Cmds

data Cmd : Nat -> Nat  -> Set where
  -- stop execution and return the current stack
  HALT : forall {n} -> Cmd n n
  -- push a new number on the stack
  PUSH : forall { n m } -> Nat -> Cmd (Succ  n) m -> Cmd n m
  -- replace the top two elements of the stack with their sum
  ADD :  forall { n m } -> Cmd (Succ n ) m  -> Cmd (Succ(Succ n)) m

Stack : (n : Nat) -> Set
Stack n = Vec Nat n

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total -- how can you fix
-- things so that it is?
-- Added two natural numbers one for the stack input and output
exec : {n m : Nat} ->  Cmd n m -> Stack n -> Stack m
exec HALT s = s
exec (PUSH x c) s = exec c (Cons x s)
exec (ADD c) (Cons x (Cons x1 s)) = exec c (Cons (x + x1) s)
-- Define a compiler from expresions to instructions

--The stack cardinality before and after both be increased
plus1 : {n m : Nat} -> Cmd n m -> Cmd (1 + n) (1 + m)
plus1 HALT = HALT
plus1 (PUSH x c) = PUSH x (plus1 c)
plus1 (ADD c) = ADD (plus1 c)

--The cardinality of the in and output can be increased arbitrary times
plusK : {n m : Nat} (k : Nat) -> Cmd n m -> Cmd (k + n) (k + m)
plusK Zero c = c
plusK (Succ k) c = plus1 (plusK k c )

-- Append the comands
cmdAppend : {n1 m1 n2 m2 : Nat} -> Cmd n1 m1 -> Cmd n2 m2 -> Cmd (n1 + n2) (m1 +  m2)
cmdAppend {m1 = m} HALT c2 = plusK m c2
cmdAppend {n1 = n1} (PUSH x c1) c2 = PUSH x (cmdAppend {n1 = Succ n1} c1 c2)
cmdAppend (ADD c1) c2 = ADD (cmdAppend c1 c2)

--Add an ADD at the end
addADD : {n m : Nat} -> Cmd n (Succ (Succ m)) -> Cmd n ( Succ m)
addADD HALT = ADD HALT
addADD (PUSH x c1) = PUSH x (addADD c1)
addADD (ADD c1) = ADD (addADD c1)

compile : Expr -> Cmd Zero (Succ Zero)
compile (Add e e1) = (addADD (cmdAppend (compile e) (compile e1)))
compile (Val x) = PUSH x HALT
-- And prove your compiler correct

-- I could not finish the last exercise.
correctness : (e : Expr) -> Cons (eval e) Nil == (exec (compile e) Nil)
correctness e = {!!}
--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
