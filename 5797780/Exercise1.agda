-- Ruud van Asseldonk, 5797780

module Exercise1 where

{- Instruction: Fill in all the missing definitions. In most cases,
the type signature enforces that there should be a single unique
definition that fits. 

If you have any questions, don't hesitate to email me or ask in class.
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

-- The == is already taken for use in proofs, so I'll use === for Nat equality.
_===_ : Nat -> Nat -> Bool
_===_ Zero Zero = True
_===_ (Succ n) Zero = False
_===_ Zero (Succ n) = False
_===_ (Succ n) (Succ m) = n === m

if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if_then_else_ True x _ = x
if_then_else_ False _ x = x

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

-- Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} x = Nil
pure {Succ _} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
_<*>_ Nil Nil = Nil
_<*>_ (Cons f fs) (Cons x xs) = Cons (f x) (fs <*> xs)

infixl 20 _<*>_

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap _ Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Add two vectors component-wise
vadd : {n : Nat} -> Vec Nat n -> Vec Nat n -> Vec Nat n
vadd xs ys = (pure _+_) <*> xs <*> ys

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd xxs yys = (pure vadd) <*> xxs <*> yys

-- Generate a vector from a function index -> value
generate : {n : Nat} {a : Set} -> (Nat -> a) -> Vec a n
generate {Zero} _ = Nil
generate {Succ i} f = Cons (f i) (generate f)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix = generate λ i -> generate λ j -> if i === j then 1 else 0

heads : {n m : Nat} -> {a : Set} -> Matrix a (Succ n) m -> Vec a m
heads Nil = Nil
heads (Cons (Cons h _) rows) = Cons h (heads rows)

tails : {n m : Nat} -> {a : Set} -> Matrix a (Succ n) m -> Vec (Vec a n) m
tails Nil = Nil
tails (Cons (Cons _ tail) rows) = Cons tail (tails rows)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = generate λ _ -> Nil
transpose (Cons Nil rows) = Nil
transpose (Cons (Cons h tail) rows) =
  let hs = heads rows in
  let ts = tails rows in
  Cons (Cons h hs) (transpose (Cons tail ts))
  
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} with plan {n}
plan {Succ .Zero} | Nil = Cons Fz Nil
plan {Succ k} | tail = Cons Fz (vmap Fs tail)

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs k) = Succ (forget k)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs k) = Fs (embed k)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs k) = cong Succ (correct k)

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
cmp Zero (Succ m) = LessThan m
cmp (Succ n) Zero = GreaterThan n
cmp Zero Zero = Equal
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k)) | LessThan k = LessThan k
cmp (Succ .(n + Succ k)) (Succ n) | GreaterThan k = GreaterThan k
cmp (Succ n) (Succ .n)            | Equal = Equal

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference .(n + Succ k) n | GreaterThan k = Succ k
difference n .n            | Equal = Zero

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
plusSucc (Succ n) m = let indHypot = plusSucc n m in cong Succ indHypot

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) m =
  let indHypot = plusCommutes n m
  in trans (cong Succ indHypot) (plusSucc m n)

associativity : (n m k : Nat) -> (n + (m + k)) == ((n + m) + k)
associativity Zero m k = Refl
associativity (Succ n) m k = let indHypot = associativity n m k in cong Succ indHypot

-- My distributivity proof is really ugly. I started with induction,
-- and then arrived at the claim called "associativity2" below.

associativity2 : (a b c d : Nat) -> ((a + b) + (c + d)) == ((a + c) + (b + d))
associativity2 a b c d =
  let swapBCLocal = plusCommutes b c in
  let swapBCWithA1 = cong (λ x -> a + x) swapBCLocal in
  let assoc1 = sym (associativity a b c) in
  let assoc2 = associativity a c b in
  let swapBCWithA2 = trans assoc1 (trans swapBCWithA1 assoc2) in
  let swapBCFull = cong (λ x -> x + d) swapBCWithA2 in
  let aPlusB = associativity (a + b) c d in
  let aPlusC = associativity (a + c) b d in
  trans aPlusB (trans swapBCFull (sym aPlusC))

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
   let indHypot = distributivity n m k in
   let plusMK = cong (λ x -> (m + k) + x) indHypot in
   let assoc = associativity2 m k (n * m) (n * k) in
   trans plusMK assoc

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {a} {Nil} = Base
SubListRefl {a} {Cons h t} = Keep SubListRefl

-- This one was quite tricky to solve. I followed the types, and at every step there
-- is only one thing you can do. In hindsight the solution is obvious, of course.
SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base q = q
SubListTrans (Keep p) (Keep q) = Keep (SubListTrans p q)
SubListTrans (Keep p) (Drop q) = Drop (SubListTrans (Keep p) q)
SubListTrans (Drop p) (Keep q) = Drop (SubListTrans p q)
SubListTrans (Drop p) (Drop q) = Drop (SubListTrans (Drop p) q)

UnCons : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
UnCons (Keep p) = Drop p
UnCons (Drop p) = Drop (UnCons p)

-- The last case for antisymmetry was a really tough one, but in the end
-- I managed to solve it using the Contradiction lemma below.
Contradiction : {a : Set} {x : a} {xs : List a} -> SubList (Cons x xs) xs -> Empty
Contradiction (Keep p) = Contradiction p
Contradiction (Drop p) = Contradiction (UnCons p)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base q = Refl
SubListAntiSym (Keep {x} p) (Keep q) = cong (Cons x) (SubListAntiSym p q)
SubListAntiSym (Keep {x} p) (Drop q) = cong (Cons x) (SubListAntiSym p (UnCons q))
SubListAntiSym (Drop {x} p) (Keep q) = cong (Cons x) (SubListAntiSym (UnCons p) q)
SubListAntiSym (Drop {x} p) (Drop q) with Contradiction (SubListTrans q (UnCons p))
... | ()


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Minimum : forall {x} -> LEQ Zero x
  LeqSucc : forall {x y} -> LEQ x y -> LEQ (Succ x) (Succ y)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Minimum
leqRefl (Succ n) = LeqSucc (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Minimum q = Minimum
leqTrans (LeqSucc p) (LeqSucc q) = LeqSucc (leqTrans p q)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Minimum Minimum = Refl
leqAntiSym (LeqSucc p) (LeqSucc q) = cong Succ (leqAntiSym p q)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Minimum = Refl
leq<= (LeqSucc p) = leq<= p

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m p = Minimum
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) p = LeqSucc (<=leq n m p)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p notP = notP p

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

mapInl : {a b c : Set} -> (a -> c) -> Or a b -> Or c b
mapInl f (Inl x) = Inl (f x)
mapInl f (Inr x) = Inr x

-- The type desugars to ((Or P (Not P)) -> Empty) -> Empty
notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle notLem = let notP p = notLem (Inl p) in notLem (Inr notP)

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.


doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

step1 : doubleNegation -> excludedMiddle
step1 dn = dn notNotExcludedMiddle

exFalso : {P : Set} -> Empty -> P
exFalso ()

-- I thought it might be easier to prove the reverse three directions,
-- so I started proving those. I ended up proving four directions:
--   excludedMiddle <--> doubleNegation
--   excludedMiddle <--> impliesToOr
step1' : excludedMiddle -> doubleNegation
step1' em notNotP = orCase (λ p -> p) (λ notP -> exFalso (notNotP notP)) em

-- Desugared type:
-- Or P (P -> Empty) -> (P -> Q) -> Or (P -> Empty) Q
-- If it was Not P, keep it, if it was P, apply the function.
step2 : excludedMiddle -> impliesToOr
step2 pOrNot f = orCase (λ p -> Inr (f p)) Inl pOrNot

swap : {P Q : Set} -> Or P Q -> Or Q P
swap (Inl p) = Inr p
swap (Inr q) = Inl q

step2' : impliesToOr -> excludedMiddle
step2' ito = swap (ito (λ p -> p))

step3 : impliesToOr -> doubleNegation
step3 ito = step1' (step2' ito)

step3' : doubleNegation -> impliesToOr
step3' dn = step2 (step1 dn)

-- HARDER: show that these are equivalent to Peirces law:
peircesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

-- This is impliesToOr with both sides negated.
notImplies : {P Q : Set} -> Not (P -> Q) -> Not (Or (Not P) Q)
notImplies notImpl impl = notImpl (orCase (λ notP p -> exFalso (notP p)) (λ q p -> q) impl)

-- From Not (Or (Not P) Q) it follows that (Not Not P) and (Not Q),
-- but only the former is returned here.
notOr : {P Q : Set} -> Not (Or (Not P) Q) -> (Not (Not P))
notOr f notP = f (Inl notP)

-- Because impliesToOr <--> doubleNegation <--> excludedMiddle,
-- it is sufficient to prove that impliesToOr -> peircesLaw
-- and peircesLaw -> doubleNegation to prove all four equivalent.

step4 : impliesToOr -> peircesLaw
step4 ito f =
  let dn = step3 ito in
  let or = mapInl notImplies (ito f)
  in orCase (λ no -> dn (notOr no)) (λ p -> p) or

step5 : peircesLaw -> doubleNegation
step5 pl notNotP = let makeP notP = exFalso (notNotP notP) in pl makeP

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

-- We can also compile such expressions to stack machine code
data Cmd : Set where
  -- stop execution and return the current stack
  HALT : Cmd 
  -- push a new number on the stack
  PUSH : Nat -> Cmd -> Cmd 
  -- replace the top two elements of the stack with their sum
  ADD : Cmd -> Cmd

Stack : Set
Stack = List Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total -- how can you fix
-- things so that it is?
exec : Cmd -> Stack -> Stack
exec HALT st = st
exec (PUSH n cmd) st =
  let newSt = Cons n st
  in exec cmd newSt
exec (ADD cmd) (Cons x (Cons y st)) =
  let newSt = Cons (x + y) st
  in exec cmd newSt

-- The problem is this: depending on the program, not every input stack
-- might be valid. In particular, if the program starts with an add, the
-- input stack must contain at least two items. Perhaps it would be
-- possible to encode that constraint in the type system, but I will avoid
-- the issue by defining a missing argument to add to be an implicit zero.
-- This aligns with the notion of an empty sum being zero. (Other options
-- are possible, such as ignoring the instruction altogether, or
-- terminating execution and returning the current stack.)
exec (ADD cmd) (Cons x Nil) = exec cmd (Cons x Nil)
exec (ADD cmd) Nil = exec cmd (Cons 0 Nil)

compile' : Cmd -> Expr -> Cmd
compile' continuation (Add lhs rhs) =
  -- The add instruction comes *after* computing LHS and RHS:
  -- its inputs must be on the stack before the add can be
  -- evaluated. Before the add comes the code that pushes the
  -- LHS onto the stack, and before that the code that pushes
  -- the RHS onto the stack.
  let cmdAdd = ADD continuation in
  let cmdLhs = compile' cmdAdd lhs in
  compile' cmdLhs rhs
compile' continuation (Val n) = PUSH n continuation

-- Define a compiler from expresions to instructions
compile : Expr -> Cmd
compile = compile' HALT

correctness' : (cont : Cmd) (e : Expr) (s : Stack)
             -> exec cont (Cons (eval e) s) == exec (compile' cont e) s
correctness' cont (Val n) s = Refl
correctness' cont (Add lhs rhs) s =
  -- This is solved backwards, starting from the expected type,
  -- by recursively applying the correctness' lemma.
  let evalRhs = correctness' (compile' (ADD cont) lhs) rhs s in
  let evalLhs = correctness' (ADD cont) lhs (Cons (eval rhs) s)
  in trans evalLhs evalRhs

-- And prove your compiler correct
correctness : (e : Expr) (s : Stack) -> Cons (eval e) s == exec (compile e) s
correctness = correctness' HALT

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...

-- For fun, here's a compiler that can do constant folding :)
compileOptimized : Expr -> Cmd
compileOptimized expr = PUSH (eval expr) HALT
