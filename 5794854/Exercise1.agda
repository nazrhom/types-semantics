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

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> Nil = Nil
Cons f xf <*> Cons x xs = Cons (f x) (xf <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Append one element at the end of the vector
_<+_ : ∀ {n a} ->  Vec a n -> a -> Vec a (Succ n)
Nil <+ a = Cons a Nil
Cons x xs <+ a = Cons x (xs <+ a)

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m

-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil Nil = Nil
madd (Cons xs xss) (Cons ys yss) = Cons (vmap _+_ xs <*> ys) (madd xss yss)

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {Zero} = Nil
idMatrix {Succ n} = vmap (_<+ 0) idMatrix <+ (pure 0 <+ 1)

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons v vs) = vmap Cons v <*> (transpose vs)

vec1 : Vec Nat 2
vec1 = Cons 1 (Cons 2 Nil)

ex1 : Matrix Nat 2 1
ex1 = Cons vec1 Nil

ex2 : Matrix Nat 1 2
ex2 = transpose ex1

ex3 : ∀ n -> Matrix Nat n n
ex3 n = idMatrix

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero}   = Nil
plan {Succ n} = vmap Fs (plan {n}) <+ Fz

plan_ex : Vec (Fin 3) 3
plan_ex = plan

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz     = Zero
forget (Fs f) = Succ (forget f)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz     = Fz
embed (Fs f) = Fs (embed f)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = Refl
correct (Fs f) = cong Succ (correct f)

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
difference n .(n + Succ k) | LessThan k = (Succ k)
difference m .m | Equal = 0
difference .(m + Succ k) m | GreaterThan k = (Succ k)

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

_⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
x ⟨ Refl ⟩ Refl = Refl

infixr 2 _⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x == x
x ∎ = Refl

infix  3 _∎

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : ∀ m n -> (m + n) == (n + m)
plusCommutes Zero m = sym (plusZero m)
plusCommutes (Succ n) Zero = cong Succ (plusZero n)
plusCommutes (Succ n) (Succ m) with plusCommutes (Succ n) m | plusCommutes n (Succ m) | plusCommutes n m
... | pcSnm | pcnSm | pcnm = cong Succ (trans pcnSm (trans (cong Succ (sym pcnm)) pcSnm))

plusAssoc : ∀ a b c -> ((a + b) + c) == (a + (b + c))
plusAssoc Zero b c = Refl
plusAssoc (Succ a) b c = cong Succ (plusAssoc a b c)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
  let ih = distributivity n m k in
  (m + k) + (n * (m + k))
    ⟨ cong (λ x → (m + k) + x) ih ⟩
  (m + k) + ((n * m) + (n * k))
    ⟨ plusAssoc  m k (((n * m) + (n * k))) ⟩
  m + (k + ((n * m) + (n * k)))
    ⟨ cong (λ x → (m + (k + x))) (plusCommutes (n * m) (n * k)) ⟩
  m + (k + ((n * k) + (n * m)))
    ⟨ cong (λ x → (m + x)) (sym (plusAssoc k (n * k) (n * m))) ⟩
  m + ((k + (n * k)) + (n * m))
    ⟨ cong (λ x → m + x) (plusCommutes (k + (n * k)) (n * m)) ⟩
  m + ((n * m) + (k + (n * k)))
    ⟨ sym (plusAssoc m (n * m) (k + (n * k))) ⟩
  (m + (n * m)) + (k + (n * k))
  ∎

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {xs = Nil} = Base
SubListRefl {xs = Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans sxy Base = sxy
SubListTrans (Keep sxy) (Keep syz) = Keep (SubListTrans sxy syz)
SubListTrans (Drop sxy) (Keep syz) = Drop (SubListTrans sxy syz)
SubListTrans sxy (Drop syz) = Drop (SubListTrans sxy syz)

-- Drop the left element and is still a sublist
drop-SL-Left : ∀ {A : Set} {x : A}{xs ys : List A} -> SubList (Cons x xs) ys -> SubList xs ys
drop-SL-Left (Keep p) = Drop p
drop-SL-Left (Drop p) = Drop (drop-SL-Left p)

-- Drop both elements (the same) and is still a sublist
drop-SL-Both : ∀ {A : Set} {x : A}{xs ys : List A} -> SubList (Cons x xs) (Cons x ys) -> SubList xs ys
drop-SL-Both (Keep sl) = sl
drop-SL-Both (Drop sl) = drop-SL-Left sl

-- A list plus an element is not a sublist of itself
not_SL : {A : Set} {x : A} {xs : List A} -> (SubList (Cons x xs) xs) -> Empty
not_SL (Keep s) = not_SL s
not_SL (Drop s) with (not_SL (drop-SL-Left s))
not_SL (Drop s) | ()

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base syz = Refl
SubListAntiSym (Keep sxy) syz = cong (Cons _) (SubListAntiSym sxy (drop-SL-Both syz))
SubListAntiSym (Drop sxy) (Keep syz) = cong (Cons _) (SubListAntiSym (drop-SL-Left sxy) syz)
SubListAntiSym (Drop sxy) (Drop syz) with SubListAntiSym (drop-SL-Left syz) (drop-SL-Left sxy)
SubListAntiSym (Drop sxy) (Drop syz) | Refl = magic (not_SL syz)


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  LEQZero : ∀ {n}   -> LEQ Zero n
  LEQSucc : ∀ {n m} -> LEQ n m -> LEQ (Succ n) (Succ m)

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = LEQZero
leqRefl (Succ n) = LEQSucc (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQZero l2 = LEQZero
leqTrans (LEQSucc l1) (LEQSucc l2) = LEQSucc (leqTrans l1 l2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQZero LEQZero = Refl
leqAntiSym (LEQSucc l1) (LEQSucc l2) = cong Succ (leqAntiSym l1 l2)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQZero = Refl
leq<= (LEQSucc leq) = leq<= leq

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m p = LEQZero
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) p = LEQSucc (<=leq n m p)

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP p = λ not → not p

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
notNotExcludedMiddle {P} not = not (Inr (λ p → not (Inl p))) 

-- There are various different axioms that can be added to a
-- constructive logic to get the more familiar classical logic.

doubleNegation = {P : Set} -> Not (Not P) -> P
excludedMiddle = {P : Set} -> Or P (Not P)
impliesToOr = {P Q : Set} -> (P -> Q) -> Or (Not P) Q
-- Let's try to prove these three statements are equivalent...  you
--  may find it helpful to replace the 'doubleNegation' and others
--  with their definition in the type signatures below.
--  This is not always easy...

id : {A : Set} -> A -> A
id x = x

step1 : doubleNegation -> excludedMiddle
step1 dn {P} = dn (λ not → not (Inr (λ p → not (Inl p))))

step2 : excludedMiddle -> impliesToOr
step2 em {P} {Q} f = orCase (λ p → (Inr (f p))) Inl em

step3 : impliesToOr -> doubleNegation
step3  ito {P} h = orCase (λ np → magic (h np)) id (ito id)

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

eq1 : excludedMiddle -> piercesLaw
eq1 em {P} {Q} imp = orCase id (λ np → imp (λ p → magic (np p))) em

eq1' : piercesLaw -> excludedMiddle
eq1' pl {P} = pl (λ orpimp → Inr (λ np → orpimp (Inl np)))

eq2 : doubleNegation -> piercesLaw
eq2 dn {P} {Q} imp = dn (λ np → np (imp (λ p → magic (np p))))

eq2' : piercesLaw -> doubleNegation
eq2' pl {P} nnp = pl (λ piq → magic (nnp piq))

eq3 : impliesToOr -> piercesLaw
eq3 ito {P} {Q} imp = orCase (λ np → imp (λ p → magic (np p))) id (ito id)

eq3'' : piercesLaw -> impliesToOr
eq3'' pl {P} {Q} imp = orCase Inl (λ p → Inr (imp p)) (pl (λ z → Inl (λ x → z (Inr x))))

-- Of course we can have used step1, step2 and step3.

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
exec HALT stack = stack
exec (PUSH x c) stack = exec c (Cons x stack)
exec (ADD c) (Cons y (Cons x stack)) = exec c (Cons (x + y) stack)
-- In this cases ADD does not make much sense
exec (ADD c) Nil          = exec c Nil
exec (ADD c) (Cons x Nil) = exec c (Cons x Nil)

compileCont : Expr -> (Cmd -> Cmd)
compileCont (Add e1 e2) = let i1 = compileCont e1
                              i2 = compileCont e2
                          in λ c → i1 (i2 (ADD c))
compileCont (Val x)     = PUSH x

-- Define a compiler from expresions to instructions
compile : Expr -> Cmd
compile e = compileCont e HALT

lemma : ∀ (c : Cmd) (e : Expr) (s : Stack)
      -> (exec c (Cons (eval e) s)) == (exec (compileCont e c) s)
lemma c (Add x y) s with lemma (compileCont y (ADD c)) x s | lemma (ADD c) y (Cons (eval x) s)
... | p | r = trans r p
lemma c (Val x) s = Refl

-- And prove your compiler correct
correctness : (e : Expr) (s : Stack) -> Cons (eval e) s == exec (compile e) s
correctness e s = lemma HALT e s

-- Custom definition of commands, indexed by the size of the stack they
-- take as input and spit as output.

MyStack : Nat -> Set
MyStack n = Vec Nat n

data MyCmd : Nat -> Nat -> Set where
  -- stop execution and return the current stack
  HALT : ∀ {n}   -> MyCmd n n
  -- push a new number on the stack
  PUSH : ∀ {n k} -> Nat -> MyCmd (1 + n) k -> MyCmd n k
  -- replace the top two elements of the stack with their sum
  ADD  : ∀ {n k}        -> MyCmd (1 + n) k -> MyCmd (2 + n) k

cmd1 : ∀ {n} -> MyCmd n (1 + n)
cmd1 = PUSH 0 HALT

_++_ : ∀ {n m k} -> MyCmd n m -> MyCmd m k -> MyCmd n k
_++_ HALT c2        = c2
_++_ (PUSH x c1) c2 = PUSH x (c1 ++ c2)
_++_ (ADD c1) c2    = ADD (c1 ++ c2)

-- Exec version of MyCmd
exec' : ∀ {n m} -> MyCmd n m -> MyStack n -> MyStack m
exec' HALT s = s
exec' (PUSH x c) s  = exec' c (Cons x s)
exec' (ADD c) (Cons y (Cons x s)) = exec' c (Cons ((x + y)) s)


compileCont' : ∀ {n m} -> Expr -> (MyCmd (1 + n) m -> MyCmd n m)
compileCont' (Add x y) = let c1 = compileCont' x
                             c2 = compileCont' y
                         in λ c -> c1 (c2 (ADD c))
compileCont' (Val x)    = PUSH x

compile' : ∀ {n} -> Expr -> MyCmd n (1 + n)
compile' e = compileCont' e HALT

lemma' : ∀ {n m : Nat} (c : MyCmd (1 + n) m)  (e : Expr) (s : MyStack n)
      -> (exec' c (Cons (eval e) s)) == (exec' (compileCont' e c) s)
lemma' c (Add x y) s with lemma' (compileCont' y (ADD c)) x s | lemma' (ADD c) y (Cons (eval x) s)
... | cx | cxy = trans cxy cx
lemma' c (Val x) s   = Refl

correctness' : ∀ {n} (e : Expr) (s : MyStack n) -> Cons (eval e) s == exec' (compile' e) s
correctness' e s = lemma' HALT e s

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...

-- Now expressions support variables indexed by Fin n
data MyExpr : Nat -> Set where
  Add : ∀ {n} -> MyExpr n -> MyExpr n -> MyExpr n
  Val : ∀ {n} -> Nat    -> MyExpr n
  Var : ∀ {n} -> Fin n  -> MyExpr n

ClosedExpr = MyExpr Zero

Ctx : Nat -> Set
Ctx n = Vec Nat n

_!!_ : ∀ {n a} -> Vec a n -> Fin n -> a
Cons x xs !! Fz = x
Cons x xs !! Fs n = xs !! n

eval' : ∀ {n} -> Ctx n -> MyExpr n -> Nat
eval' ctx (Add x y)  = eval' ctx x + eval' ctx y
eval' ctx (Val x)    = x
eval' ctx (Var x)    = ctx !! x

compileCont'' : ∀ {n m l} -> Ctx l -> MyExpr l -> (MyCmd (1 + n) m -> MyCmd n m)
compileCont'' ctx (Add x y) c = compileCont'' ctx x (compileCont'' ctx y (ADD c))
compileCont'' ctx (Val x) c   = PUSH x c
compileCont'' ctx (Var ix) c  = PUSH (ctx !! ix) c

compile'' : ∀ {n m} -> Ctx m -> MyExpr m -> MyCmd n (1 + n)
compile'' ctx e = compileCont'' ctx e HALT

lemma'' : ∀ {n m s : Nat} (c : MyCmd (1 + n) m) (ctx : Ctx s) (e : MyExpr s) (s : MyStack n)
       -> (exec' c (Cons (eval' ctx e) s)) == (exec' (compileCont'' ctx e c) s)
lemma''  c ctx (Add x y) s with lemma'' (compileCont'' ctx y (ADD c)) ctx x s | lemma'' (ADD c) ctx y (Cons (eval' ctx x) s)
... | p | r = trans r p
lemma'' c ctx (Val x) s = Refl
lemma'' c ctx (Var x) s = Refl

correctness'' : ∀ {n m} (c : Ctx m) (e : MyExpr m) (s : MyStack n) -> Cons (eval' c e) s == exec' (compile'' c e) s
correctness'' e s = lemma'' HALT e s
