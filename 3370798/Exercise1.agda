module Exercise1 where

{- Marinus Oosters, 3370798. 

   It's not completely filled in, but there were things I couldn't figure out.
-}

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

{- helper: natural equality -}
_=N_ : Nat -> Nat -> Bool
Zero     =N Zero     = True
Zero     =N (Succ x) = False
(Succ x) =N Zero     = False
(Succ x) =N (Succ y) = x =N y

{- helper: if then else -}
if_then_else_ : {a : Set} -> Bool -> a -> a -> a
if True  then x else y = x
if False then x else y = y

{- helper: function composition -}
_O_ : {a b c : Set} -> (b -> c) -> (a -> b) -> a -> c
(f O g) x = f (g x) 

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
pure {Zero}   x = Nil
pure {Succ _} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil         <*> Nil         = Nil
(Cons a va) <*> (Cons b vb) = Cons (a b) (va <*> vb)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil         = Nil
vmap f (Cons a va) = Cons (f a) (vmap f va)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a n m = Vec (Vec a n) m 

-- helper: pairwise function application
zipWith : {a b c : Set} {n : Nat} -> (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
zipWith f Nil         Nil         = Nil
zipWith f (Cons a as) (Cons b bs) = Cons (f a b) (zipWith f as bs)


-- Define matrix addition
madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd ma mb = zipWith (zipWith  _+_) ma mb

-- helper: vector where each item is its index (in reverse)
idxVec : {n : Nat} -> Vec Nat n
idxVec {Zero}   = Nil
idxVec {Succ x} = Cons x idxVec

-- helper: row index matrix
rowIdxMat : {n : Nat} -> Matrix Nat n n
rowIdxMat = pure idxVec

-- helper: column index matrix
colIdxMat' : (m : Nat) -> (n : Nat) -> Matrix Nat n m
colIdxMat' Zero     n = Nil
colIdxMat' (Succ m) n = Cons (pure m) (colIdxMat' m n) 

colIdxMat : {n : Nat} -> Matrix Nat n n
colIdxMat {n} = colIdxMat' n n

-- Boolean to natural
boolToNat : Bool -> Nat
boolToNat False = Zero
boolToNat True  = Succ Zero

-- Identity matrix with true/false
idMatBool : {n : Nat} -> Matrix Bool n n
idMatBool = zipWith (zipWith  _=N_ ) rowIdxMat colIdxMat

-- Define the identity matrix
idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {n} = vmap (vmap boolToNat) idMatBool

-- Define matrix transposition
transpose : {n m : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose Nil = pure Nil
transpose (Cons r rs) = zipWith Cons r (transpose rs)
----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- helper: vector of increasing numbers
incrVec : {n : Nat} -> Vec Nat n
incrVec {Zero}   = Nil
incrVec {Succ n} = vmap Succ (Cons Zero incrVec)



-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.
plan : {n : Nat} -> Vec (Fin n) n
plan {Zero}   = Nil
plan {Succ n} = Cons Fz (vmap Fs plan) 

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz     = Zero
forget (Fs n) = Succ (forget n) 

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs n) = Fs (embed n)

correct : {n : Nat} -> (i : Fin n) -> forget i == forget (embed i)
correct Fz = (Refl)
correct (Fs i) = cong Succ (correct i)

----------------------
----- Exercise 4 -----
----------------------

-- Given the following data type definition:

data Compare : Nat -> Nat -> Set where
  LessThan : forall {n} k -> Compare n (n + Succ k)
  Equal : forall {n} -> Compare n n
  GreaterThan : forall {n} k -> Compare (n + Succ k) n

dec : Nat -> Nat
dec Zero = Zero
dec (Succ x) = x

-- Show that there is a 'covering function'
cmp : (n m : Nat) -> Compare n m 
cmp Zero Zero     = Equal {Zero}
cmp Zero (Succ m) = LessThan {Zero} m
cmp (Succ n) Zero = GreaterThan {Zero} n

-- I might have taken a look at the standard library which does something similar ...
cmp (Succ n) (Succ m)   with cmp n m
cmp (Succ .n) (Succ .(n + Succ k)) | LessThan {n} k    = LessThan {Succ n} k
cmp (Succ .n) (Succ .n)            | Equal {n}         = Equal {Succ n}
cmp (Succ .(n + Succ k)) (Succ .n) | GreaterThan {n} k = GreaterThan {Succ n} k



-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference .n .n            | Equal {n}         = Zero
difference .n .(n + Succ k) | LessThan {n} k    = Succ k
difference .(n + Succ k) .n | GreaterThan {n} k = Succ k

----------------------
----- Exercise 5 -----
----------------------

-- Prove the following equalities.  You may want to define auxiliary
-- lemmas or use the notation intoduced in the lectures.

sym : {a : Set} {x y : a} -> x == y -> y == x
sym Refl = Refl

trans : {a : Set} {x y z : a} -> x == y -> y == z -> x == z
trans Refl Refl = Refl

-- from the demo code
infixr 2 _⟨_⟩_
_⟨_⟩_ : (x : Nat) -> {y z : Nat} -> x == y -> y == z -> x == z
_⟨_⟩_ x = trans

plusZero : (n : Nat) -> (n + 0) == n
plusZero Zero = Refl
plusZero (Succ n) = cong Succ (plusZero n)

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m     = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes Zero Zero     = Refl
plusCommutes Zero (Succ m) = cong Succ (plusCommutes Zero m)
plusCommutes (Succ n) m    =
     (Succ n) + m
          ⟨ cong Succ (plusCommutes n m) ⟩
     plusSucc m n

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k = {!!}
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
SubListTrans xs₁ Base = xs₁
SubListTrans (Keep xs₂) (Keep ys₁) = Keep (SubListTrans xs₂ ys₁)
SubListTrans (Drop xs₂) (Keep ys₁) = Drop (SubListTrans xs₂ ys₁)
SubListTrans xs₁ (Drop ys₂) = Drop (SubListTrans xs₁ ys₂)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base ys = Refl
SubListAntiSym (Keep xs₁) (Keep ys₁) with SubListAntiSym xs₁ ys₁ 
SubListAntiSym (Keep xs₁) (Keep ys₁) | Refl = Refl
SubListAntiSym (Keep xs₁) (Drop ys₁) = {!!}
SubListAntiSym (Drop xs₁) (Keep ys₂) = {!!}
SubListAntiSym (Drop xs₁) (Drop ys₂) = {!!}


----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
    LEQBase : {n : Nat}   -> LEQ Zero n
    LEQStep : {m n : Nat} -> LEQ m n -> LEQ (Succ m) (Succ n) 

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero     = LEQBase
leqRefl (Succ x) = LEQStep (leqRefl x)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans LEQBase mk = LEQBase
leqTrans (LEQStep nm) (LEQStep mk) = LEQStep (leqTrans nm mk)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym LEQBase LEQBase = Refl
leqAntiSym (LEQStep LEQBase) (LEQStep LEQBase) = Refl
leqAntiSym (LEQStep (LEQStep nm)) (LEQStep mn) with leqAntiSym (LEQStep nm) mn
leqAntiSym (LEQStep (LEQStep nm)) (LEQStep mn') | Refl = Refl

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= LEQBase = Refl
leq<= (LEQStep z) = leq<= z  

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m p = LEQBase {m}
<=leq (Succ n) Zero ()
<=leq (Succ n) (Succ m) p = LEQStep (<=leq n m p)

----------------------
----- Exercise 8 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP a b = b a

-- The reverse does not hold: Not (Not P) does not imply P

-- Similarly, P or Not P doesn't hold for all statements P, but we can
-- prove the statement below. It's an amusing brainteaser.

data Or (a b : Set) : Set where
  Inl : a -> Or a b
  Inr : b -> Or a b

orCase : {a b c : Set} -> (a -> c) -> (b -> c) -> Or a b -> c
orCase f g (Inl x) = f x
orCase f g (Inr x) = g x

-- I found some of these by typing C-c C-a
notNotExcludedMiddle : {P : Set} -> Not (Not (Or P (Not P)))
notNotExcludedMiddle = λ {P} z → z (Inr (λ x → z (Inl x))) 

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
step1 dn {P} = dn (λ z → z (Inr (λ x → z (Inl x)))) 

--step2 : excludedMiddle -> impliesToOr
--step2 = {!!}
step2 : ({P Q : Set} -> Or P (Not P)) -> {P Q : Set} -> (P -> Q) -> (Or (Not P) Q)
step2 x = {!!}

--step3 : impliesToOr -> doubleNegation
step3 : ({P Q : Set} -> (P -> Q) -> Or (Not P) Q ) -> ( {P : Set } -> Not (Not P) -> P )
step3  ito {P} h = {!!}

-- HARDER: show that these are equivalent to Pierces law:
piercesLaw = {P Q : Set} -> ((P -> Q) -> P) -> P

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
-- Stack = (n : Nat) -> Vec Nat n
Stack = List Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total -- how can you fix
-- things so that it is?
exec : Cmd -> Stack -> Stack
exec HALT stack = stack
exec (PUSH n cmds) stack = exec cmds (Cons n stack) 
exec (ADD cmds) Nil = Nil -- this won't work, but I'm leaving it in, as at least I can provide an exec and compile that parse
exec (ADD cmds) (Cons x Nil) = Nil
exec (ADD cmds) (Cons x (Cons y stack)) = exec cmds (Cons (x + y) stack)

-- Define a compiler from expresions to instructions
compile' : Expr -> (Cmd -> Cmd)
compile' (Val x)   r = PUSH x r
compile' (Add x y) r = (compile' x (compile' y (ADD r)))

compile : Expr -> Cmd
compile x = compile' x HALT

-- And prove your compiler correct
correctness : (e : Expr) (s : Stack) -> Cons (eval e) s == exec (compile e) s
correctness e Nil = {!!}
correctness e (Cons x s) = {!!}

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
