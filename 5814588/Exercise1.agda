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

c = Succ (Succ Zero)

{-# BUILTIN NATURAL Nat #-}




_+_ : Nat -> Nat -> Nat
Zero + m = m
Succ n + m = Succ (n + m)

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

_⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A} → x == y → y == z → x == z
x ⟨ Refl ⟩ Refl = Refl

infixr 2 _⟨_⟩_

_∎ : ∀ {A : Set} (x : A) → x == x
x ∎ = Refl

infix  2 _∎

----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {Zero} x = Nil   
pure {Succ n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
_<*>_ Nil _ = Nil
_<*>_ (Cons f fs) (Cons x xs) = Cons (f x) (fs <*> xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> Nat -> Nat -> Set
Matrix a m n = Vec (Vec a m) n 

-- Define matrix addition
vmap2 : {a b c : Set} {n : Nat} -> (a -> b -> c) -> Vec a n -> Vec b n -> Vec c n
vmap2 f Nil _ = Nil
vmap2 f (Cons x xs) (Cons y ys) = Cons (f x y) (vmap2 f xs ys)

madd : {n m : Nat} -> Matrix Nat m n -> Matrix Nat m n -> Matrix Nat m n
madd Nil _ = Nil
madd (Cons xs xss) (Cons ys yss) = Cons (vmap2 _+_ xs ys) (madd xss yss)

-- Define the identity matrix
createIdVector : (n : Nat) -> (col : Nat) -> Vec Nat n
createIdVector Zero _ = Nil
createIdVector (Succ n) (Succ col) = Cons Zero (createIdVector n col)
createIdVector (Succ n) (Zero) = Cons (Succ Zero) (createIdVector n (Succ n))

idRecMatrix : (n : Nat) -> (m : Nat) -> (col : Nat)  -> Matrix Nat n m
idRecMatrix _ Zero _ = Nil
idRecMatrix n (Succ m) col = Cons (createIdVector n col) (idRecMatrix n m (Succ col))

idMatrix : {n : Nat} -> Matrix Nat n n
idMatrix {n} = idRecMatrix n n Zero


-- Define matrix transposition

tail : {n : Nat} {a : Set} -> Vec a (Succ n) -> Vec a n
tail (Cons x xs) = xs

transpose : {m n : Nat} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {Zero} _ = Nil
transpose {Succ m} xss = Cons (vmap head xss) (transpose (vmap tail xss))

----------------------
----- Exercise 3 -----
----------------------

-- Define a few functions manipulating finite types.

-- The result of "plan {n}" should be a vector of length n storing all
-- the inhabitants of Fin n in increasing order.

plan : {n : Nat} -> Vec (Fin n) n
plan {Zero} = Nil
plan {Succ n} = Cons Fz (vmap Fs (plan {n}))

-- Define a forgetful map, mapping Fin to Nat
forget : {n : Nat} -> Fin n -> Nat
forget Fz = Zero
forget (Fs i) = Succ (forget i)

-- There are several ways to embed Fin n in Fin (Succ n).  Try to come
-- up with one that satisfies the correctness property below (and
-- prove that it does).

-- moved embed in order to use it for plan
embed : {n : Nat} -> Fin n -> Fin (Succ n)
embed Fz = Fz
embed (Fs i) = Fs (embed i)

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

-- Show that there is a 'Covering function'
cmp : (n m : Nat) -> Compare n m
cmp Zero (Succ m) = LessThan m
cmp Zero Zero = Equal
cmp (Succ n) Zero = GreaterThan n 
cmp (Succ n) (Succ m) with cmp n m
cmp (Succ n) (Succ .(n + Succ k))   | LessThan k = LessThan k
cmp (Succ n) (Succ .n)              | Equal = Equal
cmp (Succ .(m + (Succ k))) (Succ m) | GreaterThan k = GreaterThan k

-- Use the cmp function you defined above to define the absolute
-- difference between two natural numbers.
difference : (n m : Nat) -> Nat
difference n m with cmp n m
difference n .(n + Succ k) | LessThan k = Succ k
difference n .n            | Equal = Zero
difference .(m + Succ k) m | GreaterThan k = Succ k

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
plusZero (Succ n) = cong Succ (plusZero n) -- Use congs

plusSucc : (n m : Nat) -> Succ (n + m) == (n + Succ m)
plusSucc Zero m = Refl
plusSucc (Succ n) m = cong Succ (plusSucc n m)

plusCommutes : (n m : Nat) -> (n + m) == (m + n)
plusCommutes n Zero = plusZero n
plusCommutes n (Succ m) =
    n + Succ m
  ⟨ sym (plusSucc n m) ⟩
    Succ (n + m)
  ⟨ cong Succ (plusCommutes n m) ⟩
    ((Succ (m + n)) ∎)

-- For the Distributivity, I created the assoc and assoc-sym functions
-- which are used for getting the natural numbers in the right place

assoc : (n m k : Nat) -> ((n + m) + k) == (n + (m + k))
assoc Zero m k = Refl
assoc (Succ n) m k = cong Succ (assoc n m k)

assoc-sym : (n m k : Nat) -> (n + (m + k)) == (m + (n + k))
assoc-sym n m k = (n + (m + k))
  ⟨ sym (assoc n m k) ⟩
    ((n + m) + k)
  ⟨  cong (\{ x -> x + k}) (plusCommutes n m) ⟩
    ((m + n) + k)
  ⟨ assoc m n k ⟩
    ((m + (n + k)) ∎)

distributivity : (n m k : Nat) -> (n * (m + k)) == ((n * m) + (n * k))
distributivity Zero m k = Refl
distributivity (Succ n) m k =
    (m + k) + (n * (m + k))
  ⟨ cong (\{ x -> (m + k) + x}) (distributivity n m k) ⟩
    (m + k) + ((n * m) + (n * k))
  ⟨ assoc m k ((n * m) + (n * k)) ⟩
    m + (k + ((n * m) + (n * k)))
  ⟨ cong (\{ x -> m + x}) (assoc-sym k (n * m) (n * k)) ⟩
    m + ((n * m) + (k + (n * k)))
  ⟨ sym (assoc m (n * m) (k + (n * k))) ⟩
    (((m + (n * m)) + (k + (n * k)) ∎))

----------------------
----- Exercise 6 -----
----------------------

-- Prove that the sublist relation defined below is transitive and reflexive.

data SubList {a : Set} : List a -> List a -> Set where
  Base : SubList Nil Nil
  Keep : forall {x xs ys} -> SubList xs ys -> SubList (Cons x xs) (Cons x ys)
  Drop : forall {y zs ys} -> SubList zs ys -> SubList zs (Cons y ys)

SubListRefl : {a : Set} {xs : List a} -> SubList xs xs
SubListRefl {_} {Nil} = Base
SubListRefl {_} {Cons x xs} = Keep SubListRefl

SubListTrans : {a : Set} {xs ys zs : List a} -> SubList xs ys -> SubList ys zs -> SubList xs zs
SubListTrans Base b = b
SubListTrans (Keep a) (Keep b) = Keep (SubListTrans a b)
SubListTrans (Keep a) (Drop b) = Drop (SubListTrans (Keep a) b) 
SubListTrans (Drop a) (Keep b) = Drop (SubListTrans a b)
SubListTrans (Drop a) (Drop b) = Drop (SubListTrans (Drop a) b)

ssxs : List Nat
ssxs = Cons 5 (Cons 3 (Cons 1 Nil))

ssys : List Nat
ssys = Cons 3 (Cons 1 Nil)

StillSubList : {a : Set} {x : a} {xs ys : List a} -> SubList (Cons x xs) ys -> SubList xs ys
StillSubList (Keep s) = Drop s
StillSubList (Drop s) = Drop (StillSubList s)

NotCorrect : {a : Set} {x : a} {xs : List a} -> SubList (Cons x xs) xs -> Empty
NotCorrect (Keep s) = NotCorrect s
NotCorrect (Drop s) = NotCorrect (StillSubList s)

SubListAntiSym : {a : Set} {xs ys : List a} ->  SubList xs ys -> SubList ys xs -> xs == ys
SubListAntiSym Base _ = Refl
SubListAntiSym {xs = Cons x xs} {ys = Cons .x ys} (Keep s1) (Keep s2) = cong (Cons x) (SubListAntiSym s1 s2)
SubListAntiSym {xs = Cons x xs} {ys = Cons .x ys} (Keep s1) (Drop s2) = cong (Cons x) (SubListAntiSym s1 (StillSubList s2))
SubListAntiSym {xs = Cons x xs} {ys = Cons .x ys} (Drop s1) (Keep s2) = cong (Cons x) (SubListAntiSym (StillSubList s1) s2)
SubListAntiSym {xs = Cons x xs} {ys = Cons y ys} (Drop s1) (Drop s2) = magic ( NotCorrect (SubListTrans s1 (StillSubList s2)))
----------------------
----- Exercise 7 -----
----------------------

-- Define the constructors of a data type 
data LEQ : Nat -> Nat -> Set where
  Leq-Zero : forall {n} -> LEQ Zero n
  Leq-Succ : forall {n  m} -> LEQ n m -> LEQ (Succ n) (Succ m) 

-- (Alternative correct definitions exist - this one is the easiest to
-- work with for the rest of this exercise)

leqRefl : (n : Nat) -> LEQ n n
leqRefl Zero = Leq-Zero
leqRefl (Succ n) = Leq-Succ (leqRefl n)

leqTrans : {n m k : Nat} -> LEQ n m -> LEQ m k -> LEQ n k
leqTrans Leq-Zero _ = Leq-Zero
leqTrans (Leq-Succ leq1) (Leq-Succ leq2) = Leq-Succ (leqTrans leq1 leq2)

leqAntiSym : {n m : Nat} -> LEQ n m -> LEQ m n -> n == m
leqAntiSym Leq-Zero Leq-Zero = Refl
leqAntiSym (Leq-Succ leq1) (Leq-Succ leq2) = cong Succ (leqAntiSym leq1 leq2)

-- Given the following function:
_<=_ : Nat -> Nat -> Bool
Zero <= y = True
Succ x <= Zero = False
Succ x <= Succ y = x <= y

-- Now show that this function behaves as the LEQ data type

leq<= : {n m : Nat} -> LEQ n m -> (n <= m) == True
leq<= Leq-Zero = Refl
leq<= (Leq-Succ l) = leq<= l

<=leq : (n m : Nat) -> (n <= m) == True -> LEQ n m
<=leq Zero m x = Leq-Zero
<=leq (Succ l) Zero ()
<=leq (Succ l) (Succ m) x = Leq-Succ (<=leq l m x) 

----------------------
----- Exercise 7 -----
----------------------

-- We can define negation as follows
Not : Set -> Set
Not P = P -> Empty

-- Agda's logic is *constructive*, meaning some properties you may be
-- familiar with from classical logic do not hold.

notNotP : {P : Set} -> P -> Not (Not P)
notNotP P = \{ z -> z P}

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
notNotExcludedMiddle = \{ z -> z (Inr (\{ x -> z (Inl x) } ))}

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

step2 : excludedMiddle -> impliesToOr
step2 em with em
step2 em | Inl a =  \{ {P} z -> Inr (z (a {P}))}
step2 em | Inr b = \{ {P} z -> Inl {!!} }

step3 : impliesToOr -> doubleNegation
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

Stack : Nat -> Set
Stack = Vec Nat

-- Complete the following definition, executing a list of instructions
-- Note: there 'obvious' definition is not total -- how can you fix
-- things so that it is?

-- Define a compiler from expresions to instructions

data Cmd : Nat -> Nat -> Set where
  -- stop execution and return the current stack
  HALT : forall {n} -> Cmd (Succ n) (Succ n)
  -- push a new number on the stack
  PUSH : forall {n m} ->  Nat -> Cmd (Succ n) m -> Cmd n m
  -- replace the top two elements of the stack with their sum
  ADD : forall {n m} -> Cmd (Succ n) m -> Cmd (Succ (Succ n)) m

_++_ : {n m : Nat} -> (e : Expr) -> Cmd (Succ n) m -> Cmd n m
Add e e₁ ++ c = e₁ ++ (e ++ (ADD c))
Val x ++ c = PUSH x c

compile : {n : Nat} -> (e : Expr) -> Cmd n (Succ n)
compile (Val x) = PUSH x HALT
compile (Add e e₁) = e₁ ++ (e ++ (ADD HALT))

exec : {n m : Nat} -> Cmd n m -> Stack n -> Stack m
exec HALT s = s
exec (PUSH x c) s = exec c (Cons x s)
exec (ADD c) (Cons x (Cons x₁ s)) = exec c (Cons (x + x₁) s)

-- And prove your compiler correct

-- subfunction, needed to prove the correctness. Unfortunately, not final
subCorrect : { n m : Nat} -> { s : Stack n } -> (c : Cmd (Succ n) m) -> (e : Expr) -> exec c (exec (compile e) s) == exec (e ++ c) s
subCorrect HALT (Add e e₁) = Refl
subCorrect HALT (Val x) = Refl
subCorrect (PUSH x c) (Val x₁) = Refl
subCorrect {n} {m} {s} (PUSH x c) (Add e e₁) = {!!}
subCorrect (ADD c) (Val x) = Refl
subCorrect (ADD c) (Add e e₁) = {!!}

-- Proof for correctness using subCorrect
correctness : {n : Nat} (e : Expr) (s : Stack n) -> Cons (eval e) s == exec (compile e) s
correctness (Val x) s = Refl
correctness (Add e e₁) s =
    exec (ADD HALT) (Cons (eval e) (Cons (eval e₁) s))
  ⟨ cong (\{x -> exec (ADD HALT) x}) (correctness e (Cons (eval e₁) s)) ⟩
    exec (ADD HALT) (exec (compile e) (Cons (eval e₁) s))
  ⟨ cong (\{x -> exec (ADD HALT) (exec (compile e) x)}) (correctness e₁ s) ⟩
    exec (ADD HALT) (exec (compile e) (exec (compile e₁) s))
  ⟨ subCorrect ((ADD HALT)) e ⟩
    exec (e ++ (ADD HALT)) (exec (compile e₁) s)
  ⟨ subCorrect ((e ++ (ADD HALT))) e₁ ⟩
    (exec (e₁ ++ (e ++ (ADD HALT))) s ∎)

--BONUS exercises: extend the language with new constructs for let
--bindings, variables, new operators, mutable references, assignment,
--functions, ...
