
module Exercise2a where

-------------------------------------------------------------------------------
----------------------                 Instructions        --------------------
-------------------------------------------------------------------------------

{-

This exercise consists of two parts.  

1. Firstly, complete the missing definitions. You may want to check the
previous version of some lemmas and definitions (BoolDemo.agda) in
case you get stuck.

Note that in many of the lemmas, I have made all arguments
explicit. This way I don't give away too much information about how to
do your induction. In many cases, you can make many of these arguments
implicit - feel free to do so!

2. Extend the Term data type with constructors for creating tuples,
fst, and snd. Update the various semantics accordingly, and complete
the proofs.

You may want to check Chapter 11.7 of Pierce's book to see how he defines
the syntax, semantics and types for tuples.

-}

-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
-- Congruency
cong : {a b : Set} {x y : a} (f : a → b) → x == y → f x == f y
cong f refl = refl

-- Transitivity
trans : {a : Set} {x y z : a} → x == y → y == z → x == z
trans refl refl = refl

-- Symmetry
sym : {a : Set} {x y : a} → x == y → y == x
sym refl = refl

-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

data Exists (a : Set) (b : a → Set) : Set where
  Witness : (x : a) → b x → Exists a b

-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat → Nat

data Either (a b : Set) : Set where
  Left  : a → Either a b
  Right : b → Either a b

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT  : Type 
  BOOL : Type

-- Our Term language
data Term : Type → Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : ∀ {σ} → (c : Term BOOL) → (t e : Term σ) → Term σ
  zero          : Term NAT
  succ          : (n : Term NAT) → Term NAT
  iszero        : (n : Term NAT) → Term BOOL

-- The set of atomic values within the language.
data Value : Type → Set where
  vtrue  : Value BOOL
  vfalse : Value BOOL
  vnat   : Nat → Value NAT

-- Associate each value with a term.
val2term : ∀ {ty} → Value ty → Term ty
val2term vtrue          = true
val2term vfalse        = false
val2term (vnat Zero)      = zero
val2term (vnat (Succ x))  = succ (val2term (vnat x))

-------------------------------------------------------------------------------
----------------------        Denotational semantics       --------------------
-------------------------------------------------------------------------------

-- Evaluation function.
eval : ∀ {ty} → Term ty  → Value ty
eval true      = vtrue
eval false     = vfalse
eval zero      = vnat Zero
eval (succ t)  with eval t 
eval (succ t)  | vnat x = vnat (Succ x)
eval (iszero t)  with eval t 
eval (iszero t) | vnat Zero     = vtrue
eval (iszero t) | vnat (Succ x) = vfalse
eval (if t then t₁ else t₂) with eval t 
eval (if t then t₁ else t₂) | vtrue  = eval t₁ 
eval (if t then t₁ else t₂) | vfalse = eval t₂ 

-------------------------------------------------------------------------------
-- Small-step semantics.
-------------------------------------------------------------------------------

data IsValue : {ty : Type} → Term ty → Set where
  V-True  : IsValue true
  V-False : IsValue false
  V-Zero  : IsValue zero
  V-Succ  : ∀ {x} → IsValue x → IsValue (succ x)

isValueComplete : ∀ {ty} → (v : Value ty) → IsValue (val2term v)
isValueComplete vtrue           = V-True
isValueComplete vfalse          = V-False
isValueComplete (vnat Zero)     = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))

isValueSound : ∀ {ty} {t : Term ty} → IsValue t → Exists (Value ty) (\v → (val2term v) == t)
isValueSound V-True  = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero  = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)

data Step  : {ty : Type} → Term ty → Term ty → Set where
  E-If-True    : ∀ {ty} {t1 t2  : Term ty} → Step (if true then t1 else t2) t1
  E-If-False   : ∀ {ty} {t1 t2  : Term ty} → Step (if false then t1 else t2) t2
  E-If-If      : ∀ {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} → Step t1 t1' → Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : ∀ {t t' : Term NAT} → Step t t' → Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t    : Term NAT} → IsValue t → Step (iszero (succ t)) false
  E-IsZero     : ∀ {t t' : Term NAT} → Step t t' → Step (iszero t) (iszero t')

preservation : ∀ {ty} → (t t' : Term ty) → Step t t' → ty == ty
preservation t t' step = refl

valuesDoNotStep : ∀ {ty} → (t t' : Term ty) → Step t t' → IsValue t → Empty
valuesDoNotStep .true  t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero  t' () V-Zero
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v

-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} → Step t t' → Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} → Term ty → Set
NF t = Red t → Empty

toVal : ∀ {ty} → (t : Term ty) → IsValue t → Value ty
toVal .true V-True   = vtrue
toVal .false V-False = vfalse
toVal .zero V-Zero   = vnat Zero
toVal _ (V-Succ v) with toVal _ v
toVal _ (V-Succ v) | vnat x₁ = vnat (Succ x₁)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true  t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)

  iszero-reduces : (t : Term NAT) → Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))

  succ-nf : (k : Term NAT) → NF (succ k) → Red k → Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true       nf = V-True
  normal-forms-are-values false      nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero       nf = V-Zero
  normal-forms-are-values (succ t)   nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))

  values-are-normal-forms : ∀ {ty} → {t : Term ty} → IsValue t → NF t
  values-are-normal-forms p (Reduces step) = valuesDoNotStep _ _ step p

  lemma : (k : Term NAT) → NF k → NF (succ k)
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} → (t : Term ty) → Either (NF t) (Red t)
  progress true  = Left (values-are-normal-forms V-True)
  progress false = Left (values-are-normal-forms V-False)
  progress (if t then t₁ else t₂) = Right (if-reduces _ _ _)
  progress zero = Left (values-are-normal-forms V-Zero)
  progress (succ t) with progress t
  progress (succ t) | Left x = Left (lemma t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) = Right (iszero-reduces _ )

--------------------------------------------------------------------------------
---------------------------       EXERCISES       ------------------------------
--------------------------------------------------------------------------------

-- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True (E-If-If ())
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-IsZero ()) E-IsZeroZero
deterministic E-IsZeroZero (E-IsZero ())
deterministic E-If-False E-If-False             = refl
deterministic E-If-True E-If-True               = refl
deterministic (E-IsZeroSucc _) (E-IsZeroSucc _) = refl
deterministic E-IsZeroZero E-IsZeroZero         = refl
deterministic (E-If-If x) (E-If-If y)           = cong (λ z → if z then _ else _) (deterministic x y)
deterministic (E-Succ  x) (E-Succ y)            = cong succ   (deterministic x y)
deterministic (E-IsZero x) (E-IsZero y)         = cong iszero (deterministic x y)
deterministic (E-IsZeroSucc x) (E-IsZero y)     = {!!} 
deterministic (E-IsZero x) (E-IsZeroSucc y)     = {!!}

-- (1/2) * 13 / 18 points

-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil  : ∀ {t} → Steps t t
  Cons : ∀ {t1 t2 t3} → Step t1 t2 → Steps t2 t3 → Steps t1 t3

-- Single-step sequence.
[_] : ∀ {ty} {t₁ t₂ : Term ty} → Step t₁ t₂ → Steps t₁ t₂
[_] x = Cons x Nil
  
-- Concatenation.
infixr 5 _++_
_++_ : ∀ {ty} {t₁ t₂ t₃ : Term ty} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ ys = ys
Cons x xs ++ ys = Cons x (xs ++ ys)

-- If steps extension from the Booldemo
E-If-Steps : ∀ {ty} {c c'} {t₁ t₂ : Term ty} → Steps c c' → Steps (if c then t₁ else t₂) (if c' then t₁ else t₂)
E-If-Steps Nil            = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

-- E-Succ-Steps derived from E-If-Steps
E-Succ-Steps : {t₁ t₂ : Term NAT} → Steps t₁ t₂ → Steps (succ t₁) (succ t₂)
E-Succ-Steps Nil         = Nil
E-Succ-Steps (Cons x xs) = Cons (E-Succ x) (E-Succ-Steps xs)

-- Same ^
E-IsZero-Steps : {t₁ t₂ : Term NAT} → Steps t₁ t₂ → Steps (iszero t₁) (iszero t₂)
E-IsZero-Steps Nil         = Nil
E-IsZero-Steps (Cons x xs) = Cons (E-IsZero x) (E-IsZero-Steps xs)

-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms : ∀ {ty} {t t₁ t₂ : Term ty} → Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms  Nil         Nil        norm₁ norm₂ = refl
uniqueness-of-normal-forms  Nil        (Cons y ys) norm₁ norm₂ = contradiction (norm₁ (Reduces y))
uniqueness-of-normal-forms (Cons x xs)  Nil        norm₁ norm₂ = contradiction (norm₂ (Reduces x))
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) norm₁ norm₂ with deterministic x y
uniqueness-of-normal-forms (Cons x xs) (Cons y ys) norm₁ norm₂ | refl = uniqueness-of-normal-forms xs ys norm₁ norm₂

-- (1/2) * 4 / 4 points

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} → Term ty → Value ty → Set where
  B-True       : true  ⇓ vtrue
  B-False      : false ⇓ vfalse
  B-Zero       : zero  ⇓ vnat Zero
  B-Succ       : {val : Nat} {t : Term NAT} → t ⇓ vnat val → succ t ⇓ vnat (Succ val)
  B-If-True    : ∀ {ty} {c} {t₁ t₂ : Term ty} {val : Value ty} → c ⇓ vtrue  → t₁ ⇓ val → (if c then t₁ else t₂) ⇓ val
  B-If-False   : ∀ {ty} {c} {t₁ t₂ : Term ty} {val : Value ty} → c ⇓ vfalse → t₂ ⇓ val → (if c then t₁ else t₂) ⇓ val
  B-IsZeroZero : {n : Term NAT} → n ⇓ (vnat Zero) → (iszero n) ⇓ vtrue
  B-IsZeroSucc : {n : Nat} {m : Term NAT}  → m ⇓ vnat (Succ n) → iszero m ⇓ vfalse

-- 1 * 6 / 8 points. IsZeroZero and IsZeroSucc should be IsZeroFalse and IsZeroTrue

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t (val2term v)
big-to-small B-True               = Nil
big-to-small B-False              = Nil
big-to-small B-Zero               = Nil
big-to-small (B-Succ x)           = E-Succ-Steps (big-to-small x) 
big-to-small (B-IsZeroZero x)     = E-IsZero-Steps (big-to-small x) ++ [ E-IsZeroZero ]
big-to-small (B-IsZeroSucc {n} a) = E-IsZero-Steps (big-to-small a) ++ [ E-IsZeroSucc {!!} ]
big-to-small (B-If-True  x y)     = E-If-Steps (big-to-small x) ++ ([ E-If-True ]  ++ big-to-small y)
big-to-small (B-If-False x y)     = E-If-Steps (big-to-small x) ++ ([ E-If-False ] ++ big-to-small y)

-- 1 * 7 / 8 points. Counting the isZeroZero and IsZeroSucc. 6 / 8 otherwise

-- Conversion from small- to big-step representations.
value-to-value : ∀ {ty} {t : Term ty} → (p : IsValue t) → t ⇓ toVal t p
value-to-value V-True     = B-True
value-to-value V-False    = B-False
value-to-value V-Zero     = B-Zero
value-to-value (V-Succ p) = {!!}

-- ? * 3 / 4 points. Not specified in email

-- And conversion in the other direction
small-to-big : {ty : Type} → {t t' : Term ty} → (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big p steps = {!!}
  where
  prepend-step : {ty : Type} → (t t' : Term ty) (v : Value ty) → Step t t' → t' ⇓ v → t ⇓ v
  prepend-step = {!!}

-- 1 * 0 / 17 points

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ eval t
⇓-complete true       = B-True
⇓-complete false      = B-False
⇓-complete zero       = B-Zero
⇓-complete (succ t)   = {!!}
⇓-complete (iszero t) = {!!}
⇓-complete (if t then t₁ else t₂) = {!!}

-- 1 * 3 / 10 points

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → v == eval t
⇓-sound B-True  = refl
⇓-sound B-False = refl
⇓-sound B-Zero  = refl
⇓-sound (B-Succ x)       = {!!}
⇓-sound (B-If-True  x y) = {!!}
⇓-sound (B-If-False x y) = {!!}
⇓-sound (B-IsZeroZero x) = {!!}
⇓-sound (B-IsZeroSucc x) = {!!}

-- 1 * 3 / 8 points:

-- * Determinism & uniqueness of normal forms proofs
--   1.2222 points
-- * Definition of big step semantics
--   0.75 points
-- * Big-to-small and small-to-big lemmas
--   0.875 points
-- * Soundness and completeness of big-step semantics
--   0.675 points
-- * Small step semantics, big step semantics and denotational semantics of pairs
--   0 points
-- * Updating existing proofs to handle pairs
--   0 points
--
-- Total: 3.52 points (39.1 % of max)
