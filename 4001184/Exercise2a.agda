
module Exercise2a where

--------------------------------------------------------------------------------
-- Rogier Wuijts
-- I didn't manage to do part 2 and the sound and complete proof
--Instructions--
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
--------------------------------------------------------------------------------



-------------------------------------------------------------------------------
----------------------                 Prelude             --------------------
-------------------------------------------------------------------------------

-- Equality.
data _==_ {A : Set} (x : A) : A → Set where
  refl : x == x
  
cong : {a b : Set} {x y : a} (f : a -> b) -> x == y -> f x == f y
cong f refl = refl

-- Contradiction type.
data Empty : Set where

-- Reducto ab absurdum.
contradiction : {A : Set} → Empty → A
contradiction ()

data Exists (a : Set) (b : a -> Set) : Set where
  Witness : (x : a) -> b x -> Exists a b


-- Negation
Not : Set → Set
Not A = A → Empty

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

data Either (a b : Set) : Set where
  Left : a -> Either a b
  Right : b -> Either a b

-------------------------------------------------------------------------------
----------------------                Syntax             ----------------------
-------------------------------------------------------------------------------

data Type : Set where
  NAT : Type 
  BOOL : Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------


-- Evaluation function.
⟦_⟧ : forall {ty} ->  Term ty  → Value ty
⟦ true ⟧ = vtrue
⟦ false ⟧ = vfalse
⟦ if t then t₁ else t₂ ⟧ with ⟦ t ⟧
⟦ if t then t₁ else t₂ ⟧ | vtrue = ⟦ t₁ ⟧
⟦ if t then t₁ else t₂ ⟧ | vfalse = ⟦ t₂ ⟧
⟦ zero ⟧ = vnat Zero
⟦ succ t ⟧ with ⟦ t ⟧
⟦ succ t ⟧ | vnat x = vnat (Succ x)
⟦ iszero t ⟧ with ⟦ t ⟧
⟦ iszero t ⟧ | vnat Zero = vtrue
⟦ iszero t ⟧ | vnat (Succ x) = vfalse



-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep ._ ._ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v

-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

toVal : forall {ty} -> (t : Term ty) -> IsValue t -> Value ty
toVal .true V-True = vtrue
toVal .false V-False = vfalse
toVal .zero V-Zero = vnat Zero
toVal ._ (V-Succ v) with toVal _ v
toVal ._ (V-Succ v) | vnat x₁ = vnat (Succ x₁)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))

  values-are-normal-forms : forall {ty} -> {t : Term ty} -> IsValue t -> NF t
  values-are-normal-forms p (Reduces step) = valuesDoNotStep _ _ step p

  lemma : (k : Term NAT) -> NF k -> NF (succ k)
  lemma t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms V-True)
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
deterministic : ∀ {ty} (t t₁ t₂ : Term ty) → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic ._ t3 .t3 E-If-True E-If-True = refl
deterministic ._ t2 ._ E-If-True (E-If-If ())
deterministic ._ t3 .t3 E-If-False E-If-False = refl
deterministic ._ t3 ._ E-If-False (E-If-If ())
deterministic ._ ._ t2 (E-If-If ()) E-If-True
deterministic ._ ._ t4 (E-If-If ()) E-If-False
deterministic ._ ._ ._ (E-If-If s1) (E-If-If s2) with deterministic _ _ _ s1 s2
deterministic ._ ._ ._ (E-If-If s1) (E-If-If s2) | refl = refl
deterministic ._ ._ ._ (E-Succ s1) (E-Succ s2) with deterministic _ _ _ s1 s2
deterministic ._ ._ ._ (E-Succ s1) (E-Succ s2) | refl = refl
deterministic .(iszero zero) .true .true E-IsZeroZero E-IsZeroZero = refl
deterministic .(iszero zero) .true ._ E-IsZeroZero (E-IsZero ())
deterministic ._ .false true (E-IsZeroSucc x) ()
deterministic ._ .false false (E-IsZeroSucc x) s2 = refl
deterministic ._ .false (if t2 then t3 else t4) (E-IsZeroSucc x) ()
deterministic ._ .false (iszero (if t2 then t3 else t4)) (E-IsZeroSucc x) (E-IsZero ())
deterministic ._ .false (iszero zero) (E-IsZeroSucc x) (E-IsZero ())
deterministic .(iszero (succ zero)) .false (iszero (succ t2)) (E-IsZeroSucc V-Zero) (E-IsZero (E-Succ ()))
deterministic ._ .false (iszero (succ ._)) (E-IsZeroSucc (V-Succ x₁)) (E-IsZero (E-Succ (E-Succ s2))) = contradiction (valuesDoNotStep _ _ s2 x₁)
deterministic .(iszero zero) ._ .true (E-IsZero ()) E-IsZeroZero
deterministic ._ ._ .false (E-IsZero s1) (E-IsZeroSucc x) = contradiction (valuesDoNotStep _ _ s1 (V-Succ x))
deterministic ._ ._ ._ (E-IsZero s1) (E-IsZero s2) = cong iszero (deterministic _ _ _ s1 s2)
-- A sequence of steps that can be applied in succession.
data Steps {ty : Type} : Term ty → Term ty → Set where
  Nil : forall {t} -> Steps t t
  Cons : forall {t1 t2 t3} -> Step t1 t2 -> Steps t2 t3 -> Steps t1 t3

-- Single-step sequence.
[_] : ∀ {ty} {t₁ t₂ : Term ty} -> Step t₁ t₂ -> Steps t₁ t₂
[_] x = Cons x Nil
  
-- Concatenation.
_++_ : ∀ {ty} {t₁ t₂ t₃ : Term ty} → Steps t₁ t₂ → Steps t₂ t₃ → Steps t₁ t₃
Nil ++ stps' = stps'
Cons x stps ++ stps' = Cons x (stps ++ stps')

infixr 5 _++_


-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms :
  ∀ {ty} (t t₁ t₂ : Term ty) →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms t1 .t1 .t1 Nil Nil n1 n2 = refl
uniqueness-of-normal-forms t1 .t1 t2 Nil (Cons x s2) n1 n2 = contradiction (valuesDoNotStep _ _ x (normal-forms-are-values t1 n1))
uniqueness-of-normal-forms t2 t1 .t2 (Cons x s1) Nil n1 n2 = contradiction (valuesDoNotStep _ _ x (normal-forms-are-values t2 n2))
uniqueness-of-normal-forms t t1 t2 (Cons x s1) (Cons x1 s2) n1 n2 with (deterministic _ _ _ x x1 )
uniqueness-of-normal-forms t t1 t3 (Cons x s1) (Cons x1 s2) n1 n2 | refl = uniqueness-of-normal-forms _ _ _ s1 s2 n1 n2

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  evalTrue : true ⇓ vtrue
  evalFalse : false ⇓ vfalse
  evalIfTrue : forall {ty} {c : Term BOOL} {t e : Term ty} {v : Value ty} -> c ⇓ vtrue -> t ⇓ v -> (if c then t else e) ⇓ v
  evalIfFalse : forall {ty} {c : Term BOOL} {t e : Term ty} {v : Value ty} -> c ⇓ vfalse -> e ⇓ v -> (if c then t else e) ⇓ v
  evalZero : zero ⇓ (vnat Zero)
  evalSucc : forall {n : Term NAT} {v : Nat} -> n ⇓ (vnat v) -> (succ n) ⇓ vnat (Succ v)
  evalIsZeroTrue : forall {n} -> n ⇓ (vnat Zero) -> (iszero n) ⇓ vtrue
  evalIsZeroFalse : forall {n : Term NAT} {v : Nat} -> n ⇓ (vnat (Succ v)) -> (iszero n) ⇓ vfalse

E-If-Steps : ∀ {ty} {t₁ t₁′ : Term BOOL} {t₂ t₃ : Term ty} →
        Steps t₁ t₁′ →
        Steps (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)


-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small evalTrue = Nil
big-to-small evalFalse = Nil
big-to-small (evalIfTrue p p₁) with big-to-small p | big-to-small p₁
... | l1 | l2 = E-If-Steps l1 ++ ([ E-If-True ] ++ l2)
big-to-small (evalIfFalse p p₁) with big-to-small p | big-to-small p₁
... | l1 | l2 = E-If-Steps l1 ++ ([ E-If-False ] ++ l2)
big-to-small evalZero = Nil
big-to-small (evalSucc p) = E-Succ-Steps (big-to-small p)
  where
  E-Succ-Steps : {t₁ t₁′ : Term NAT} → Steps t₁ t₁′ →  Steps (succ t₁) (succ t₁′)
  E-Succ-Steps Nil = Nil
  E-Succ-Steps (Cons x s) = Cons (E-Succ x) (E-Succ-Steps s) 
big-to-small (evalIsZeroTrue p) = E-iszero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
  where
  E-iszero-Steps : {t1 t2 : Term NAT}-> Steps t1 t2 -> Steps (iszero t1) (iszero t2)
  E-iszero-Steps Nil = Nil
  E-iszero-Steps (Cons x s) = Cons (E-IsZero x) (E-iszero-Steps s)
big-to-small (evalIsZeroFalse p) = E-iszero-false-Steps _ _ ( big-to-small p)
  where
  E-iszero-false-Steps : (v : Value NAT)(t1 : Term NAT) -> Steps t1 (succ  ⌜ v ⌝) -> Steps (iszero t1) (false)
  E-iszero-false-Steps v .(succ ⌜ v ⌝) Nil = Cons (E-IsZeroSucc (isValueComplete v)) Nil
  E-iszero-false-Steps v t1 (Cons x s) = Cons (E-IsZero x) (E-iszero-false-Steps v _ s)


-- Conversion from small- to big-step representations.


value-to-value : forall (ty : Type) (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .BOOL true V-True = evalTrue
value-to-value .BOOL false V-False = evalFalse
value-to-value ty (if t then t₁ else t₂) ()
value-to-value .NAT zero V-Zero = evalZero
value-to-value .NAT (succ t) (V-Succ p) = v2v t p (value-to-value NAT t p)
  where
  v2v : (t : Term NAT) -> (p : IsValue t)  -> t ⇓ toVal t p -> (succ t) ⇓ toVal (succ t) (V-Succ p)
  v2v t p bs with toVal t p
  v2v t p bs | vnat x = evalSucc bs
value-to-value .BOOL (iszero t) ()



-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t2 .t2 p Nil = value-to-value _ t2 p
small-to-big t1 t2 p (Cons x s) = prepend-step t1 _ (toVal t2 p) x (small-to-big _ _ p s)
  where
  prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
  prepend-step ._ t2 v₁ E-If-True bs = evalIfTrue evalTrue bs
  prepend-step ._ t2 v₁ E-If-False bs = evalIfFalse evalFalse bs
  prepend-step ._ ._ v₁ (E-If-If s) (evalIfTrue bs bs₁) = evalIfTrue (prepend-step _ _ vtrue s bs) bs₁
  prepend-step ._ ._ v₁ (E-If-If s) (evalIfFalse bs bs₁) = evalIfFalse (prepend-step _ _ vfalse s bs) bs₁
  prepend-step ._ ._ ._ (E-Succ s) (evalSucc bs) = evalSucc (prepend-step _ _ (vnat _) s bs)
  prepend-step .(iszero zero) .true .vtrue E-IsZeroZero evalTrue = evalIsZeroTrue evalZero
  prepend-step .(iszero (succ zero)) .false .vfalse (E-IsZeroSucc V-Zero) evalFalse = evalIsZeroFalse (evalSucc evalZero)
  prepend-step ._ .false .vfalse (E-IsZeroSucc (V-Succ x₁)) evalFalse = evalIsZeroFalse2 ((prepend-step (iszero (succ _)) false vfalse (E-IsZeroSucc x₁)
                                                                        evalFalse))
               where
               evalIsZeroFalse2 : forall {n : Term NAT} {v : Value BOOL} -> (iszero n) ⇓ v -> (iszero (succ n)) ⇓ vfalse   
               evalIsZeroFalse2 (evalIsZeroTrue bs) = evalIsZeroFalse (evalSucc bs)
               evalIsZeroFalse2 (evalIsZeroFalse bs) = evalIsZeroFalse (evalSucc bs)
  prepend-step ._ ._ .vtrue (E-IsZero s) (evalIsZeroTrue bs) = evalIsZeroTrue (prepend-step _ _ (vnat Zero) s bs)
  prepend-step ._ ._ .vfalse (E-IsZero s) (evalIsZeroFalse bs) = evalIsZeroFalse (prepend-step _ _ (vnat (Succ _)) s bs)

------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete = {!!}
 
-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound = {!!}
