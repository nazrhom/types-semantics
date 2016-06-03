
module Exercise2a3 where

--------------------------------------------------------------------------------
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
deterministic true t₁ t₂ () step₂
deterministic false t₁ t₂ () step₂
deterministic (if .true then t₁ else t₂) .t₁ .t₁ E-If-True E-If-True = refl
deterministic (if .true then t₁ else t₂) .t₁ ._ E-If-True (E-If-If ())
deterministic (if .false then t₁ else t₂) .t₂ .t₂ E-If-False E-If-False = refl
deterministic (if .false then t₁ else t₂) .t₂ ._ E-If-False (E-If-If ())
deterministic (if .true then t₁ else t₂) ._ .t₁ (E-If-If ()) E-If-True
deterministic (if .false then t₁ else t₂) ._ .t₂ (E-If-If ()) E-If-False
deterministic (if t then t₁ else t₂) ._ ._ (E-If-If step₁) (E-If-If step₂) with deterministic t _ _ step₁ step₂ 
deterministic (if t then t₁ else t₂) ._ ._ (E-If-If step₁) (E-If-If step₂) | refl = refl
deterministic zero t₁ t₂ () step₂
deterministic (succ t) ._ ._ (E-Succ step₁) (E-Succ step₂) with deterministic t _ _ step₁ step₂
deterministic (succ t) ._ ._ (E-Succ step₁) (E-Succ step₂) | refl = refl
deterministic (iszero .zero) .true .true E-IsZeroZero E-IsZeroZero = refl
deterministic (iszero .zero) .true ._ E-IsZeroZero (E-IsZero ())
deterministic (iszero ._) .false .false (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic (iszero ._) .false ._ (E-IsZeroSucc x) (E-IsZero (E-Succ step₂)) = contradiction (valuesDoNotStep _ _ step₂ x)
deterministic (iszero .zero) ._ .true (E-IsZero ()) E-IsZeroZero
deterministic (iszero ._) ._ .false (E-IsZero (E-Succ step₁)) (E-IsZeroSucc x) = contradiction (valuesDoNotStep _ _ step₁ x)
deterministic (iszero t) ._ ._ (E-IsZero step₁) (E-IsZero step₂) with deterministic t _ _ step₁ step₂
deterministic (iszero t) ._ ._ (E-IsZero step₁) (E-IsZero step₂) | refl = refl


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
uniqueness-of-normal-forms t .t .t Nil Nil nf₁ nf₂ = refl
uniqueness-of-normal-forms t .t t₂ Nil (Cons x step₂) nf₁ nf₂ = contradiction (nf₁ (Reduces x))
uniqueness-of-normal-forms t t₁ .t (Cons x step₁) Nil nf₁ nf₂ = contradiction (nf₂ (Reduces x))
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) nf₁ nf₂ with deterministic t _ _ x x₁ 
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) nf₁ nf₂ | refl with uniqueness-of-normal-forms _ t₁ t₂ step₁ step₂ nf₁ nf₂
uniqueness-of-normal-forms t t₁ .t₁ (Cons x step₁) (Cons x₁ step₂) nf₁ nf₂ | refl | refl = refl

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  B-True : true ⇓ vtrue
  B-False : false ⇓ vfalse
  -- Reviewer modification for parse error
  B-If-True : forall {ty} {c : Term BOOL} {th el : Term ty} {v : Value ty } -> c ⇓ vtrue -> th ⇓ v -> (if c then th else el) ⇓ v
  B-If-False : forall {ty} {c : Term BOOL} {th el : Term ty} {v : Value ty } -> c ⇓ vfalse -> el ⇓ v -> (if c then th else el) ⇓ v
  B-Zero : zero ⇓ vnat Zero
  B-Succ : { t : Term NAT} { v : Nat} -> t ⇓ vnat v -> succ t ⇓ vnat (Succ v)
  B-IsZero-True :  { t : Term NAT } -> t ⇓ vnat Zero -> iszero t ⇓ vtrue
  B-IsZero-False : { t : Term NAT } { v : Nat } -> t ⇓ vnat (Succ v) -> iszero t ⇓ vfalse

map-if : ∀ {ty} {t t' : Term BOOL} {t₁ t₂ : Term ty} -> Steps t t' -> Steps (if t then t₁ else t₂) (if t' then t₁ else t₂)
map-if Nil = Nil
map-if (Cons x steps) = Cons (E-If-If x) (map-if steps)

map-succ : { t t' : Term NAT } -> Steps t t' -> Steps (succ t) (succ t')
map-succ Nil = Nil
map-succ (Cons x steps) = Cons (E-Succ x) (map-succ steps)

map-iszero : { t t' : Term NAT } -> Steps t t' -> Steps (iszero t) (iszero t')
map-iszero Nil = Nil
map-iszero (Cons x steps) = Cons (E-IsZero x) (map-iszero steps)

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small B-True = Nil
big-to-small B-False = Nil
big-to-small (B-If-True p p₁) = map-if (big-to-small p) ++ Cons E-If-True (big-to-small p₁)
big-to-small (B-If-False p p₁) = map-if (big-to-small p) ++ Cons E-If-False (big-to-small p₁)
big-to-small B-Zero = Nil
big-to-small (B-Succ p) = map-succ (big-to-small p)
big-to-small (B-IsZero-True p) = map-iszero (big-to-small p) ++ Cons E-IsZeroZero Nil
big-to-small (B-IsZero-False p ) = map-iszero (big-to-small p) ++ Cons (E-IsZeroSucc (isValueComplete (vnat _))) Nil

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value true V-True = B-True
value-to-value false V-False = B-False
value-to-value (if t then t₁ else t₂) ()
value-to-value zero V-Zero = B-Zero
value-to-value (succ t) (V-Succ p) with toVal t p | value-to-value t p
value-to-value (succ t) (V-Succ p) | vnat x | y = B-Succ y
value-to-value (iszero t) ()

bigstep-values : forall {ty} (t : Term ty) -> Exists (Value ty) (\v -> t ⇓ v)
bigstep-values true = Witness vtrue B-True
bigstep-values false = Witness vfalse B-False
bigstep-values (if t then t₁ else t₂) with bigstep-values t
bigstep-values (if t then t₁ else t₂) | Witness vtrue x₁ with bigstep-values t₁
bigstep-values (if t then t₁ else t₂) | Witness vtrue x₂ | Witness x x₁ = Witness x (B-If-True x₂ x₁)
bigstep-values (if t then t₁ else t₂) | Witness vfalse x₁ with bigstep-values t₂
bigstep-values (if t then t₁ else t₂) | Witness vfalse x₂ | Witness x x₁ = Witness x (B-If-False x₂ x₁)
bigstep-values zero = Witness (vnat Zero) B-Zero
bigstep-values (succ t) with bigstep-values t
bigstep-values (succ t) | Witness (vnat x) x₁ = Witness (vnat (Succ x)) (B-Succ x₁)
bigstep-values (iszero t) with bigstep-values t
bigstep-values (iszero t) | Witness (vnat Zero) x₁ = Witness vtrue (B-IsZero-True x₁)
bigstep-values (iszero t) | Witness (vnat (Succ x)) x₁ = Witness vfalse (B-IsZero-False x₁)

-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t .t p Nil = value-to-value t p
small-to-big t t' p (Cons x steps) = prepend-step t _ (toVal t' p) x (small-to-big _ t' p steps)
  where
  prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
  prepend-step ._ t' v₁ E-If-True bstep = B-If-True B-True bstep
  prepend-step ._ t' v₁ E-If-False bstep = B-If-False B-False bstep
  prepend-step ._ ._ v₁ (E-If-If step) (B-If-True bstep bstep₁) = B-If-True (prepend-step _ _ vtrue step bstep) bstep₁
  prepend-step ._ ._ v₁ (E-If-If step) (B-If-False bstep bstep₁) = B-If-False (prepend-step _ _ vfalse step bstep) bstep₁
  prepend-step ._ ._ ._ (E-Succ step) (B-Succ bstep) = B-Succ (prepend-step _ _ (vnat _) step bstep)
  prepend-step .(iszero zero) .true vtrue E-IsZeroZero bstep = B-IsZero-True B-Zero
  prepend-step .(iszero zero) .true vfalse E-IsZeroZero ()
  prepend-step ._ .false vtrue (E-IsZeroSucc x₁) ()
  prepend-step ._ .false vfalse (E-IsZeroSucc {t} x₁) B-False with bigstep-values t
  prepend-step ._ .false vfalse (E-IsZeroSucc x₃) B-False | Witness (vnat x₁) x₂ = B-IsZero-False (B-Succ x₂)
  prepend-step ._ ._ .vtrue (E-IsZero step) (B-IsZero-True bstep) = B-IsZero-True (prepend-step _ _ (vnat Zero) step bstep)
  prepend-step ._ ._ .vfalse (E-IsZero step) (B-IsZero-False bstep) = B-IsZero-False (prepend-step _ _ (vnat (Succ _)) step bstep)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | p = B-If-True p (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | p = B-If-False p (⇓-complete t₂)
⇓-complete zero = B-Zero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | p = B-Succ p
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | p = B-IsZero-True p
⇓-complete (iszero t) | vnat (Succ x) | p = B-IsZero-False p

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound .true .vtrue B-True = refl
⇓-sound .false .vfalse B-False = refl
⇓-sound ._ v (B-If-True {ty} {c} p p₁) with ⟦ c ⟧ | ⇓-sound _ _ p
⇓-sound ._ v (B-If-True p p₁) | vtrue | refl = ⇓-sound _ _ p₁
⇓-sound ._ v (B-If-True p p₁) | vfalse | ()
⇓-sound ._ v (B-If-False {ty} {c} p p₁) with ⟦ c ⟧ | ⇓-sound _ _ p
⇓-sound ._ v (B-If-False p p₁) | vtrue | ()
⇓-sound ._ v (B-If-False p p₁) | vfalse | refl = ⇓-sound _ _ p₁
⇓-sound .zero .(vnat Zero) B-Zero = refl
⇓-sound ._ ._ (B-Succ {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound ._ .(vnat (Succ v)) (B-Succ p) | vnat v | refl = refl
⇓-sound ._ .vtrue (B-IsZero-True {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound ._ .vtrue (B-IsZero-True p) | vnat .Zero | refl = refl
⇓-sound ._ .vfalse (B-IsZero-False {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound ._ .vfalse (B-IsZero-False p) | vnat ._ | refl = refl
