
module Exercise2a where

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
  _X_ : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- And tuples
  tuple           : forall {σ τ} -> (f : Term σ) -> (s : Term τ) -> Term (σ X τ)
  fst             : forall {σ τ} -> (t : Term (σ X τ)) -> Term σ
  snd             : forall {σ τ} -> (t : Term (σ X τ)) -> Term τ
    
-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  vtup : forall {σ τ} -> Value σ -> Value τ -> Value (σ X τ)



-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝
⌜ vtup x x₁ ⌝ = tuple ⌜ x ⌝ ⌜ x₁ ⌝

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
⟦ tuple x x₁ ⟧ = vtup ⟦ x ⟧ ⟦ x₁ ⟧
⟦ fst x ⟧ with ⟦ x ⟧
⟦ fst x ⟧ | vtup k k₁ = k
⟦ snd x ⟧ with ⟦ x ⟧
⟦ snd x ⟧ | vtup k k₁ = k₁


-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Tup : ∀ {σ τ} -> {x : Term σ} {y : Term τ} -> IsValue x -> IsValue y -> IsValue (tuple x y)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (vtup x x₁) = V-Tup (isValueComplete x) (isValueComplete x₁)

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Tup x₁ x₂) with isValueSound x₁ | isValueSound x₂
isValueSound (V-Tup x₁ x₂) | Witness x₃ x₄ | Witness x₅ x₆ = Witness (vtup x₃ x₅) ({!!}) 

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  E-Fst : forall {ty} {t1 t2 : Term ty} -> Step (fst (tuple t1 t2)) t1
  E-Snd : forall {ty} {t1 t2 : Term ty} -> Step (snd (tuple t1 t2)) t2

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v
valuesDoNotStep ._ y () (V-Tup t t₁)

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
toVal _ (V-Succ v) with toVal _ v
toVal _ (V-Succ v) | vnat x₁ = vnat (Succ x₁)
toVal ._ (V-Tup v v₁) with toVal _ v | toVal _ v₁
... | k | j = vtup k j

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x )
  if-reduces (fst t1) t2 t3 =  ({!!})
  if-reduces (snd t1) t2 t3 = {!!}

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces x = {!!}
  
  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values x nf = {!!}
  
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
  progress x = {!!}

--------------------------------------------------------------------------------
---------------------------       EXERCISES       ------------------------------
--------------------------------------------------------------------------------

-- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} -> {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If step₁) (E-If-If step₂) with deterministic step₁ step₂
deterministic (E-If-If step₁) (E-If-If step₂) | refl = refl 
deterministic (E-Succ step₁) (E-Succ step₂) with deterministic step₁ step₂
deterministic (E-Succ step₁) (E-Succ step₂) | refl = refl
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic (E-IsZeroSucc x) (E-IsZero (E-Succ step₂)) = contradiction (valuesDoNotStep _ _ step₂ x)
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ step₁)) (E-IsZeroSucc x) = contradiction (valuesDoNotStep _ _ step₁ x)
deterministic (E-IsZero step₁) (E-IsZero step₂) with deterministic step₁ step₂
deterministic (E-IsZero step₁) (E-IsZero step₂) | refl = refl
deterministic s1 ss2 = {!!}

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

-- Extension of the single step rule, for multiple steps.
E-If-Steps : ∀ {ty} {t₁ t₁′ : Term BOOL} {t₂ t₃ : Term ty} →
        Steps t₁ t₁′ →
        Steps (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)

E-Succ-Steps : ∀ {t₁ t₂ : Term NAT} →
        Steps t₁ t₂ →
        Steps (succ t₁) (succ t₂)
E-Succ-Steps Nil = Nil
E-Succ-Steps (Cons x steps) = Cons (E-Succ x) (E-Succ-Steps steps)

E-IsZero-Steps : ∀ {t₁ t₂ : Term NAT} →
        Steps t₁ t₂ →
        Steps (iszero t₁) (iszero t₂)
E-IsZero-Steps Nil = Nil
E-IsZero-Steps (Cons x steps) = Cons (E-IsZero x) (E-IsZero-Steps steps)

-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms :
  ∀ {ty} {t t₁ t₂ : Term ty} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms Nil Nil nf₁ nf₂ = refl
uniqueness-of-normal-forms Nil (Cons x step₂) nf₁ nf₂ = contradiction (nf₁ (Reduces x))
uniqueness-of-normal-forms (Cons x step₁) Nil nf₁ nf₂ = contradiction (nf₂ (Reduces x))
uniqueness-of-normal-forms (Cons x step₁) (Cons x₁ step₂) nf₁ nf₂ with deterministic x x₁
uniqueness-of-normal-forms (Cons x step₁) (Cons x₁ step₂) nf₁ nf₂ | refl = uniqueness-of-normal-forms step₁ step₂ nf₁ nf₂

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : forall {ty} {c : Term BOOL} {t e : Term ty} {v} -> c ⇓ vtrue -> t ⇓ v -> (if c then t else e) ⇓ v
  EvalIfFalse : forall {ty} {c : Term BOOL} {t e : Term ty} {v} -> c ⇓ vfalse -> e ⇓ v -> (if c then t else e) ⇓ v
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : forall {n v} -> n ⇓ vnat v -> succ n ⇓ vnat (Succ v)
  EvalIsZeroTrue : forall {n : Term NAT} -> n ⇓ vnat Zero -> iszero n ⇓ vtrue
  EvalIsZeroFalse : forall {n : Term NAT} {v : Nat} -> n ⇓ vnat (Succ v) -> iszero n ⇓ vfalse

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-True ] ++ big-to-small p₁
big-to-small (EvalIfFalse p p₁) = E-If-Steps (big-to-small p) ++ [ E-If-False ] ++ big-to-small p₁
big-to-small EvalZero = Nil
big-to-small (EvalSucc p) = E-Succ-Steps (big-to-small p)
big-to-small (EvalIsZeroTrue p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroFalse p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc (isValueComplete _) ]


-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = EvalTrue
value-to-value .false V-False = EvalFalse
value-to-value .zero V-Zero = EvalZero
value-to-value (succ x) (V-Succ p) with toVal x p | value-to-value x p
value-to-value (succ x) (V-Succ p) | vnat x₁ | k = EvalSucc k
value-to-value x y = {!!}

-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t .t p Nil = value-to-value t p
small-to-big t t₁ p (Cons step steps) = prepend-step step (small-to-big _ _ p steps)
  where
  prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
  prepend-step E-If-True x₁ = EvalIfTrue EvalTrue x₁
  prepend-step E-If-False x₁ = EvalIfFalse EvalFalse x₁
  prepend-step (E-If-If x) (EvalIfTrue x₁ x₂) = EvalIfTrue (prepend-step x x₁) x₂
  prepend-step (E-If-If x) (EvalIfFalse x₁ x₂) = EvalIfFalse (prepend-step x x₁) x₂
  prepend-step (E-Succ x) (EvalSucc x₁) = EvalSucc (prepend-step x x₁)
  prepend-step E-IsZeroZero EvalTrue = EvalIsZeroTrue EvalZero
  prepend-step {_} {iszero (succ t)} (E-IsZeroSucc x) EvalFalse with toVal t x | value-to-value t x
  prepend-step {.BOOL} {iszero (succ t₂)} (E-IsZeroSucc x) EvalFalse | vnat x₁ | j = EvalIsZeroFalse (EvalSucc j)
  prepend-step (E-IsZero x) (EvalIsZeroTrue x₁) = EvalIsZeroTrue (prepend-step x x₁)
  prepend-step (E-IsZero x) (EvalIsZeroFalse x₁) = EvalIsZeroFalse (prepend-step x x₁)
  prepend-step t t2 = {!!}

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | k = EvalIfTrue k (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | k = EvalIfFalse k (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | j = EvalSucc j
⇓-complete (iszero x) with ⟦ x ⟧ | ⇓-complete x
⇓-complete (iszero x) | vnat Zero | j = EvalIsZeroTrue j
⇓-complete (iszero x) | vnat (Succ x₁) | j = EvalIsZeroFalse j 
⇓-complete x = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound .true .vtrue EvalTrue = refl
⇓-sound .false .vfalse EvalFalse = refl
⇓-sound (if c then t else e) v (EvalIfTrue p p₁) with ⟦ if c then t else e ⟧ | ⇓-sound _ v p₁
⇓-sound (if c then t else e) .(⟦ t ⟧) (EvalIfTrue p p₁) | k | refl = {!!}
⇓-sound ._ v (EvalIfFalse p p₁) = {!!}
⇓-sound .zero .(vnat Zero) EvalZero = refl
⇓-sound ._ ._ (EvalSucc p) with ⇓-sound _ _ p
... | k = {!!}
⇓-sound ._ .vtrue (EvalIsZeroTrue p) = {!!}
⇓-sound ._ .vfalse (EvalIsZeroFalse p) = {!!}
