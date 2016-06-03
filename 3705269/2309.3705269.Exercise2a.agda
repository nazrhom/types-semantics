module Exercise2a-tuples where

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
  _,_ : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Tuples
  2tuple        : {ty ty' : Type} -> Term ty -> Term ty' -> Term (ty , ty')
  fst           : {ty ty' : Type} -> Term (ty , ty') -> Term ty
  snd           : {ty ty' : Type} -> Term (ty , ty') -> Term ty'

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  v2tuple : {ty ty' : Type} -> Value ty -> Value ty' -> Value (ty , ty')
--  vfst : {ty ty' : Type} -> Value (ty , ty') -> Value ty
--  vsnd : {ty ty' : Type} -> Value (ty , ty') -> Value ty'


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 
⌜ v2tuple ty₁ ty₂ ⌝ = 2tuple ⌜ ty₁ ⌝ ⌜ ty₂ ⌝
--⌜ vfst t ⌝ = fst ⌜ t ⌝
--⌜ vsnd t ⌝ = snd ⌜ t ⌝

------------------------------------------------------------------------
-- Denotational semantics.
--------------------------------------------------------------------------------

-- fst and snd are not really values, they lead to values. Therefore we use external functions, not part of the Value datatype
vfst : {ty ty' : Type} -> Value (ty , ty') -> Value ty
vfst (v2tuple t₁ t₂) = t₁

vsnd : {ty ty' : Type} -> Value (ty , ty') -> Value ty'
vsnd (v2tuple t₁ t₂) = t₂


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
⟦ 2tuple t₁ t₂ ⟧ = v2tuple ⟦ t₁ ⟧ ⟦ t₂ ⟧
⟦ fst t ⟧ = vfst ⟦ t ⟧
⟦ snd t ⟧ = vsnd ⟦ t ⟧



-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-2Tuple : ∀ {x y} -> IsValue x -> IsValue y -> IsValue (2tuple x y)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (v2tuple t₁ t₂) = {!!}

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-2Tuple x y) with isValueSound x | isValueSound y
isValueSound (V-2Tuple x₁ y₁) | Witness x₂ x₃ | Witness x₄ x₅ = Witness (v2tuple x₂ x₄) ({!!}) where
--  lemma : {tyx tyy : Type} {x x' : Term tyx} {y y' : Term tyy} -> 2tuple x y -> x == x' -> y == y' -> 2tuple x' y'
--  lemma = ?

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
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v
valuesDoNotStep _ t' () (V-2Tuple x₁ y₁)

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
toVal _ (V-2Tuple x₁ y₁) = v2tuple (toVal _ x₁) (toVal _ y₁)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t1) t2 t3 with {!if-reduces t1 t2 t3!}
  ... | a = {!!}
  if-reduces (snd t1) t2 t3 = {!!}

  fst-reduces : ∀ {ty₁ ty₂} (t : Term (ty₁ , ty₂)) -> Red (fst t)
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = {!!}
  fst-reduces (2tuple t t₁) = {!!}
  fst-reduces (fst t) = {!!}
  fst-reduces (snd t) = {!!}

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) = {!!}
  iszero-reduces (snd t) = {!!}

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values (2tuple t₁ t₂) nf = {!!}
  normal-forms-are-values (fst t) nf = {!!}
  normal-forms-are-values (snd t) nf = {!!}

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
  progress (2tuple t₁ t₂) = Right (Reduces {!!})
  progress (fst t) = {!!}
  progress (snd t) = {!!}

--------------------------------------------------------------------------------
---------------------------       EXERCISES       ------------------------------
--------------------------------------------------------------------------------

-- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
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
deterministic (E-IsZeroSucc step₁) (E-IsZero step₂) = {!deterministic !}
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero step₁) (E-IsZeroSucc x) = {!!}
deterministic (E-IsZero step₁) (E-IsZero step₂) with deterministic step₁ step₂
deterministic (E-IsZero step₁) (E-IsZero step₂) | refl = refl

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
  ∀ {ty} {t t₁ t₂ : Term ty} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms Nil Nil nf₁ nf₂ = refl
uniqueness-of-normal-forms Nil (Cons x steps₂) nf₁ nf₂ = contradiction (nf₁ (Reduces x))
uniqueness-of-normal-forms (Cons x steps₁) Nil nf₁ nf₂ = contradiction (nf₂ (Reduces x))
uniqueness-of-normal-forms (Cons x₁ steps₁) (Cons x₂ steps₂) nf₁ nf₂ with deterministic x₁ x₂
uniqueness-of-normal-forms (Cons x₁ steps₁) (Cons x₂ steps₂) nf₁ nf₂ | refl = uniqueness-of-normal-forms steps₁ steps₂ nf₁ nf₂

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : ∀ {c ty} {e t : Term ty} {v : Value ty}
    -> c ⇓ vtrue -> t ⇓ v -> (if c then t else e) ⇓ v

  EvalIfFalse : ∀ {c ty} {e t : Term ty} {v : Value ty}
    -> c ⇓ vfalse -> e ⇓ v -> (if c then t else e) ⇓ v

  EvalZero : zero ⇓ vnat Zero

  -- If x ⇓ vnat v, it also holds for its succesor
  EvalSucc : {x : Term NAT} {v : Nat} -> x ⇓ vnat v -> succ x ⇓ vnat (Succ v)

  -- If x leads to Zero, iszero x leads to true
  EvalIsZeroTrue : {x : Term NAT} -> x ⇓ vnat Zero -> iszero x ⇓ vtrue

  -- If x leads to a succesor, it may not be zero
  EvalIsZeroFalse : {x : Term NAT} {v : Nat} -> x ⇓ vnat (Succ v) -> iszero x ⇓ vfalse

if-small : ∀ {ty} {c c' : Term BOOL} {t e : Term ty}
  -> Steps c c'
  -> Steps (if c then t else e) (if c' then t else e)
if-small Nil = Nil
if-small (Cons c cs) = [ E-If-If c ] ++ if-small cs

succ-small : {x x' : Term NAT}
  -> Steps x x'
  -> Steps (succ x) (succ x')
succ-small Nil = Nil
succ-small (Cons p ps) = [ E-Succ p ] ++ succ-small ps

iszero-small : ∀ {x x'}
  -> Steps x x'
  -> Steps (iszero x) (iszero x')
iszero-small Nil = Nil
iszero-small (Cons p ps) = [ E-IsZero p ] ++ iszero-small ps

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue c v) = if-small (big-to-small c) ++ [ E-If-True ] ++ big-to-small v
big-to-small (EvalIfFalse c v) = if-small (big-to-small c) ++ [ E-If-False ] ++ big-to-small v
big-to-small EvalZero = Nil
big-to-small (EvalSucc p) = succ-small (big-to-small p)
big-to-small (EvalIsZeroTrue p) = iszero-small (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroFalse p) = iszero-small (big-to-small p) ++ [ E-IsZeroSucc _ ]

vsucc : Value NAT -> Value NAT
vsucc (vnat Zero) = vnat Zero
vsucc (vnat (Succ x)) = {!!}

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} {t : Term ty} -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value V-True = EvalTrue
value-to-value V-False = EvalFalse
value-to-value V-Zero = EvalZero
value-to-value (V-Succ p) = {!vsucc ?!}
value-to-value (V-2Tuple x y) = {!!}

-- And conversion in the other direction
small-to-big : {ty : Type} -> {t t' : Term ty} -> {p : IsValue t'} -> Steps t t' -> t ⇓ toVal t' p
small-to-big {_} {_} {_} {p'} Nil = value-to-value p'
small-to-big (Cons s steps) = prepend-step s (small-to-big steps)
  where
  prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} -> Step t t' -> t' ⇓ v -> t ⇓ v
  prepend-step E-If-True t'v = EvalIfTrue EvalTrue t'v
  prepend-step E-If-False t'v = EvalIfFalse EvalFalse t'v
  prepend-step (E-If-If tt') (EvalIfTrue t'v t'v₁) = EvalIfTrue (prepend-step tt' t'v) t'v₁
  prepend-step (E-If-If tt') (EvalIfFalse t'v t'v₁) = EvalIfFalse (prepend-step tt' t'v) t'v₁
  prepend-step (E-Succ tt') (EvalSucc t'v) = EvalSucc (prepend-step tt' t'v)
  prepend-step E-IsZeroZero EvalTrue = EvalIsZeroTrue EvalZero
  prepend-step (E-IsZeroSucc V-Zero) EvalFalse = EvalIsZeroFalse (EvalSucc EvalZero)
  prepend-step (E-IsZeroSucc (V-Succ x₁)) EvalFalse = EvalIsZeroFalse (EvalSucc {!!})
  prepend-step (E-IsZero tt') (EvalIsZeroTrue t'v) = EvalIsZeroTrue (prepend-step tt' t'v)
  prepend-step (E-IsZero tt') (EvalIsZeroFalse t'v) = EvalIsZeroFalse (prepend-step tt' t'v)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | x = EvalIfTrue x (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | x = EvalIfFalse x (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat _ | x₁ = EvalSucc x₁
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | x₁ = EvalIsZeroTrue x₁
⇓-complete (iszero t) | vnat (Succ x) | x₁ = EvalIsZeroFalse x₁
⇓-complete (2tuple a a₁) = {!!}
⇓-complete (fst a) = {!!}
⇓-complete (snd a) = {!!}

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → v == ⟦ t ⟧
⇓-sound EvalTrue = refl
⇓-sound EvalFalse = refl
⇓-sound (EvalIfTrue c tv) = {!!}
⇓-sound (EvalIfFalse c ev) = {!!}
⇓-sound EvalZero = {!!}
⇓-sound (EvalSucc tv) = {!!}
⇓-sound (EvalIsZeroTrue tv) = {!!}
⇓-sound (EvalIsZeroFalse tv) = {!!}

