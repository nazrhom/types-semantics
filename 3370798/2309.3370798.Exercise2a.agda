
module Exercise2a where


{- Marinus Oosters - 33070798

   This is nowhere near complete.
   Part of it is because there are things I don't know,
   but part of it is because I just ran out of time.
   (And I had to redo quite a bit of it to add in tuples.)
   I'm going to send an updated version through the mail 
   in the weekend, though I won't hold it against anyone
   if that isn't accepted.
 -}
   

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
  _×_ : Type -> Type -> Type {-- Well, more like pairs; but since I only need fst and snd... --}

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Tuple
  _,_           : {tfst tsnd : Type} -> Term tfst -> Term tsnd -> Term (tfst × tsnd)
  fst           : {tfst tsnd : Type} -> Term (tfst × tsnd) -> Term tfst
  snd           : {tfst tsnd : Type} -> Term (tfst × tsnd) -> Term tsnd

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  vtuple : {tfst tsnd : Type} -> Value tfst -> Value tsnd -> Value (tfst × tsnd)


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝
⌜ vtuple tf ts ⌝ = ‌⌜ tf ⌝ , ⌜ ts ⌝

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
⟦ x , y ⟧ = vtuple ⟦ x ⟧ ⟦ y ⟧
⟦ fst tup ⟧ with ⟦ tup ⟧
⟦ fst tup ⟧ | vtuple x y = x
⟦ snd tup ⟧ with ⟦ tup ⟧
⟦ snd tup ⟧ | vtuple x y = y 



-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True  : IsValue true
  V-False : IsValue false
  V-Zero  : IsValue zero
  V-Succ  : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Tuple : {tfst tsnd : Type} {x : Term tfst} {y : Term tsnd} -> IsValue x -> IsValue y -> IsValue ( x , y )


isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (vtuple x x₁) = V-Tuple (isValueComplete x) (isValueComplete x₁)

isValueSound : ∀ {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (λ v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ x₁) with isValueSound x₁
isValueSound (V-Succ x₁) | Witness (vnat x₂) x₃ = Witness (vnat (Succ x₂)) (cong succ x₃)
isValueSound (V-Tuple x₁ x₂) with isValueSound x₁
isValueSound (V-Tuple x₁ x₂) | sound₁ with isValueSound x₂
isValueSound (V-Tuple x₄ x₂) | Witness x₅ x₆ | Witness x x₁ = {!!}


data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True    : forall {ty} {t1 t2  : Term ty} -> Step (if true  then t1 else t2) t1
  E-If-False   : forall {ty} {t1 t2  : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If      : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
                                            Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')

  E-Tuple-Fst  : forall {tyf tys} {t₁ t₁' : Term tyf} {t₂ t₂' : Term tys} -> Step t₁ t₁' -> Step (t₁ , t₂) (t₁' , t₂)
  E-Tuple-Snd  : forall {tyf tys} {t₁ t₁' : Term tyf} {t₂ t₂' : Term tys} -> Step t₂ t₂' -> Step (t₁ , t₂) (t₁ , t₂')
  E-Fst        : forall {tyf tys} {t₁ : Term tyf} {t₂ : Term tys} -> (t : Term (tyf × tys)) -> Step (fst t) t₁
  E-Snd        : forall {tyf tys} {t₁ : Term tyf} {t₂ : Term tys} -> (t : Term (tyf × tys)) -> Step (snd t) t₂



preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl


-- Note: I redid this using Agda's goal expander. It came out to be exactly the same
-- as the previous code, which did not want to compile (whines about E-Succ not being
-- of the right type). But now it works. Don't ask me.
valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true step () V-True
valuesDoNotStep .false step () V-False
valuesDoNotStep .zero step () V-Zero
valuesDoNotStep ._ ._ (E-Succ val) (V-Succ isval) = valuesDoNotStep _ _ val isval
valuesDoNotStep ._ ._ (E-Tuple-Fst r) (V-Tuple x₁ y₁) = valuesDoNotStep _ _ r x₁
valuesDoNotStep ._ ._ (E-Tuple-Snd r) (V-Tuple x₁ y₁) = valuesDoNotStep _ _ r y₁


-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

toVal : forall {ty} -> (t : Term ty) -> IsValue t -> Value ty
toVal true V-True = vtrue
toVal false V-False = vfalse
toVal zero V-Zero = vnat Zero
toVal ._ (V-Succ isval) with toVal _ isval 
toVal ._ (V-Succ isval) | vnat x = vnat (Succ x)
toVal (x , y) (V-Tuple x' y') = vtuple (toVal x x') (toVal y y')

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t1) t2 t3 = {!!}  
  if-reduces (snd t1) t2 t3 = {!!} 

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
  normal-forms-are-values (x , y) nf = {!!} 
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
  progress (x , y) = {!!}
  progress (fst x) = {!!}
  progress (snd y) = {!!}


-- equality for first and second element of tuple

fst= : {tyf tys : Type} -> {t₁ t₁' : Term tyf} {t₂ t₂' : Term tys} -> t₁ == t₁' -> (t₁ , t₂) == (t₁' , t₂)
fst= refl = refl

snd= : {tyf tys : Type} -> {t₁ t₁' : Term tyf} {t₂ t₂' : Term tys} -> t₂ == t₂' -> (t₁ , t₂) == (t₁ , t₂')
snd= refl = refl


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

deterministic (E-IsZeroSucc x) (E-IsZeroSucc x₁) = {!!} 

deterministic (E-IsZeroSucc x) (E-IsZero step₂) = {!!}
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ step₁)) (E-IsZeroSucc {val} x) = {!!}

deterministic (E-IsZero step₁) (E-IsZero step₂) with deterministic step₁ step₂
deterministic (E-IsZero step₁) (E-IsZero step₂) | refl = refl 

deterministic (E-Tuple-Fst step₁) (E-Tuple-Fst step₂) with deterministic step₁ step₂
deterministic (E-Tuple-Fst step₁) (E-Tuple-Fst step₂) | refl = refl
deterministic (E-Tuple-Fst step₁) (E-Tuple-Snd step₂) = {!!}
deterministic (E-Tuple-Snd step₁) (E-Tuple-Fst step₂) = {!!}
deterministic (E-Tuple-Snd step₁) (E-Tuple-Snd step₂) with deterministic step₁ step₂
deterministic (E-Tuple-Snd step₁) (E-Tuple-Snd step₂) | refl = refl
deterministic (E-Fst t) (E-Fst .t) = {!!}
deterministic (E-Snd t) (E-Snd .t) = {!!}




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
uniqueness-of-normal-forms (Cons x steps₁) (Cons x₁ steps₂) nf₁ nf₂ with deterministic x x₁
uniqueness-of-normal-forms (Cons x steps₁) (Cons x₁ steps₂) nf₁ nf₂ | refl = uniqueness-of-normal-forms steps₁ steps₂ nf₁ nf₂


------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
    --values
    BS-True  : true  ⇓ vtrue
    BS-False : false ⇓ vfalse
    BS-Zero  : zero  ⇓ vnat Zero
    -- "functions"
    BS-Succ       : ∀ {t n} -> t ⇓ vnat n        -> succ t ⇓ vnat (Succ n)
    BS-IsZeroZero : ∀ {t}   -> t ⇓ vnat Zero     -> iszero t ⇓ vtrue
    BS-IsZeroSucc : ∀ {t n} -> t ⇓ vnat (Succ n) -> iszero t ⇓ vfalse
    -- if/then/else
    BS-IfFalse    : ∀ {ty cond t f} {v : Value ty} -> cond ⇓ vfalse -> f ⇓ v -> (if cond then t else f) ⇓ v
    BS-IfTrue     : ∀ {ty cond t f} {v : Value ty} -> cond ⇓ vtrue  -> t ⇓ v -> (if cond then t else f) ⇓ v
    -- tuple
    BS-Tuple      : ∀ {tyf tys} {t₁ : Term tyf} {t₂ : Term tys} {v₁ : Value tyf} {v₂ : Value tys}
                        -> t₁ ⇓ v₁ -> t₂ ⇓ v₂ -> (t₁ , t₂) ⇓ vtuple v₁ v₂
    BS-Fst        : ∀ {tyf tys v₂} {t : Term (tyf × tys)} {v₁ : Value tyf}
                        -> t ⇓ vtuple v₁ v₂ -> fst t ⇓ v₁
    BS-Snd        : ∀ {tyf tys v₁} {t : Term (tyf × tys)} {v₂ : Value tys}
                        -> t ⇓ vtuple v₁ v₂ -> snd t ⇓ v₂



-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small BS-True = Nil
big-to-small BS-False = Nil
big-to-small BS-Zero = Nil
big-to-small (BS-Succ x) = {!!}
big-to-small (BS-IsZeroZero x) = {!!}
big-to-small (BS-IsZeroSucc x) = {!!}
big-to-small (BS-IfFalse x x₁) = {!!}
big-to-small (BS-IfTrue x x₁) = {!!}
big-to-small (BS-Tuple x x₁) = {!!}
big-to-small (BS-Fst x) = {!!}
big-to-small (BS-Snd x) = {!!} 



-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = BS-True
value-to-value .false V-False = BS-False
value-to-value .zero V-Zero = BS-Zero
value-to-value ._ (V-Succ p) = {!!}
value-to-value ._ (V-Tuple p p₁) = BS-Tuple (value-to-value _ p) (value-to-value _ p₁)


-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t v steps = {!!}
  where
  prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v

  prepend-step E-If-True x = BS-IfTrue BS-True x
  prepend-step E-If-False x = BS-IfFalse BS-False x
  prepend-step (E-If-If step) (BS-IfFalse x x₁) = BS-IfFalse (prepend-step step x) x₁
  prepend-step (E-If-If step) (BS-IfTrue x x₁) = BS-IfTrue (prepend-step  step x) x₁
  prepend-step (E-Succ step) (BS-Succ x) = BS-Succ (prepend-step step x)
  prepend-step E-IsZeroZero BS-True = BS-IsZeroZero BS-Zero
  prepend-step (E-IsZeroSucc x) BS-False = {! !}
  prepend-step (E-IsZero step) x = {!!}
  prepend-step (E-Tuple-Fst step) x = {!!}
  prepend-step (E-Tuple-Snd step) x = {!!}
  prepend-step (E-Fst step) x = {!!}
  prepend-step (E-Snd step) x = {!!}
  


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = BS-True
⇓-complete false = BS-False
⇓-complete (if true then t₁ else t₂) = BS-IfTrue (⇓-complete true) (⇓-complete t₁)
⇓-complete (if false then t₁ else t₂) = BS-IfFalse (⇓-complete false) (⇓-complete t₂)
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
⇓-complete (if t then t₁ else t₂) | rs with ⟦ t ⟧ 
⇓-complete (if t then t₁ else t₂) | rs | vtrue = {!!}
⇓-complete (if t then t₁ else t₂) | rs | vfalse = {!!}
⇓-complete zero = BS-Zero
⇓-complete (succ t) with ⇓-complete t
⇓-complete (succ t) | rs with ⟦ t ⟧
⇓-complete (succ t) | rs | vnat x = BS-Succ rs
⇓-complete (iszero t) with ⇓-complete t
⇓-complete (iszero t) | rs with ⟦ t ⟧
⇓-complete (iszero t) | rs | vnat Zero = BS-IsZeroZero rs
⇓-complete (iszero t) | rs | vnat (Succ x) = BS-IsZeroSucc rs
⇓-complete (x , y) = BS-Tuple (⇓-complete x) (⇓-complete y)
⇓-complete (fst t) with ⇓-complete t
⇓-complete (fst t) | rs with ⟦ t ⟧
⇓-complete (fst t) | rs | vtuple v v₁ = BS-Fst rs
⇓-complete (snd t) with ⇓-complete t
⇓-complete (snd t) | rs with ⟦ t ⟧
⇓-complete (snd t) | rs | vtuple v v₁ = BS-Snd rs


-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.

⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
-- values
⇓-sound true vtrue BS-True = refl
⇓-sound true vfalse ()
⇓-sound false vtrue ()
⇓-sound false vfalse BS-False = refl
⇓-sound zero v s = {!!}

-- if false
⇓-sound (if t then t₁ else t₂) v (BS-IfFalse p p₁) with ⇓-sound t vfalse p
⇓-sound (if t then t₁ else t₂) v (BS-IfFalse p p₁) | rs with ⟦ t ⟧
⇓-sound (if t then t₁ else t₂) v (BS-IfFalse p p₁) | rs | y with ⇓-sound t₂ v p₁
⇓-sound (if t then t₁ else t₂) .(⟦ t₂ ⟧) (BS-IfFalse p p₁) | refl | .vfalse | refl = refl

-- if true
⇓-sound (if t then t₁ else t₂) v (BS-IfTrue p p₁) with ⇓-sound t vtrue p
⇓-sound (if t then t₁ else t₂) v (BS-IfTrue p p₁) | rs with ⟦ t ⟧
⇓-sound (if t then t₁ else t₂) v (BS-IfTrue p p₁) | rs | y with ⇓-sound t₁ v p₁
⇓-sound (if t then t₁ else t₂) .(⟦ t₁ ⟧) (BS-IfTrue p p₁) | refl | .vtrue | refl = refl

-- successor
⇓-sound (succ t) ._ (BS-Succ p) with ⇓-sound t _ p
⇓-sound (succ t) ._ (BS-Succ p) | x with ⟦ t ⟧
⇓-sound (succ t) .(vnat (Succ n)) (BS-Succ p) | refl | vnat n = refl

-- iszero
⇓-sound (iszero t) vtrue (BS-IsZeroZero p) with ⇓-sound t _ p
⇓-sound (iszero t) vtrue (BS-IsZeroZero p) | x with ⟦ t ⟧
⇓-sound (iszero t) vtrue (BS-IsZeroZero p) | refl | .(vnat Zero) = refl
⇓-sound (iszero t) vfalse (BS-IsZeroSucc p) with ⇓-sound t _ p
⇓-sound (iszero t) vfalse (BS-IsZeroSucc p) | x with ⟦ t ⟧
⇓-sound (iszero t) vfalse (BS-IsZeroSucc p) | refl | ._ = refl

-- tuples
⇓-sound (t , t₁) (vtuple v v₁) (BS-Tuple s s₁) with ⇓-sound t v s
⇓-sound (t , t₁) (vtuple v v₁) (BS-Tuple s s₁) | sound₁ with ⇓-sound t₁ v₁ s₁
⇓-sound (t , t₁) (vtuple .(⟦ t ⟧) .(⟦ t₁ ⟧)) (BS-Tuple s s₁) | refl | refl = refl
⇓-sound (fst t) v (BS-Fst s) = {!!}
⇓-sound (snd t) v (BS-Snd s) = {!!}
