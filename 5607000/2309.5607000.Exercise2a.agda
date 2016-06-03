
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
  PAIR : Type → Type → Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- ADDED: pairs
  pair          : ∀ {τ₁ τ₂} → (x₁ : Term τ₁) (x₂ : Term τ₂) → Term (PAIR τ₁ τ₂)
  fst           : ∀ {τ₁ τ₂} → (p : Term (PAIR τ₁ τ₂)) → Term τ₁
  snd           : ∀ {τ₁ τ₂} → (p : Term (PAIR τ₁ τ₂)) → Term τ₂

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  -- ADDED: pairs
  vpair : ∀ {τ₁ τ₂} → (x : Value τ₁) (y : Value τ₂) → Value (PAIR τ₁ τ₂)

-- ADDED: useful value definitions
vzero : Value NAT
vzero = vnat Zero

vsucc : Value NAT → Value NAT
vsucc (vnat x) = vnat (Succ x)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝
⌜ vpair x y ⌝ = pair ⌜ x ⌝ ⌜ y ⌝

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
⟦ pair x y ⟧ = vpair ⟦ x ⟧ ⟦ y ⟧
⟦ fst t ⟧ with ⟦ t ⟧
⟦ fst t ⟧ | vpair x y = x
⟦ snd t ⟧ with ⟦ t ⟧
⟦ snd t ⟧ | vpair x y = y

-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Pair : ∀ {τ₁ τ₂} {x : Term τ₁} {y : Term τ₂} → IsValue x → IsValue y → IsValue (pair x y)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (vpair x y) = V-Pair (isValueComplete x) (isValueComplete y)

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Pair x y) with isValueSound x | isValueSound y
isValueSound (V-Pair x y₁) | Witness xv refl | Witness yv refl = Witness (vpair xv yv) refl

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' ->
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  E-Fst-Beta : forall {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} → (v : IsValue (pair t1 t2)) → Step (fst (pair t1 t2)) t1
  E-Snd-Beta : forall {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} → (v : IsValue (pair t1 t2)) → Step (snd (pair t1 t2)) t2
  E-Fst-Proj : forall {ty1 ty2} {p p' : Term (PAIR ty1 ty2)} → Step p p' → Step (fst p) (fst p')
  E-Snd-Proj : forall {ty1 ty2} {p p' : Term (PAIR ty1 ty2)} → Step p p' → Step (snd p) (snd p')
  E-Fst      : forall {ty1 ty2} {t1 t1' : Term ty1} {t2 : Term ty2} → Step t1 t1' → Step (pair t1 t2) (pair t1' t2)
  E-Snd      : forall {ty1 ty2} {t1 : Term ty1} {t2 t2' : Term ty2} → (v : IsValue t1) → Step t2 t2' → Step (pair t1 t2) (pair t1 t2')

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v
valuesDoNotStep _ _ (E-Fst s) (V-Pair x y) = valuesDoNotStep _ _ s x
valuesDoNotStep _ _ (E-Snd v s) (V-Pair x y) = valuesDoNotStep _ _ s y

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
toVal _ (V-Pair x y) = vpair (toVal _ x) (toVal _ y)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst c) t e with fst-reduces c
  if-reduces (fst c) t e | Reduces x = Reduces (E-If-If x)
  if-reduces (snd c) t e with snd-reduces c
  if-reduces (snd c) t e | Reduces x = Reduces (E-If-If x)

  fst-reduces : ∀ {ty1 ty2} (p : Term (PAIR ty1 ty2)) → Red (fst p)
  fst-reduces (if c then t else e) with if-reduces c t e
  fst-reduces (if c then t else e) | Reduces x = Reduces (E-Fst-Proj x)
  fst-reduces (pair x y) with progress x | progress y
  fst-reduces (pair x y) | Left x₁ | Left x₂ = Reduces (E-Fst-Beta (V-Pair (normal-forms-are-values x x₁) (normal-forms-are-values y x₂)))
  fst-reduces (pair x y) | Left x₁ | Right (Reduces x₂) = Reduces (E-Fst-Proj (E-Snd (normal-forms-are-values _ x₁) x₂))
  fst-reduces (pair x y) | Right (Reduces x₁) | yr = Reduces (E-Fst-Proj (E-Fst x₁))
  fst-reduces (fst p) with fst-reduces p
  fst-reduces (fst p) | Reduces x = Reduces (E-Fst-Proj x)
  fst-reduces (snd p) with snd-reduces p
  fst-reduces (snd p) | Reduces x = Reduces (E-Fst-Proj x)

  snd-reduces : ∀ {ty1 ty2} (p : Term (PAIR ty1 ty2)) → Red (snd p)
  snd-reduces (if c then t else e) with if-reduces c t e
  snd-reduces (if c then t else e) | Reduces x = Reduces (E-Snd-Proj x)
  snd-reduces (pair x y) with progress x | progress y
  snd-reduces (pair x y) | Left x₁ | Left x₂ = Reduces
                                                 (E-Snd-Beta (V-Pair (normal-forms-are-values x x₁)
                                                  (normal-forms-are-values y x₂)))
  snd-reduces (pair x y) | Left x₁ | Right (Reduces x₂) = Reduces (E-Snd-Proj (E-Snd (normal-forms-are-values _ x₁) x₂))
  snd-reduces (pair x y) | Right (Reduces x₁) | yp = Reduces (E-Snd-Proj (E-Fst x₁))
  snd-reduces (fst p) with fst-reduces p
  snd-reduces (fst p) | Reduces x = Reduces (E-Snd-Proj x)
  snd-reduces (snd p) with snd-reduces p
  snd-reduces (snd p) | Reduces x = Reduces (E-Snd-Proj x)

  iszero-reduces : (t : Term NAT) -> Red (iszero t)
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) with fst-reduces t
  iszero-reduces (fst t) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (snd t) with snd-reduces t
  iszero-reduces (snd t) | Reduces x = Reduces (E-IsZero x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  pair-fst-nf : ∀ {ty1 ty2} (t1 : Term ty1) (t2 : Term ty2) → NF (pair t1 t2) → NF t1
  pair-fst-nf t1 t2 nf (Reduces x) = nf (Reduces (E-Fst x))

  pair-snd-nf : ∀ {ty1 ty2} (t1 : Term ty1) (t2 : Term ty2) → NF (pair t1 t2) → NF t2
  pair-snd-nf t1 t2 nf (Reduces x) = nf (Reduces (E-Snd (normal-forms-are-values t1 (pair-fst-nf t1 t2 nf)) x))

  pair-nf : ∀ {ty1 ty2} (t1 : Term ty1) (t2 : Term ty2) → NF t1 → NF t2 → NF (pair t1 t2)
  pair-nf t1 t2 nf1 nf2 (Reduces (E-Fst x)) = nf1 (Reduces x)
  pair-nf t1 t2 nf1 nf2 (Reduces (E-Snd v x)) = nf2 (Reduces x)

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values (pair x y) nf = V-Pair (normal-forms-are-values x (pair-fst-nf x y nf)) (normal-forms-are-values y (pair-snd-nf x y nf))
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

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
  progress (pair x y) with progress x | progress y
  progress (pair x y) | Left xnf | Left ynf = Left (pair-nf x y xnf ynf)
  progress (pair x y) | Left xnf | Right (Reduces xr) = Right (Reduces (E-Snd (normal-forms-are-values x xnf) xr))
  progress (pair x y) | Right (Reduces xv) | yr = Right (Reduces (E-Fst xv))
  progress (fst t) = Right (fst-reduces t)
  progress (snd t) = Right (snd-reduces t)

--------------------------------------------------------------------------------
---------------------------       EXERCISES       ------------------------------
--------------------------------------------------------------------------------

-- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} (t t₁ t₂ : Term ty) → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic _ t₂ .t₂ E-If-True E-If-True = refl
deterministic _ t2 _ E-If-True (E-If-If ())
deterministic _ t₂ .t₂ E-If-False E-If-False = refl
deterministic _ t3 _ E-If-False (E-If-If ())
deterministic _ _ t2 (E-If-If ()) E-If-True
deterministic _ _ t₂ (E-If-If ()) E-If-False
deterministic _ _ _ (E-If-If step₁) (E-If-If step₂) with deterministic _ _ _ step₁ step₂
deterministic _ _ _ (E-If-If step₁) (E-If-If step₂) | refl = refl
deterministic _ _ _ (E-Succ step₁) (E-Succ step₂) with deterministic _ _ _ step₁ step₂
deterministic _ _ _ (E-Succ step₁) (E-Succ step₂) | refl = refl
deterministic .(iszero zero) .true .true E-IsZeroZero E-IsZeroZero = refl
deterministic .(iszero zero) .true _ E-IsZeroZero (E-IsZero ())
deterministic _ .false .false (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic _ .false _ (E-IsZeroSucc x) (E-IsZero (E-Succ step₂)) = contradiction (valuesDoNotStep _ _ step₂ x)
deterministic .(iszero zero) _ .true (E-IsZero ()) E-IsZeroZero
deterministic _ _ .false (E-IsZero (E-Succ step₁)) (E-IsZeroSucc x) = contradiction (valuesDoNotStep _ _ step₁ x)
deterministic _ _ _ (E-IsZero step₁) (E-IsZero step₂) with deterministic _ _ _ step₁ step₂
deterministic _ _ _ (E-IsZero step₁) (E-IsZero step₂) | refl = refl
deterministic _ t2 .t2 (E-Fst-Beta _) (E-Fst-Beta _) = refl
deterministic _ t2 _ (E-Fst-Beta v) (E-Fst-Proj step2) = contradiction (valuesDoNotStep _ _ step2 v)
deterministic _ t2 .t2 (E-Snd-Beta _) (E-Snd-Beta _) = refl
deterministic _ t2 _ (E-Snd-Beta v) (E-Snd-Proj step2) = contradiction (valuesDoNotStep _ _ step2 v)
deterministic _ _ t3 (E-Fst-Proj step1) (E-Fst-Beta v) = contradiction (valuesDoNotStep _ _ step1 v)
deterministic _ _ _ (E-Fst-Proj step1) (E-Fst-Proj step2) with deterministic _ _ _ step1 step2
deterministic _ _ _ (E-Fst-Proj step1) (E-Fst-Proj step2) | refl = refl
deterministic _ _ t3 (E-Snd-Proj step1) (E-Snd-Beta v) = contradiction (valuesDoNotStep _ _ step1 v)
deterministic _ _ _ (E-Snd-Proj step1) (E-Snd-Proj step2) with deterministic _ _ _ step1 step2
deterministic _ _ _ (E-Snd-Proj step1) (E-Snd-Proj step2) | refl = refl
deterministic _ _ _ (E-Fst step1) (E-Fst step2) with deterministic _ _ _ step1 step2
deterministic _ _ _ (E-Fst step1) (E-Fst step2) | refl = refl
deterministic _ _ _ (E-Fst step1) (E-Snd v step2) = contradiction (valuesDoNotStep _ _ step1 v)
deterministic _ _ _ (E-Snd v step1) (E-Fst step2) = contradiction (valuesDoNotStep _ _ step2 v)
deterministic _ _ _ (E-Snd v1 step1) (E-Snd v2 step2) with deterministic _ _ _ step1 step2
deterministic _ _ _ (E-Snd v1 step1) (E-Snd v2 step2) | refl = refl

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

-- ADDED: Wrapping steps into a context
wrap-steps : ∀ {ty ty'} {t t' : Term ty} → {c : Term ty → Term ty'} → (f : ∀ {t t'} → Step t t' → Step (c t) (c t')) → Steps t t' → Steps (c t) (c t')
wrap-steps f Nil = Nil
wrap-steps f (Cons x xs) = Cons (f x) (wrap-steps f xs)

-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms :
  ∀ {ty} (t t₁ t₂ : Term ty) →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms t₁ .t₁ .t₁ Nil Nil x x₁ = refl
uniqueness-of-normal-forms t₁ .t₁ t₂ Nil (Cons x step₂) x₁ x₂ = contradiction (valuesDoNotStep _ _ x (normal-forms-are-values _ x₁))
uniqueness-of-normal-forms t₂ t₁ .t₂ (Cons x step₁) Nil x₁ x₂ = contradiction (valuesDoNotStep _ _ x (normal-forms-are-values _ x₂))
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) x₂ x₃ with deterministic _ _ _ x x₁
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons x₁ step₂) x₂ x₃ | refl = uniqueness-of-normal-forms _ _ _ step₁ step₂ x₂ x₃

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue : true ⇓ vtrue
  EvalFalse : false ⇓ vfalse
  EvalIfTrue : ∀ {ty} {c : Term BOOL} {t e : Term ty} {v : Value ty} → c ⇓ vtrue → t ⇓ v → (if c then t else e) ⇓ v
  EvalIfFalse : ∀ {ty} {c : Term BOOL} {t e : Term ty} {v : Value ty} → c ⇓ vfalse → e ⇓ v → (if c then t else e) ⇓ v
  EvalZero : zero ⇓ vnat Zero
  EvalSucc : {t : Term NAT} {n : Nat} → t ⇓ vnat n → succ t ⇓ vnat (Succ n)
  EvalIsZeroZero : {t : Term NAT} → t ⇓ vnat Zero → iszero t ⇓ vtrue
  EvalIsZeroSucc : {t : Term NAT} {n : Nat} → t ⇓ vnat (Succ n) → iszero t ⇓ vfalse
  EvalPair : ∀ {ty1 ty2} {t1 : Term ty1} {t2 : Term ty2} {v1 : Value ty1} {v2 : Value ty2} → t1 ⇓ v1 → t2 ⇓ v2 → (pair t1 t2) ⇓ (vpair v1 v2)
  EvalFst : ∀ {ty1 ty2} {p : Term (PAIR ty1 ty2)} {v1 : Value ty1} {v2 : Value ty2} → p ⇓ (vpair v1 v2) → (fst p) ⇓ v1
  EvalSnd : ∀ {ty1 ty2} {p : Term (PAIR ty1 ty2)} {v1 : Value ty1} {v2 : Value ty2} → p ⇓ (vpair v1 v2) → (snd p) ⇓ v2

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue c t) = (wrap-steps E-If-If (big-to-small c)) ++ [ E-If-True ] ++ big-to-small t
big-to-small (EvalIfFalse c e) = (wrap-steps E-If-If (big-to-small c)) ++ [ E-If-False ] ++ big-to-small e
big-to-small EvalZero = Nil
big-to-small (EvalSucc p) = wrap-steps E-Succ (big-to-small p)
big-to-small (EvalIsZeroZero p) = (wrap-steps E-IsZero (big-to-small p)) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroSucc p) =  (wrap-steps E-IsZero (big-to-small p)) ++ [ E-IsZeroSucc (isValueComplete (vnat _)) ]
big-to-small (EvalPair px py) = wrap-steps E-Fst (big-to-small px) ++ wrap-steps (E-Snd (isValueComplete _)) (big-to-small py)
big-to-small (EvalFst p) = wrap-steps E-Fst-Proj (big-to-small p) ++ [ E-Fst-Beta (isValueComplete _) ]
big-to-small (EvalSnd p) = wrap-steps E-Snd-Proj (big-to-small p) ++ [ E-Snd-Beta (isValueComplete _) ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = EvalTrue
value-to-value .false V-False = EvalFalse
value-to-value .zero V-Zero = EvalZero
value-to-value _ (V-Succ p) with toVal _ p | value-to-value _ p
value-to-value _ (V-Succ p) | vnat x₁ | b = EvalSucc b
value-to-value _ (V-Pair x y) = EvalPair (value-to-value _ x) (value-to-value _ y)

-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') → Steps t t' → t ⇓ toVal t' p
small-to-big t' .t' p Nil = value-to-value t' p
small-to-big t t' p (Cons x steps) = prepend-step t _ (toVal t' p) x (small-to-big _ t' p steps)
  where
  prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
  prepend-step _ t' v E-If-True p₁ = EvalIfTrue EvalTrue p₁
  prepend-step _ t' v E-If-False p₁ = EvalIfFalse EvalFalse p₁
  prepend-step _ _ v (E-If-If s) (EvalIfTrue p₁ p₂) = EvalIfTrue (prepend-step _ _ vtrue s p₁) p₂
  prepend-step _ _ v (E-If-If s) (EvalIfFalse p₁ p₂) = EvalIfFalse (prepend-step _ _ vfalse s p₁) p₂
  prepend-step _ _ _ (E-Succ s) (EvalSucc p₁) = EvalSucc (prepend-step _ _ _ s p₁)
  prepend-step .(iszero zero) .true .vtrue E-IsZeroZero EvalTrue = EvalIsZeroZero EvalZero
  prepend-step _ .false .vfalse (E-IsZeroSucc tval) EvalFalse with toVal _ tval | value-to-value _ tval
  prepend-step _ .false .vfalse (E-IsZeroSucc tval) EvalFalse | vnat n | b = EvalIsZeroSucc (EvalSucc b)
  prepend-step _ _ .vtrue (E-IsZero s) (EvalIsZeroZero p₁) = EvalIsZeroZero (prepend-step _ _ _ s p₁)
  prepend-step _ _ .vfalse (E-IsZero s) (EvalIsZeroSucc p₁) = EvalIsZeroSucc (prepend-step _ _ _ s p₁)
  prepend-step _ t' v (E-Fst-Beta (V-Pair v₁ v₂)) p₁ = EvalFst (EvalPair p₁ (value-to-value _ v₂))
  prepend-step _ t' v (E-Snd-Beta (V-Pair v₁ v₂)) p₁ = EvalSnd (EvalPair (value-to-value _ v₁) p₁)
  prepend-step _ _ v (E-Fst-Proj s) (EvalFst p₂) = EvalFst (prepend-step _ _ _ s p₂)
  prepend-step _ _ v (E-Snd-Proj s) (EvalSnd p₂) = EvalSnd (prepend-step _ _ _ s p₂)
  prepend-step _ _ _ (E-Fst s) (EvalPair p₁ p₂) = EvalPair (prepend-step _ _ _ s p₁) p₂
  prepend-step _ _ _ (E-Snd v₁ s) (EvalPair p₁ p₂) = EvalPair p₁ (prepend-step _ _ _ s p₂)


--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if c then t else e) with ⟦ c ⟧ | ⇓-complete c
⇓-complete (if c then t else e) | vtrue | cond = EvalIfTrue cond (⇓-complete t)
⇓-complete (if c then t else e) | vfalse | cond = EvalIfFalse cond (⇓-complete e)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | b = EvalSucc b
⇓-complete (iszero t)  with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | b = EvalIsZeroZero b
⇓-complete (iszero t) | vnat (Succ x) | b = EvalIsZeroSucc b
⇓-complete (pair x y) = EvalPair (⇓-complete x) (⇓-complete y)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | vpair dx dy | tc = EvalFst tc
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | vpair dx dy | tc = EvalSnd tc

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound .true .vtrue EvalTrue = refl
⇓-sound .false .vfalse EvalFalse = refl
⇓-sound _ v (EvalIfTrue {_} {tc} c t) with ⟦ tc ⟧ | ⇓-sound _ _ c
⇓-sound _ v (EvalIfTrue c t) | .vtrue | refl = ⇓-sound _ v t
⇓-sound _ v (EvalIfFalse {_} {tc} c e) with ⟦ tc ⟧ | ⇓-sound _ _ c
⇓-sound _ v (EvalIfFalse c e) | .vfalse | refl = ⇓-sound _ _ e
⇓-sound .zero .(vnat Zero) EvalZero = refl
⇓-sound _ _ (EvalSucc {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound _ _ (EvalSucc p) | vnat x | b = cong vsucc b
⇓-sound _ .vtrue (EvalIsZeroZero {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound _ .vtrue (EvalIsZeroZero p) | vnat .Zero | refl = refl
⇓-sound _ .vfalse (EvalIsZeroSucc {t} p) with ⟦ t ⟧ | ⇓-sound _ _ p
⇓-sound _ .vfalse (EvalIsZeroSucc p) | vnat _ | refl = refl
⇓-sound _ _ (EvalPair xp yp) with ⇓-sound _ _ xp | ⇓-sound _ _ yp
⇓-sound _ _ (EvalPair xp yp) | refl | refl = refl
⇓-sound _ v (EvalFst {_} {_} {pt} p) with ⟦ pt ⟧ | ⇓-sound _ _ p
⇓-sound _ v (EvalFst p₁) | _ | refl = refl
⇓-sound _ v (EvalSnd {_} {_} {pt} p) with ⟦ pt ⟧ | ⇓-sound _ _ p
⇓-sound _ v (EvalSnd p₁) | _ | refl = refl
