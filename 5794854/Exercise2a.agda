
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
  NAT  : Type
  BOOL : Type
  -- Tuple
  _×_  : Type -> Type -> Type

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
  ⟨_,_⟩         : ∀ {σ τ} (t : Term σ) -> (s : Term τ) -> Term (σ × τ)
  fst           : ∀ {σ τ} (t : Term (σ × τ)) -> Term σ
  snd           : ∀ {σ τ} (t : Term (σ × τ)) -> Term τ

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue  : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat   : Nat -> Value NAT
  -- Tuple
  ⟪_,_⟫  : ∀ {σ τ} -> Value σ -> Value τ -> Value (σ × τ)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 
⌜ ( ⟪ t , s ⟫ ) ⌝ = ⟨ ⌜ t ⌝ , ⌜ s ⌝ ⟩

-- ------------------------------------------------------------------------
-- -- Denotational semantics.
-- --------------------------------------------------------------------------------


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
⟦ ⟨ t , s ⟩ ⟧ = ⟪ ⟦ t ⟧ , ⟦ s ⟧ ⟫
⟦ fst t ⟧ with ⟦ t ⟧
⟦ fst t ⟧ | ⟪ f , s ⟫ = f
⟦ snd t ⟧ with ⟦ t ⟧
⟦ snd t ⟧ | ⟪ f , s ⟫ = s



-- -------------------------------------------------------------------------------
-- -- Small-step semantics.
-- -- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True  : IsValue true
  V-False : IsValue false
  V-Zero  : IsValue zero
  V-Succ  : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Tuple : ∀ {σ τ} {x : Term σ} {y : Term τ} -> IsValue x -> IsValue y -> IsValue ⟨ x , y ⟩

v-tupleleft : ∀ {σ τ} {x : Term σ} {y : Term τ} -> IsValue ⟨ x , y ⟩ -> IsValue x
v-tupleleft (V-Tuple v _) = v

v-tupleright : ∀ {σ τ} {x : Term σ} {y : Term τ} -> IsValue ⟨ x , y ⟩ -> IsValue y
v-tupleright (V-Tuple _ v) = v

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete ⟪ f , s ⟫ = V-Tuple (isValueComplete f) (isValueComplete s)

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Tuple x y) with isValueSound x | isValueSound y
isValueSound (V-Tuple x₁ y₁) | Witness x eqx | Witness y eqy = Witness ⟪ x , y ⟫ (aux eqx eqy)
  where aux : ∀ {x y x' y'} -> ⌜ x ⌝ == x' -> ⌜ y ⌝ == y' -> ⟨ ⌜ x ⌝ , ⌜ y ⌝ ⟩ == ⟨ x' , y' ⟩
        aux refl refl = refl

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  -- Tuple
  E-TupleFst   : ∀ {σ τ} {t : Term σ} {s : Term τ} -> IsValue ⟨ t , s ⟩ -> Step (fst ⟨ t , s ⟩) t
  E-TupleSnd   : ∀ {σ τ} {t : Term σ} {s : Term τ} -> IsValue ⟨ t , s ⟩ -> Step (snd ⟨ t , s ⟩) s

  E-TupleLeft  : ∀ {σ τ} {t t' : Term σ } {s : Term τ} -> Step t t' -> Step ⟨ t , s ⟩ ⟨ t' , s ⟩
  E-TupleRight : ∀ {σ τ} {t : Term σ } {s s' : Term τ} -> IsValue t -> Step s s' -> Step ⟨ t , s ⟩ ⟨ t , s' ⟩

  E-Fst        : ∀ {σ τ} {t t' : Term (σ × τ)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd        : ∀ {σ τ} {t t' : Term (σ × τ)} -> Step t t' -> Step (snd t) (snd t')

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v
valuesDoNotStep _ _ (E-TupleLeft step) (V-Tuple x₁ y₁) = valuesDoNotStep _ _ step x₁
valuesDoNotStep _ _ (E-TupleRight x step) (V-Tuple x₁ y₁) = valuesDoNotStep _ _ step y₁

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
toVal _ (V-Tuple x y) = ⟪ (toVal _ x) , (toVal _ y) ⟫

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t) t2 t3 with fst-reduces t
  if-reduces (fst t) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t) t2 t3 with snd-reduces t
  if-reduces (snd t) t2 t3 | Reduces x = Reduces (E-If-If x)

  snd-reduces : ∀ {σ τ} (t : Term (σ × τ)) -> Red (snd t)
  snd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  snd-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Snd x)
  snd-reduces ⟨ t , s ⟩ with progress t
  snd-reduces ⟨ t , s ⟩ | Left x with progress s
  snd-reduces ⟨ t , s ⟩ | Left nft | Left nfs = Reduces (E-TupleSnd (V-Tuple (normal-forms-are-values t nft) (normal-forms-are-values s nfs))) 
  snd-reduces ⟨ t , s ⟩ | Left nft | Right (Reduces rs) = Reduces (E-Snd (E-TupleRight (normal-forms-are-values t nft) rs))
  snd-reduces ⟨ t , s ⟩ | Right (Reduces rs) = Reduces (E-Snd (E-TupleLeft rs))
  snd-reduces (fst t) with fst-reduces t
  snd-reduces (fst t) | Reduces x = Reduces (E-Snd x)
  snd-reduces (snd t) with snd-reduces t
  snd-reduces (snd t) | Reduces x = Reduces (E-Snd x)

  fst-reduces : ∀ {σ τ} (t : Term (σ × τ)) -> Red (fst t)
  fst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  fst-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-Fst x)
  fst-reduces ⟨ t , s ⟩ with progress t
  fst-reduces ⟨ t , s ⟩ | Left x with progress s
  fst-reduces ⟨ t , s ⟩ | Left nft | Left nfs = Reduces (E-TupleFst (V-Tuple (normal-forms-are-values t nft) (normal-forms-are-values s nfs)))
  fst-reduces ⟨ t , s ⟩ | Left nft | Right (Reduces rs) = Reduces (E-Fst (E-TupleRight (normal-forms-are-values t nft) rs))
  fst-reduces ⟨ t , s ⟩ | Right (Reduces x) = Reduces (E-Fst (E-TupleLeft x))
  fst-reduces (fst t) with fst-reduces t
  fst-reduces (fst t) | Reduces x = Reduces (E-Fst x)
  fst-reduces (snd t) with snd-reduces t
  fst-reduces (snd t) | Reduces x = Reduces (E-Fst x)

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

  tuple-nf-left  : ∀ {σ τ} -> (t : Term σ) -> (s : Term τ) -> NF (⟨ t , s ⟩) -> NF t
  tuple-nf-left t s nf (Reduces x) = nf (Reduces (E-TupleLeft x))

  tuple-nf-right : ∀ {σ τ} -> (t : Term σ) -> (s : Term τ) -> NF (⟨ t , s ⟩) -> NF s
  tuple-nf-right t s nf (Reduces x) = nf (Reduces (E-TupleRight (normal-forms-are-values t (tuple-nf-left t s nf)) x))

  nf-tuple : ∀ {σ τ} -> (t : Term σ) -> (s : Term τ) -> NF t -> NF s -> NF (⟨ t , s ⟩)
  nf-tuple t s nft nfs (Reduces (E-TupleLeft x)) = contradiction (nft (Reduces x))
  nf-tuple t s nft nfs (Reduces (E-TupleRight x x₁)) = contradiction (nfs (Reduces x₁))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values (⟨ t , s ⟩) nf = V-Tuple (normal-forms-are-values t (tuple-nf-left t s nf))
                                                   (normal-forms-are-values s (tuple-nf-right t s nf))
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

  values-are-normal-forms : forall {ty} -> {t : Term ty} -> IsValue t -> NF t
  values-are-normal-forms p (Reduces step) = valuesDoNotStep _ _ step p

  -- previously this was lemma
  nf-succ : (k : Term NAT) -> NF k -> NF (succ k)
  nf-succ t nf (Reduces (E-Succ x)) = nf (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms V-True)
  progress false = Left (values-are-normal-forms V-False)
  progress (if t then t₁ else t₂) = Right (if-reduces _ _ _)
  progress zero = Left (values-are-normal-forms V-Zero)
  progress (succ t) with progress t
  progress (succ t) | Left x = Left (nf-succ t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) = Right (iszero-reduces _ )
  progress ⟨ t , s ⟩ with progress t | progress s
  progress ⟨ t , s ⟩ | Left nft | Left nfs  = Left (values-are-normal-forms (V-Tuple (normal-forms-are-values t nft) (normal-forms-are-values s nfs)))
  progress ⟨ t , s ⟩ | Left nf  | Right (Reduces x) = Right (Reduces (E-TupleRight (normal-forms-are-values t nf) x))
  progress ⟨ t , s ⟩ | Right (Reduces x) | _ = Right (Reduces (E-TupleLeft x))
  progress (fst t) = Right (fst-reduces t)
  progress (snd t) = Right (snd-reduces t)

-- --------------------------------------------------------------------------------
-- ---------------------------       EXERCISES       ------------------------------
-- --------------------------------------------------------------------------------

-- -- Prove that the small step semantics is deterministic
deterministic : ∀ {ty} {t t₁ t₂ : Term ty} → Step t t₁ → Step t t₂ → t₁ == t₂
deterministic E-If-True E-If-True = refl
deterministic E-If-True (E-If-If ())
deterministic E-If-False E-If-False = refl
deterministic E-If-False (E-If-If ())
deterministic (E-If-If ()) E-If-True
deterministic (E-If-If ()) E-If-False
deterministic (E-If-If step1) (E-If-If step2) with deterministic step1 step2
deterministic (E-If-If step1) (E-If-If step2) | refl = refl
deterministic (E-Succ step1) (E-Succ step2) with deterministic step1 step2
deterministic (E-Succ step1) (E-Succ step2) | refl = refl
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic (E-IsZeroSucc x) (E-IsZeroSucc x₁) = refl
deterministic (E-IsZeroSucc x) (E-IsZero step2) = contradiction (nf-succ _ (values-are-normal-forms x) (Reduces step2))
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero step1) (E-IsZeroSucc x) = contradiction (nf-succ _ (values-are-normal-forms x) (Reduces step1))
deterministic (E-IsZero step1) (E-IsZero step2) with deterministic step1 step2
deterministic (E-IsZero step1) (E-IsZero step2) | refl = refl
deterministic (E-TupleFst x ) (E-TupleFst x₂ ) = refl
deterministic (E-TupleFst vt) (E-Fst step2) = contradiction (values-are-normal-forms vt (Reduces step2))
deterministic (E-TupleSnd x ) (E-TupleSnd x₂ ) = refl
deterministic (E-TupleSnd vt) (E-Snd step2) = contradiction (values-are-normal-forms vt (Reduces step2)) 
deterministic (E-TupleLeft step1) (E-TupleLeft step2) with deterministic step1 step2
deterministic (E-TupleLeft step1) (E-TupleLeft step2) | refl = refl
deterministic (E-TupleLeft step1) (E-TupleRight x step2) = contradiction (values-are-normal-forms x (Reduces step1))
deterministic (E-TupleRight x step1) (E-TupleLeft step2) = contradiction (values-are-normal-forms x (Reduces step2))
deterministic (E-TupleRight x step1) (E-TupleRight x₁ step2) with deterministic step1 step2
deterministic (E-TupleRight x step1) (E-TupleRight x₁ step2) | refl = refl
deterministic (E-Fst step1) (E-TupleFst vs) = contradiction (values-are-normal-forms vs (Reduces step1))
deterministic (E-Fst step1) (E-Fst step2) with deterministic step1 step2
deterministic (E-Fst step1) (E-Fst step2) | refl = refl
deterministic (E-Snd step1) (E-TupleSnd vt) = contradiction (values-are-normal-forms vt (Reduces step1)) 
deterministic (E-Snd step1) (E-Snd step2) with deterministic step1 step2
deterministic (E-Snd step1) (E-Snd step2) | refl = refl

-- (1/2) * 18 / 18 points

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
uniqueness-of-normal-forms t₁ .t₁ .t₁ Nil Nil x x₁ = refl
uniqueness-of-normal-forms t₁ .t₁ t₂ Nil (Cons x step₂) nf1 nf2 = contradiction (nf1 (Reduces x))
uniqueness-of-normal-forms t₂ t₁ .t₂ (Cons x step₁) Nil nf1 nf2 = contradiction (nf2 (Reduces x))
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons y step₂) nft1 nft2 with deterministic x y
uniqueness-of-normal-forms t t₁ t₂ (Cons x step₁) (Cons y step₂) nft1 nft2 | refl = uniqueness-of-normal-forms _ t₁ t₂ step₁ step₂ nft1 nft2

-- (1/2) * 4 / 4 points

-- ------------------------------------------------------------------------
-- -- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  EvalTrue    : true ⇓ vtrue
  EvalFalse   : false ⇓ vfalse
  EvalIfTrue  : ∀ {σ} {c : Term BOOL} {t e : Term σ} {v : Value σ} -> c ⇓ vtrue  -> t ⇓ v -> (if c then t else e) ⇓ v
  EvalIfFalse : ∀ {σ} {c : Term BOOL} {t e : Term σ} {v : Value σ} -> c ⇓ vfalse -> e ⇓ v -> (if c then t else e) ⇓ v
  -- Natural numbers
  EvalZero  : zero ⇓ vnat Zero
  EvalSucc  : ∀ {t : Term NAT} {n}       -> t ⇓ (vnat n) -> succ t ⇓ vnat (Succ n)
  EvalIsZeroTrue  : ∀ {t : Term NAT}     -> t ⇓ (vnat Zero)     -> iszero t ⇓ vtrue
  EvalIsZeroFalse : ∀ {t : Term NAT} {n} -> t ⇓ (vnat (Succ n)) -> iszero t ⇓ vfalse
  -- Tuples
  -- EvalFst   : ∀ {σ τ} {t : Term σ} {v : Value σ} {s : Term τ} -> t ⇓ v -> fst ⟨ t , s ⟩ ⇓ v
  -- EvalSnd   : ∀ {σ τ} {t : Term σ} {v : Value σ} {s : Term τ} -> s ⇓ v -> snd ⟨ t , s ⟩ ⇓ v
  EvalFst   : ∀ {σ τ} {t : Term (σ × τ)} {l : Value σ} {r : Value τ} -> t ⇓ ⟪ l , r ⟫ -> fst t ⇓ l
  EvalSnd   : ∀ {σ τ} {t : Term (σ × τ)} {l : Value σ} {r : Value τ} -> t ⇓ ⟪ l , r ⟫ -> snd t ⇓ r
  EvalTuple : ∀ {σ τ} {t : Term σ} {s : Term τ} {v : Value σ} {w : Value τ } -> t ⇓ v -> s ⇓ w -> ⟨ t , s ⟩ ⇓ ⟪ v , w ⟫

-- 1 * 8 / 8 points

-- An extension of the E-If rule, for multiple steps.
E-If-Steps : ∀ {σ} {t₁ t₁′ : Term BOOL}{ t₂ t₃ : Term σ} ->
        Steps t₁ t₁′ ->
        Steps (if t₁ then t₂ else t₃) (if t₁′ then t₂ else t₃)
E-If-Steps Nil = Nil
E-If-Steps (Cons x steps) = Cons (E-If-If x) (E-If-Steps steps)


E-Succ-Steps : ∀ {t₁ t₁′ : Term NAT} ->
              Steps t₁ t₁′ ->
              Steps (succ t₁) (succ t₁′)
E-Succ-Steps Nil = Nil
E-Succ-Steps (Cons x s) = Cons (E-Succ x) (E-Succ-Steps s)


E-IsZero-Steps : ∀ {t₁ t₁′ : Term NAT} ->
                 Steps t₁ t₁′ ->
                 Steps (iszero t₁) (iszero t₁′)
E-IsZero-Steps Nil = Nil
E-IsZero-Steps (Cons x s) = Cons (E-IsZero x) (E-IsZero-Steps s)

E-TupleFst-Steps : ∀ {σ τ} {t₁ t₁′ : Term σ} {s : Term τ}->
                   Steps t₁ t₁′ ->
                   Steps ⟨ t₁ , s ⟩ ⟨ t₁′ , s ⟩
E-TupleFst-Steps Nil = Nil
E-TupleFst-Steps (Cons x s₁) = Cons (E-TupleLeft x) (E-TupleFst-Steps s₁)

E-TupleSnd-Steps : ∀ {σ τ} {s s' : Term σ} {t : Term τ}->
                   IsValue t ->
                   Steps s s' ->
                   Steps ⟨ t , s ⟩ ⟨ t , s' ⟩
E-TupleSnd-Steps vt Nil = Nil
E-TupleSnd-Steps vt (Cons x s₁) = Cons (E-TupleRight vt x) (E-TupleSnd-Steps vt s₁)

E-FstTuple-Steps : ∀ {σ τ} {t t' : Term (τ × σ)}->
                   Steps t t' ->
                   Steps (fst t) (fst t')
E-FstTuple-Steps Nil = Nil
E-FstTuple-Steps (Cons x xs) = Cons (E-Fst x) (E-FstTuple-Steps xs)

E-SndTuple-Steps : ∀ {σ τ} {s s'  : Term (τ × σ)} ->
                   Steps s s' ->
                   Steps (snd s) (snd  s' )
E-SndTuple-Steps  Nil = Nil
E-SndTuple-Steps  (Cons x s) = Cons (E-Snd x) (E-SndTuple-Steps s)

allNatValue : ∀ n -> IsValue ⌜ vnat n ⌝
allNatValue Zero = V-Zero
allNatValue (Succ n) = V-Succ (allNatValue n)

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small EvalTrue = Nil
big-to-small EvalFalse = Nil
big-to-small (EvalIfTrue p p₁) = (E-If-Steps (big-to-small p)) ++ Cons E-If-True (big-to-small p₁)
big-to-small (EvalIfFalse p p₁) = (E-If-Steps (big-to-small p)) ++ (Cons E-If-False (big-to-small p₁))
big-to-small EvalZero = Nil
big-to-small (EvalSucc p) = E-Succ-Steps (big-to-small p)
big-to-small (EvalIsZeroTrue p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroZero ]
big-to-small (EvalIsZeroFalse p) = E-IsZero-Steps (big-to-small p) ++ [ E-IsZeroSucc (allNatValue _) ]
big-to-small (EvalFst p) = (E-FstTuple-Steps (big-to-small p)) ++ [ E-TupleFst (V-Tuple (isValueComplete _) (isValueComplete _))]
big-to-small (EvalSnd p) = (E-SndTuple-Steps ((big-to-small p))) ++ [ E-TupleSnd (V-Tuple (isValueComplete _) (isValueComplete _))]
big-to-small (EvalTuple p r) = (E-TupleFst-Steps (big-to-small p)) ++ E-TupleSnd-Steps (isValueComplete _) (big-to-small r)

-- 1 * 7 / 8 points

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = EvalTrue
value-to-value .false V-False = EvalFalse
value-to-value .zero V-Zero = EvalZero
value-to-value _ (V-Succ p) with toVal _ p  | value-to-value _ p
value-to-value _ (V-Succ p) | vnat n | vp = EvalSucc  vp
value-to-value _ (V-Tuple t s) = EvalTuple (value-to-value _ t) (value-to-value _ s)

-- ? * 3 / 4 points. Not specified in email

value-lemma : ∀ {σ} (v : Value σ) -> ⌜ v ⌝ ⇓ v
value-lemma vtrue = EvalTrue
value-lemma vfalse = EvalFalse
value-lemma (vnat Zero) = EvalZero
value-lemma (vnat (Succ x)) = EvalSucc (value-lemma (vnat x))
value-lemma ⟪ v , v₁ ⟫ = EvalTuple (value-lemma v) (value-lemma v₁)

nat-lemma : ∀ n -> succ ⌜ vnat n ⌝ ⇓ vnat (Succ n)
nat-lemma Zero = EvalSucc EvalZero
nat-lemma (Succ n) = EvalSucc (nat-lemma n)

-- And conversion in the other direction
small-to-big : {ty : Type} -> (t t' : Term ty) -> (p : IsValue t') -> Steps t t' -> t ⇓ toVal t' p
small-to-big t' .t' p Nil = value-to-value t' p
small-to-big t t' p (Cons x steps) = prepend-step t _ (toVal t' p) x (small-to-big _ _ p steps)
  where
    prepend-step : {ty : Type} -> (t t' : Term ty) (v : Value ty) → Step t t' -> t' ⇓ v → t ⇓ v
    prepend-step _ t' v E-If-True d = EvalIfTrue EvalTrue d
    prepend-step _ t' v E-If-False d = EvalIfFalse EvalFalse d
    prepend-step _ _ v (E-If-If step) (EvalIfTrue d d₁) = EvalIfTrue (prepend-step _ _ vtrue step d) d₁
    prepend-step _ _ v (E-If-If step) (EvalIfFalse d d₁) = EvalIfFalse (prepend-step _ _ vfalse step d) d₁
    prepend-step _ _ _ (E-Succ step) (EvalSucc d) = EvalSucc (prepend-step _ _ (vnat _) step d)
    prepend-step .(iszero zero) .true .vtrue E-IsZeroZero EvalTrue = EvalIsZeroTrue EvalZero
    prepend-step _ .false .vfalse (E-IsZeroSucc x₁) EvalFalse with isValueSound x₁
    prepend-step .(iszero (succ ⌜ vnat x₁ ⌝)) .false .vfalse (E-IsZeroSucc x₂) EvalFalse | Witness (vnat x₁) refl = EvalIsZeroFalse (nat-lemma x₁)
    prepend-step _ _ .vtrue (E-IsZero step) (EvalIsZeroTrue d) = EvalIsZeroTrue (prepend-step _ _ (vnat Zero) step d)
    prepend-step _ _ .vfalse (E-IsZero step) (EvalIsZeroFalse d) = EvalIsZeroFalse (prepend-step _ _ (vnat (Succ _)) step d)
    prepend-step _ t' v (E-TupleFst (V-Tuple x₁ x₂)) d with isValueSound x₁ | isValueSound x₂
    prepend-step .(fst ⟨ ⌜ x₂ ⌝ , ⌜ x₃ ⌝ ⟩) .(⌜ x₂ ⌝) v (E-TupleFst (V-Tuple x₁ x₄)) d | Witness x₂ refl | Witness x₃ refl =
      EvalFst (EvalTuple d (value-lemma x₃))
    prepend-step _ t' v (E-TupleSnd (V-Tuple x₁ x₂)) d with isValueSound x₁ | isValueSound x₂
    prepend-step .(snd ⟨ ⌜ x₃ ⌝ , ⌜ x₄ ⌝ ⟩) .(⌜ x₄ ⌝) v (E-TupleSnd (V-Tuple x₁ x₂)) d | Witness x₃ refl | Witness x₄ refl =
      EvalSnd (EvalTuple (value-lemma x₃) d)
    prepend-step _ _ _ (E-TupleLeft step) (EvalTuple d d₁) = EvalTuple (prepend-step _ _ _ step d) d₁
    prepend-step _ _ _ (E-TupleRight x₁ step) (EvalTuple d d₁) = EvalTuple d (prepend-step _ _ _ step d₁)
    prepend-step _ _ v (E-Fst step) (EvalFst d) = EvalFst (prepend-step _ _ ⟪ v , _ ⟫ step d)
    prepend-step _ _ v (E-Snd step) (EvalSnd d) = EvalSnd (prepend-step _ _ ⟪ _ , v ⟫ step d)

-- 1 * 17 / 17 points

-- --------------------------------------------------------------------------------
-- -- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = EvalTrue
⇓-complete false = EvalFalse
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue  | ct = EvalIfTrue ct (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | ct = EvalIfFalse ct (⇓-complete t₂)
⇓-complete zero = EvalZero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | ct = EvalSucc ct
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | ct     = EvalIsZeroTrue ct
⇓-complete (iszero t) | vnat (Succ x) | ct = EvalIsZeroFalse ct
⇓-complete ⟨ l , r ⟩ = EvalTuple (⇓-complete l) (⇓-complete r)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | ⟪ l , r ⟫ | ct = EvalFst ct
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | ⟪ l , r ⟫ | ct = EvalSnd ct

-- 1 * 3 / 10 points

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → v == ⟦ t ⟧
⇓-sound .true .vtrue EvalTrue = refl
⇓-sound .false .vfalse EvalFalse = refl
⇓-sound _ v (EvalIfTrue {_} {c} {_} {_} d d₁) with ⟦ c ⟧ | ⇓-sound _ _ d
⇓-sound _ v (EvalIfTrue d d₁) | .vtrue | refl = ⇓-sound _ _ d₁
⇓-sound _ v (EvalIfFalse {_} {c} {_} {_} d d₁) with ⟦ c ⟧ | ⇓-sound _ _ d
⇓-sound _ v (EvalIfFalse d d₁) | .vfalse | refl = ⇓-sound _ _ d₁
⇓-sound .zero .(vnat Zero) EvalZero = refl
⇓-sound _ _ (EvalSucc {n} d) with ⟦ n ⟧ | ⇓-sound _ _ d
⇓-sound _ _ (EvalSucc d) | _ | refl = refl
⇓-sound _ .vtrue (EvalIsZeroTrue {n} d) with ⟦ n ⟧ | ⇓-sound _ _ d
⇓-sound _ .vtrue (EvalIsZeroTrue d) | .(vnat Zero) | refl = refl
⇓-sound _ .vfalse (EvalIsZeroFalse {n} d) with ⟦ n ⟧ | ⇓-sound _ _ d
⇓-sound _ .vfalse (EvalIsZeroFalse d) | _ | refl = refl
⇓-sound _ v (EvalFst {_} {_} {t} d) with ⟦ t ⟧ | ⇓-sound _ _ d
⇓-sound _ v (EvalFst d) | _ | refl = refl
⇓-sound _ v (EvalSnd {_} {_} {t} d) with ⟦ t ⟧ | ⇓-sound _ _ d
⇓-sound _ v (EvalSnd d) | _ | refl = refl
⇓-sound _ _ (EvalTuple {_} {_} {t} {s} d r) with  ⟦ t ⟧ | ⇓-sound _ _ d | ⟦ s ⟧ | ⇓-sound _ _ r
⇓-sound _ .(⟪ v , w ⟫) (EvalTuple d r) | v | refl | w | refl = refl

-- 1 * 3 / 8 points

-- Termination

-- The execution of a term terminates when there exists a step
-- sequence that evaluates this term to a value.
data _⇓ {σ} (t : Term σ) : Set where
  terminates : ∀ v → Steps t (⌜ v ⌝) → t ⇓

-- If t₁ evaluates to t₂, and t₂ terminates, then t₁ terminates as
-- well.
prepend-steps : ∀ {σ} {t₁ t₂ : Term σ} →  Steps t₁ t₂  → t₂ ⇓  → t₁ ⇓
prepend-steps steps (terminates v x) = terminates v (steps ++ x)

-- All steps terminate.
termination : ∀ {σ} (t : Term σ) → t ⇓
termination true = terminates vtrue Nil
termination false = terminates vfalse Nil
termination (if t then t₁ else t₂) with termination t
termination (if t then t₁ else t₂) | terminates vtrue x with termination t₁
termination (if t then t₁ else t₂) | terminates vtrue x₁ | terminates v x = terminates v ((E-If-Steps x₁) ++ [ E-If-True ] ++ x)
termination (if t then t₁ else t₂) | terminates vfalse x with termination t₂
termination (if t then t₁ else t₂) | terminates vfalse x₁ | terminates v x = terminates v (E-If-Steps x₁ ++ ([ E-If-False ] ++ x))
termination zero = terminates (vnat Zero) Nil
termination (succ t) with termination t
termination (succ t) | terminates (vnat x) x₁ = terminates (vnat (Succ x)) (E-Succ-Steps x₁)
termination (iszero t) with termination t
termination (iszero t) | terminates (vnat Zero) x₁ = terminates vtrue ((E-IsZero-Steps x₁) ++ [ E-IsZeroZero ])
termination (iszero t) | terminates (vnat (Succ x)) x₁ = terminates vfalse (E-IsZero-Steps x₁ ++ [ (E-IsZeroSucc (allNatValue x)) ] )
termination ⟨ t , s ⟩ with termination t | termination s
termination ⟨ t , s ⟩ | terminates v x | terminates v₁ x₁ = terminates ⟪ v , v₁ ⟫ (E-TupleFst-Steps x ++ (E-TupleSnd-Steps (isValueComplete v) x₁))
termination (fst t) with termination t
termination (fst t) | terminates ⟪ v , v₁ ⟫ x = terminates v ((E-FstTuple-Steps x) ++ [ E-TupleFst (V-Tuple (isValueComplete v) (isValueComplete v₁)) ])
termination (snd t) with termination t
termination (snd t) | terminates ⟪ v , v₁ ⟫ x = terminates v₁ ((E-SndTuple-Steps x) ++ [ E-TupleSnd (V-Tuple (isValueComplete v) (isValueComplete v₁)) ])

-- * Determinism & uniqueness of normal forms proofs
--   1 point
-- * Definition of big step semantics
--   1 point
-- * Big-to-small and small-to-big lemmas
--   2 points
-- * Soundness and completeness of big-step semantics
--   2 points
-- * Small step semantics, big step semantics and denotational semantics of pairs
--   1.5 points
-- * Updating existing proofs to handle pairs
--   1.5 points
--
-- Total: 9.00 points (100 % of max)
