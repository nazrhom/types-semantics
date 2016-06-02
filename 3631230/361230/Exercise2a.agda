
module Exercise2a where

-- Author: Sije Harkema - 3631230

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
data _==_ {a}{A : Set a} (x : A) : A → Set a where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}  
  
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
  _×_ : Type → Type → Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  -- Let's add natural numbers
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  -- Let's add tuples
  <_,_>         : ∀{ty₁ ty₂ : Type} -> Term ty₁ -> Term ty₂ -> Term (ty₁ × ty₂)
  fst           : ∀{ty₁ ty₂ : Type} -> Term (ty₁ × ty₂) -> Term ty₁
  snd           : ∀{ty₁ ty₂ : Type} -> Term (ty₁ × ty₂) -> Term ty₂

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue : Value BOOL
  vfalse : Value BOOL
  -- And what else?
  vnat : Nat -> Value NAT
  vtup : ∀{ty₁ ty₂ : Type} -> Value ty₁ -> Value ty₂ -> Value (ty₁ × ty₂)


-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝ 
⌜ vtup a b ⌝ = < ⌜ a ⌝ , ⌜ b ⌝ >

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
-- Tuples
⟦ < a , b > ⟧ = vtup ⟦ a ⟧ ⟦ b ⟧
⟦ fst t ⟧ = vfst ⟦ t ⟧ where 
  vfst : {ty₁ ty₂ : Type} -> Value (ty₁ × ty₂) -> Value ty₁
  vfst (vtup v₁ v₂) = v₁
⟦ snd t ⟧ = vsnd ⟦ t ⟧ where
  vsnd : {ty₁ ty₂ : Type} -> Value (ty₁ × ty₂) -> Value ty₂
  vsnd (vtup v₁ v₂) = v₂


-------------------------------------------------------------------------------
-- Small-step semantics.
-- --------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : ∀ {x} -> IsValue x -> IsValue (succ x)
  V-Tup : ∀ {ty₁ ty₂} {a : Term ty₁} {b : Term ty₂} -> IsValue a -> IsValue b -> IsValue ( < a , b >)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (vtup a b) = V-Tup (isValueComplete a) (isValueComplete b)

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Tup p₁ p₂) with isValueSound p₁ | isValueSound p₂
isValueSound (V-Tup p₁ p₂) | Witness vtrue refl | Witness vtrue refl = Witness (vtup vtrue vtrue) refl
isValueSound (V-Tup p₁ p₂) | Witness vtrue refl | Witness vfalse refl = Witness (vtup vtrue vfalse) refl
isValueSound (V-Tup p₁ p₂) | Witness vtrue refl | Witness (vnat x) refl = Witness (vtup vtrue (vnat x)) refl
isValueSound (V-Tup p₁ p₂) | Witness vtrue refl | Witness (vtup c c₁) refl = Witness (vtup vtrue (vtup c c₁)) refl
isValueSound (V-Tup p₁ p₂) | Witness vfalse refl | Witness vtrue refl = Witness (vtup vfalse vtrue) refl
isValueSound (V-Tup p₁ p₂) | Witness vfalse refl | Witness vfalse refl = Witness (vtup vfalse vfalse) refl
isValueSound (V-Tup p₁ p₂) | Witness vfalse refl | Witness (vnat x) refl = Witness (vtup vfalse (vnat x)) refl
isValueSound (V-Tup p₁ p₂) | Witness vfalse refl | Witness (vtup c c₁) refl = Witness (vtup vfalse (vtup c c₁)) refl
isValueSound (V-Tup p₁ p₂) | Witness (vnat x) refl | Witness vtrue refl = Witness (vtup (vnat x) vtrue) refl
isValueSound (V-Tup p₁ p₂) | Witness (vnat x) refl | Witness vfalse refl = Witness (vtup (vnat x) vfalse) refl
isValueSound (V-Tup p₁ p₂) | Witness (vnat x) refl | Witness (vnat x₁) refl = Witness (vtup (vnat x) (vnat x₁)) refl
isValueSound (V-Tup p₁ p₂) | Witness (vnat x) refl | Witness (vtup c c₁) refl = Witness (vtup (vnat x) (vtup c c₁)) refl
isValueSound (V-Tup p₁ p₂) | Witness (vtup a₁ a₂) refl | Witness vtrue refl = Witness (vtup (vtup a₁ a₂) vtrue) refl
isValueSound (V-Tup p₁ p₂) | Witness (vtup a₁ a₂) refl | Witness vfalse refl = Witness (vtup (vtup a₁ a₂) vfalse) refl
isValueSound (V-Tup p₁ p₂) | Witness (vtup a₁ a₂) refl | Witness (vnat x) refl = Witness (vtup (vtup a₁ a₂) (vnat x)) refl
isValueSound (V-Tup p₁ p₂) | Witness (vtup a₁ a₂) refl | Witness (vtup c c₁) refl = Witness (vtup (vtup a₁ a₂) (vtup c c₁)) refl

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True : forall  {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1' -> 
    Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t') 
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : ∀ {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  -- Order matters for tuple steps
  E-Fst-Fst : ∀ {ty₁ ty₂} {t₁ : Term ty₁} {v₁ : Value ty₁} {t₂ : Term ty₂} {v₂ : Value ty₂} 
    → t₁ == ⌜ v₁ ⌝ → t₂ == ⌜ v₂ ⌝ →  Step (fst < t₁ , t₂ >) t₁
  E-Snd-Snd : ∀ {ty₁ ty₂} {t₁ : Term ty₁} {v₁ : Value ty₁} {t₂ : Term ty₂} {v₂ : Value ty₂} 
    → t₁ == ⌜ v₁ ⌝ → t₂ == ⌜ v₂ ⌝ → Step (snd < t₁ , t₂ >) t₂
  E-Fst : ∀ {ty₁ ty₂} {t t' : Term (ty₁ × ty₂)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd : ∀ {ty₁ ty₂} {t t' : Term (ty₁ × ty₂)} -> Step t t' -> Step (snd t) (snd t')
  E-Tup-Fst : ∀{ty₁ ty₂} {t₁ t₁' : Term ty₁} {t₂ : Term ty₂} → Step t₁ t₁' → Step (< t₁ , t₂ >) (< t₁' , t₂ >)
  E-Tup-Snd : {ty₁ ty₂ : Type} {t₁ : Term ty₁} {v₁ : Value ty₁} {t₂ t₂' : Term ty₂} 
    → t₁ == ⌜ v₁ ⌝ → Step t₂ t₂' → Step  (< t₁ , t₂ >) (< t₁ , t₂' >)

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> (t t' : Term ty) -> Step t t' -> IsValue t -> Empty
valuesDoNotStep .true t' () V-True
valuesDoNotStep .false t' () V-False
valuesDoNotStep .zero t' () V-Zero
valuesDoNotStep _ _ (E-Succ step) (V-Succ v) = valuesDoNotStep _ _ step v
valuesDoNotStep _ (if t then t₁ else t₂) () (V-Tup t₃ t₄)
valuesDoNotStep _ < t , t₁ > (E-Tup-Fst x) (V-Tup t₂ t₃) = valuesDoNotStep _ t x t₂
valuesDoNotStep _ < t , t₁ > (E-Tup-Snd x x₁) (V-Tup t₂ t₃) = valuesDoNotStep _ t₁ x₁ t₃
valuesDoNotStep _ (fst t) () (V-Tup t₁ t₂)
valuesDoNotStep _ (snd t) () (V-Tup t₁ t₂)

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
toVal (< t₁ , t₂ >) (V-Tup a b) = vtup (toVal t₁ a) (toVal t₂ b)

mutual
  if-reduces : ∀ {ty} (t₁ : Term BOOL) (t₂ : Term ty) (t₃ : Term ty) → Red (if t₁ then t₂ else t₃)
  if-reduces true t2 t3 = Reduces E-If-True
  if-reduces false t2 t3 = Reduces E-If-False
  if-reduces (if t1 then t2 else t3) t4 t5 with if-reduces t1 t2 t3
  if-reduces (if t1 then t2 else t3) t4 t5 | Reduces x = Reduces (E-If-If x)
  if-reduces (iszero t1) t2 t3 with iszero-reduces t1
  if-reduces (iszero t1) t2 t3 | Reduces x = Reduces (E-If-If x)
  if-reduces (fst t1) t2 t3 with fstfst-reduces t1
  ... | Reduces x = Reduces (E-If-If x)
  if-reduces (snd t1) t2 t3 with sndsnd-reduces t1
  ... | Reduces x = Reduces (E-If-If x)

  iszero-reduces : (t : Term NAT) -> Red (iszero t) 
  iszero-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂ 
  iszero-reduces (if t then t₁ else t₂) | Reduces x = Reduces (E-IsZero x)
  iszero-reduces zero = Reduces E-IsZeroZero
  iszero-reduces (succ t) with progress t
  iszero-reduces (succ t) | Left x = Reduces (E-IsZeroSucc (normal-forms-are-values _ x))
  iszero-reduces (succ t) | Right (Reduces x) = Reduces (E-IsZero (E-Succ x))
  iszero-reduces (fst t) with fstfst-reduces t
  ... | Reduces x = Reduces (E-IsZero x)
  iszero-reduces (snd t) with sndsnd-reduces t
  ... | Reduces x = Reduces (E-IsZero x)

  fstfst-reduces : ∀{ty ty'} (t : Term (ty × ty')) → Red (fst t)
  fstfst-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ...| Reduces x = Reduces (E-Fst x)
  fstfst-reduces (fst t) with fstfst-reduces t
  ...| Reduces x = Reduces (E-Fst x)
  fstfst-reduces (snd t) with sndsnd-reduces t
  ...| Reduces x = Reduces (E-Fst x)
  fstfst-reduces < t , t₁ > with progress t
  ...| Right (Reduces x) = Reduces (E-Fst (E-Tup-Fst x))
  ...| Left x = {!!}


  sndsnd-reduces : ∀{ty ty'} (t : Term (ty × ty')) → Red (snd t)
  sndsnd-reduces (if t then t₁ else t₂) with if-reduces t t₁ t₂
  ...| Reduces x = Reduces (E-Snd x)
  sndsnd-reduces (fst t) with fstfst-reduces t
  ...| Reduces x = Reduces (E-Snd x)
  sndsnd-reduces (snd t) with sndsnd-reduces t
  ...| Reduces x = Reduces (E-Snd x)
  sndsnd-reduces < t , t₁ > with progress t
  ...| Right (Reduces x) = Reduces (E-Snd (E-Tup-Fst x))
  ...| Left x = {!!}

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values (< a , b >) nf with normal-forms-are-values a {!!} | normal-forms-are-values b {!!}
  normal-forms-are-values (< a , b >) nf | anf | bnf = V-Tup anf bnf
  normal-forms-are-values (fst t) nf = contradiction (nf (fstfst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (sndsnd-reduces t))

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
  progress (< t₁ , t₂ >) with progress t₁
  ... | Right (Reduces x) = Right (Reduces (E-Tup-Fst x))
  ... | Left x = {!!}
  progress (fst t) = Right (fstfst-reduces t)
  progress (snd t) = Right (sndsnd-reduces t)


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
deterministic (E-If-If steps₁) (E-If-If steps₂) = cong (\x -> if x then _ else _) (deterministic steps₁ steps₂)
deterministic (E-Succ steps₁) (E-Succ steps₂) = cong succ (deterministic steps₁ steps₂)
deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())
deterministic {t₂ = t₂} (E-IsZeroSucc {t₃} _) steps₂ = lemma₂ _ t₂ steps₂
  where
  lemma₂ : (v : Value NAT) (t : Term BOOL) -> Step (iszero (succ ⌜ v ⌝)) t -> false == t
  lemma₂ (vnat x) true ()
  lemma₂ (vnat x) false steps = refl
  lemma₂ (vnat x) (if t then t₁ else t₂) ()
  -- This didn't go as planned
  lemma₂ (vnat x) (iszero ._) (E-IsZero (E-Succ steps)) = contradiction (valuesDoNotStep (iszero (succ ⌜ (vnat x) ⌝ )) (iszero _) (E-IsZero (E-Succ steps)) {!!})
  lemma₂ (vnat x) (fst t) ()
  lemma₂ (vnat x) (snd t) ()
deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero (E-Succ steps₁)) (E-IsZeroSucc {t} tIsValue) = contradiction (valuesDoNotStep t {!!} steps₁ tIsValue)
deterministic (E-IsZero steps₁) (E-IsZero steps₂) = cong iszero (deterministic steps₁ steps₂)

deterministic (E-Fst-Fst x y) (E-Fst-Fst x1 y1) = refl
deterministic (E-Fst-Fst {v₁ = v₁} x y) (E-Fst (E-Tup-Fst z)) rewrite x = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ z {!!})
deterministic (E-Fst-Fst {v₂ = v₂} x y) (E-Fst (E-Tup-Snd _ z)) rewrite y = contradiction (valuesDoNotStep (⌜ v₂ ⌝) _ z {!!})
deterministic (E-Snd-Snd x y) (E-Snd-Snd x₁ x₂) = refl
deterministic (E-Snd-Snd {v₁ = v₁} x y) (E-Snd (E-Tup-Fst z)) rewrite x = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ z {!!} )
deterministic (E-Snd-Snd {v₂ = v₂} x y) (E-Snd (E-Tup-Snd _ z)) rewrite y = contradiction (valuesDoNotStep (⌜ v₂ ⌝) _ z {!!})
deterministic (E-Fst (E-Tup-Fst z)) (E-Fst-Fst {v₁ = v₁} x y) rewrite x  = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ z {!!})
deterministic (E-Fst (E-Tup-Snd _ z)) (E-Fst-Fst {v₂ = v₂} x y) rewrite y = contradiction (valuesDoNotStep (⌜ v₂ ⌝) _ z {!!})
deterministic (E-Fst x) (E-Fst y) with deterministic x y
...| refl = refl
deterministic (E-Snd (E-Tup-Fst z)) (E-Snd-Snd {v₁ = v₁} x y) rewrite x = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ z {!!})
deterministic (E-Snd (E-Tup-Snd _ z)) (E-Snd-Snd {v₂ = v₂} x y) rewrite y = contradiction (valuesDoNotStep (⌜ v₂ ⌝) _ z {!!})
deterministic (E-Snd x) (E-Snd y) with deterministic x y
...| refl = refl
deterministic (E-Tup-Fst x) (E-Tup-Fst y) with deterministic x y
...| refl = refl
deterministic (E-Tup-Fst {t₂ = t₂} s) (E-Tup-Snd {v₁ = v₁} prf y) rewrite prf = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ s {!!})
deterministic (E-Tup-Snd {v₁ = v₁} p s) (E-Tup-Fst {t₂ = t₂} y)  rewrite p  = contradiction (valuesDoNotStep (⌜ v₁ ⌝) _ y {!!})
deterministic (E-Tup-Snd p s) (E-Tup-Snd x y) with deterministic s y
...| refl = refl

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
uniqueness-of-normal-forms Nil Nil x x₁ = refl
uniqueness-of-normal-forms Nil (Cons x step₂) x₁ x₂ = contradiction (x₁ (Reduces x))
uniqueness-of-normal-forms (Cons x step₁) Nil x₁ x₂ = contradiction (x₂ (Reduces x))
uniqueness-of-normal-forms (Cons x step₁) (Cons x₁ step₂) x₂ x₃ with deterministic x x₁
uniqueness-of-normal-forms (Cons x step₁) (Cons x₁ step₂) x₂ x₃ | refl = uniqueness-of-normal-forms step₁ step₂ x₂ x₃

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  Eval-True        : true ⇓ vtrue
  Eval-False       : false ⇓ vfalse
  Eval-Zero        : zero  ⇓ (vnat Zero)
  Eval-IfTrue      : ∀{ty c} {t : Term ty} {e : Term ty} {v : Value ty} → c ⇓ vtrue  → t ⇓ v → (if c then t else e) ⇓ v
  Eval-IfFalse     : ∀{ty c} {t : Term ty} {e : Term ty} {v : Value ty} → c ⇓ vfalse → e ⇓ v → (if c then t else e) ⇓ v
  Eval-IsZeroZero  : ∀{t} → t ⇓ (vnat Zero) → (iszero t) ⇓ vtrue
  --  Eval-IsZeroFalse : ∀{t n} → t ⇓ (vnat (Succ n)) → (iszero t) ⇓ vfalse
  Eval-IsZeroSucc : forall {t} {n} -> t ⇓ vnat (Succ n) -> iszero t ⇓ vfalse  
  Eval-Succ        : ∀{t n} → t ⇓ (vnat n) → (succ t) ⇓ (vnat (Succ n))
  Eval-Tup         : ∀{ty₁ ty₂} {t₁ : Term ty₁} {t₂ : Term ty₂} {v₁ : Value ty₁} {v₂ : Value ty₂} → t₁ ⇓ v₁ → t₂ ⇓ v₂ → < t₁ , t₂ > ⇓ (vtup v₁ v₂)
  Eval-Fst         : ∀ {ty₁ ty₂} {t : Term (ty₁ × ty₂)} {v₁ : Value ty₁} {v₂ : Value ty₂} → t ⇓ (vtup v₁ v₂) → fst t ⇓ v₁
  Eval-Snd         : ∀ {ty₁ ty₂} {t : Term (ty₁ × ty₂)} {v₁ : Value ty₁} {v₂ : Value ty₂} → t ⇓ (vtup v₁ v₂) → snd t ⇓ v₂

map-steps : ∀{ty ty' t t'} {f : Term ty → Term ty'} 
  → ({a b : Term ty} → Step a b → Step (f a ) (f b) ) 
  → Steps t t' → Steps (f t) (f t')
map-steps f Nil = Nil
map-steps f (Cons {t₁} {t₂} s ss) = Cons (f s) (map-steps f ss)

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small Eval-True = Nil
big-to-small Eval-False = Nil
big-to-small Eval-Zero = Nil
big-to-small (Eval-IfTrue c b) = map-steps E-If-If (big-to-small c) ++ [ E-If-True ] ++ big-to-small b
big-to-small (Eval-IfFalse c b) = map-steps E-If-If (big-to-small c) ++ [ E-If-False ] ++ big-to-small b
big-to-small (Eval-IsZeroZero t) = map-steps E-IsZero (big-to-small t) ++ [ E-IsZeroZero ]
big-to-small (Eval-IsZeroSucc {t} {n} r) = map-steps E-IsZero (big-to-small r) ++ [ E-IsZeroSucc {!!} ]
big-to-small (Eval-Succ p) = map-steps E-Succ (big-to-small p)
big-to-small {_} {_} {v = vtup v₁ v₂} (Eval-Tup a b) = map-steps E-Tup-Fst (big-to-small a) ++ map-steps (E-Tup-Snd {v₁ = v₁} refl ) (big-to-small b)
big-to-small {_} {_} {v} (Eval-Fst {v₂ = v₂} p) = map-steps E-Fst (big-to-small p) ++ [ E-Fst-Fst {v₁ = v} {v₂ = v₂} refl refl ]
big-to-small {_} {_} {v} (Eval-Snd {v₁ = v₁} p) = map-steps E-Snd (big-to-small p) ++ [ E-Snd-Snd {v₁ = v₁} {v₂ = v} refl refl ]

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} (t : Term ty) -> (p : IsValue t) -> t ⇓ toVal t p
value-to-value .true V-True = Eval-True
value-to-value .false V-False = Eval-False
value-to-value .zero V-Zero = Eval-Zero
value-to-value (succ n) (V-Succ p) = {!!}
value-to-value ._ (V-Tup {t₁} {t₂} a b) = Eval-Tup (value-to-value _ a) (value-to-value _ b)

prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True r = Eval-IfTrue Eval-True r
prepend-step E-If-False r = Eval-IfFalse Eval-False r
prepend-step (E-If-If step) (Eval-IfTrue r r₁) = Eval-IfTrue (prepend-step step r) r₁
prepend-step (E-If-If step) (Eval-IfFalse r r₁) = Eval-IfFalse (prepend-step step r) r₁
prepend-step (E-Succ step) (Eval-Succ r) = Eval-Succ (prepend-step step r)
prepend-step E-IsZeroZero EvalTrue = {!!} --Eval-IsZeroZero Eval-Zero
prepend-step (E-IsZeroSucc x) EvalFalse = {!!}
prepend-step (E-IsZero step) (Eval-IsZeroZero r) = Eval-IsZeroZero (prepend-step step r)
prepend-step (E-IsZero step) (Eval-IsZeroSucc r) = Eval-IsZeroSucc (prepend-step step r)
prepend-step (E-Fst-Fst {v₁ = v₁} {t₂ = t₂} {v₂ = v₂} _ _) r = Eval-Fst (Eval-Tup r (value-to-value t₂ {!!} ))
prepend-step (E-Snd-Snd {t₁ = t₁} {v₁ = v₁} {v₂ = v₂} _ _) r = Eval-Snd (Eval-Tup (value-to-value t₁ {!!}) r )
prepend-step (E-Fst a) (Eval-Fst r) = Eval-Fst (prepend-step a r)
prepend-step (E-Snd a) (Eval-Snd r) = Eval-Snd (prepend-step a r)
prepend-step (E-Tup-Fst a) (Eval-Tup r₁ r₂) = Eval-Tup (prepend-step a r₁) r₂
prepend-step (E-Tup-Snd _ a) (Eval-Tup r₁ r₂) = Eval-Tup r₁ (prepend-step a r₂)


-- And conversion in the other direction
small-to-big : {ty : Type} -> {t t' : Term ty} -> {p : IsValue t'} → Steps t t' → t ⇓ toVal t' p
small-to-big {t = t} {p = p} Nil =  value-to-value t p
small-to-big (Cons x steps) = prepend-step x (small-to-big steps)
  

                                                                                        
--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = Eval-True
⇓-complete false = Eval-False
⇓-complete (if t then t₁ else t₂) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (if t then t₁ else t₂) | vtrue | c = Eval-IfTrue c (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | vfalse | c = Eval-IfFalse c (⇓-complete t₂)
⇓-complete zero = Eval-Zero
⇓-complete (succ t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (succ t) | vnat x | c = Eval-Succ c
⇓-complete (iszero t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (iszero t) | vnat Zero | c = Eval-IsZeroZero c
⇓-complete (iszero t) | vnat (Succ x) | c = Eval-IsZeroSucc c
⇓-complete (< t₁ , t₂ >) = Eval-Tup (⇓-complete t₁) (⇓-complete t₂)
⇓-complete (fst t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (fst t) | vtup v1 v2 | c = Eval-Fst c
⇓-complete (snd t) with ⟦ t ⟧ | ⇓-complete t
⇓-complete (snd t) | vtup v1 v2 | c = Eval-Snd c

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} (t : Term ty) (v : Value ty) → t ⇓ v → ⟦ t ⟧ == v
⇓-sound true .vtrue Eval-True = refl
⇓-sound false .vfalse Eval-False = refl
⇓-sound zero ._ Eval-Zero = refl
⇓-sound (if c then t₁ else t₂) v (Eval-IfTrue p p₁) rewrite (⇓-sound c vtrue p) = ⇓-sound t₁ v p₁
⇓-sound (if c then t₁ else t₂) v (Eval-IfFalse p p₁) rewrite (⇓-sound c vfalse p) = ⇓-sound t₂ v p₁
⇓-sound (iszero t) vtrue (Eval-IsZeroZero p) with ⟦ t ⟧ | ⇓-sound t (vnat Zero) p
⇓-sound (iszero t) vtrue (Eval-IsZeroZero p) | ._ | refl = refl
⇓-sound _ _ (Eval-IsZeroSucc {t} {n} p) with ⟦ t ⟧ | ⇓-sound t (vnat (Succ n)) p
⇓-sound _ _ (Eval-IsZeroSucc p) | ._ | refl = refl
⇓-sound (succ t) .(vnat (Succ n)) (Eval-Succ {n = n} p) rewrite (⇓-sound t (vnat n) p) = refl
⇓-sound (< a , b >) ._ (Eval-Tup {v₁ = v₁} {v₂ = v₂} p₁ p₂) rewrite (⇓-sound a v₁ p₁) | (⇓-sound b v₂ p₂) =  refl
⇓-sound (fst t) v (Eval-Fst {v₂ = v₂} p) rewrite (⇓-sound t (vtup v v₂) p) = refl
⇓-sound (snd t) v (Eval-Snd {v₁ = v₁} p) rewrite (⇓-sound t (vtup v₁ v) p) = refl
