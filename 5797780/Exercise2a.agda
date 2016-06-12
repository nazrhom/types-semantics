-- 5797780

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
  TUP : Type -> Type -> Type

-- Our Term language
data Term : Type -> Set where 
  true          : Term BOOL
  false         : Term BOOL
  if_then_else_ : forall {σ} -> (c : Term BOOL) -> (t e : Term σ) → Term σ
  zero          : Term NAT
  succ          : (n : Term NAT) -> Term NAT
  iszero        : (n : Term NAT) -> Term BOOL
  tup           : forall {tl tr} -> (l : Term tl) -> (r : Term tr) -> Term (TUP tl tr)
  fst           : forall {tl tr} -> (t : Term (TUP tl tr)) -> Term tl
  snd           : forall {tl tr} -> (t : Term (TUP tl tr)) -> Term tr

-- The set of atomic values within the language.
data Value : Type -> Set where
  vtrue  : Value BOOL
  vfalse : Value BOOL
  vnat   : Nat -> Value NAT
  vtup   : forall {tl tr} -> Value tl -> Value tr -> Value (TUP tl tr)

-- Associate each value with a term.
⌜_⌝ : forall {ty} -> Value ty → Term ty
⌜ vtrue ⌝ = true
⌜ vfalse ⌝ = false
⌜ vnat Zero ⌝ = zero
⌜ vnat (Succ x) ⌝ = succ ⌜ vnat x ⌝
⌜ vtup a b ⌝ = tup ⌜ a ⌝ ⌜ b ⌝

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
⟦ tup a b ⟧ = vtup ⟦ a ⟧ ⟦ b ⟧
⟦ fst t ⟧ with ⟦ t ⟧
⟦ fst t ⟧ | vtup a b = a
⟦ snd t ⟧ with ⟦ t ⟧
⟦ snd t ⟧ | vtup a b = b

-------------------------------------------------------------------------------
-- Small-step semantics.
-----------------------------------------------------------------------------------

data IsValue : {ty : Type} -> Term ty -> Set where
  V-True : IsValue true
  V-False : IsValue false
  V-Zero : IsValue zero
  V-Succ : forall {x} -> IsValue x -> IsValue (succ x)
  V-Tup  : forall {tl tr : Type} {x y} -> IsValue {tl} x -> IsValue {tr} y -> IsValue (tup x y)

isValueComplete : forall {ty} -> (v : Value ty) -> IsValue ⌜ v ⌝ 
isValueComplete vtrue = V-True
isValueComplete vfalse = V-False
isValueComplete (vnat Zero) = V-Zero
isValueComplete (vnat (Succ x)) = V-Succ (isValueComplete (vnat x))
isValueComplete (vtup a b) = V-Tup (isValueComplete a) (isValueComplete b)

-- Lemma to help isValueSound.
isValueSoundTuple : forall {tl tr} {a : Term tl} {b : Term tr} {x : Value tl} {y : Value tr}
                  -> (⌜ x ⌝ == a) -> (⌜ y ⌝ == b) -> (tup ⌜ x ⌝ ⌜ y ⌝ == tup a b)
isValueSoundTuple refl refl = refl

isValueSound : forall {ty} {t : Term ty} -> IsValue t -> Exists (Value ty) (\v -> ⌜ v ⌝ == t)
isValueSound V-True = Witness vtrue refl
isValueSound V-False = Witness vfalse refl
isValueSound V-Zero = Witness (vnat Zero) refl
isValueSound (V-Succ p) with isValueSound p
isValueSound (V-Succ p) | Witness (vnat k) q = Witness (vnat (Succ k) ) (cong succ q)
isValueSound (V-Tup pl pr) with isValueSound pl
... | Witness a ppl with isValueSound pr
... | Witness b ppr = Witness (vtup a b) (isValueSoundTuple ppl ppr)

data Step  : {ty : Type} -> Term ty → Term ty → Set where
  E-If-True    : forall {ty} {t1 t2 : Term ty} -> Step (if true then t1 else t2) t1
  E-If-False   : forall {ty} {t1 t2 : Term ty} -> Step (if false then t1 else t2) t2
  E-If-If      : forall {ty} {t1 t1' : Term BOOL} {t2 t3 : Term ty} -> Step t1 t1'
                 -> Step (if t1 then t2 else t3) (if t1' then t2 else t3)
  E-Succ       : forall {t t' : Term NAT} -> Step t t' -> Step (succ t) (succ t')
  E-IsZeroZero : Step (iszero zero) true
  E-IsZeroSucc : forall {t : Term NAT} -> IsValue t -> Step (iszero (succ t)) false
  E-IsZero     : forall {t t' : Term NAT} -> Step t t' -> Step (iszero t) (iszero t')
  -- Taking the first or second element of a tuple is only allowed after the tuple has
  -- been fully evaluated to a normal form. This is silly performance-wise, but it is
  -- the easiest way to ensure determinism.
  E-FstTup     : forall {tl tr} {a : Term tl} {b : Term tr}
                 -> IsValue (tup a b) -> Step (fst (tup a b)) a
  E-SndTup     : forall {tl tr} {a : Term tl} {b : Term tr}
                 -> IsValue (tup a b) -> Step (snd (tup a b)) b
  E-Fst        : forall {tl tr} {t t' : Term (TUP tl tr)} -> Step t t' -> Step (fst t) (fst t')
  E-Snd        : forall {tl tr} {t t' : Term (TUP tl tr)} -> Step t t' -> Step (snd t) (snd t')
  E-Tup-Fst    : forall {tl tr} {a a' : Term tl} {b : Term tr} -> Step a a'
                 -> Step (tup a b) (tup a' b)
  -- To take a step in evaluating the second element of a tuple, require a proof that the first
  -- element is a value. This is necessary to ensure determinism, otherwise we could step either
  -- the first or second element.
  E-Tup-Snd    : forall {tl tr} {a : Term tl} {b b' : Term tr} -> IsValue a -> Step b b'
                 -> Step (tup a b) (tup a b')

preservation : ∀ {ty} -> (t t' : Term ty) -> Step t t' -> ty == ty
preservation t t' step = refl

valuesDoNotStep : forall {ty} -> {t t' : Term ty} -> Step t t' -> IsValue t -> Empty
valuesDoNotStep {_} {.true} () V-True
valuesDoNotStep {_} {.false} () V-False
valuesDoNotStep {_} {.zero} () V-Zero
valuesDoNotStep (E-Succ step) (V-Succ v) = valuesDoNotStep step v
valuesDoNotStep (E-Tup-Fst step) (V-Tup pl pr) = valuesDoNotStep step pl
valuesDoNotStep (E-Tup-Snd iv step) (V-Tup pl pr) = valuesDoNotStep step pr

-- A term is reducible when some evaluation step can be applied to it.
data Red {ty : Type} (t : Term ty) : Set where
  Reduces : {t' : Term ty} -> Step t t' -> Red t

-- A term is considered a normal form whenever it is not reducible.
NF : ∀ {ty} -> Term ty → Set
NF t = Red t -> Empty

toVal : forall {ty} -> {t : Term ty} -> IsValue t -> Value ty
toVal V-True = vtrue
toVal V-False = vfalse
toVal V-Zero = vnat Zero
toVal (V-Succ v) with toVal v
toVal (V-Succ v) | vnat x₁ = vnat (Succ x₁)
toVal (V-Tup pl pr) = vtup (toVal pl) (toVal pr)

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

  fst-reduces : forall {tl tr} -> (t : Term (TUP tl tr)) -> Red (fst t)
  fst-reduces t with progress t
  fst-reduces t | Left nf with normal-forms-are-values t nf
  fst-reduces _ | Left nf | V-Tup vl vr = Reduces (E-FstTup (V-Tup vl vr))
  fst-reduces t | Right (Reduces x) = Reduces (E-Fst x)

  snd-reduces : forall {tl tr} -> (t : Term (TUP tl tr)) -> Red (snd t)
  snd-reduces t with progress t
  snd-reduces t | Left nf with normal-forms-are-values t nf
  snd-reduces _ | Left nf | V-Tup vl vr = Reduces (E-SndTup (V-Tup vl vr))
  snd-reduces t | Right (Reduces x) = Reduces (E-Snd x)

  succ-nf : (k : Term NAT) -> NF (succ k) -> Red k -> Empty
  succ-nf _ nf (Reduces x) = nf (Reduces (E-Succ x))

  fst-nf : forall {tl tr} (a : Term tl) (b : Term tr) -> NF (tup a b) -> NF a
  fst-nf _ _ nf (Reduces x) = nf (Reduces (E-Tup-Fst x))

  snd-nf : forall {tl tr} (a : Term tl) (b : Term tr) -> NF (tup a b) -> NF b
  snd-nf a b nf (Reduces x) = nf (Reduces (E-Tup-Snd (normal-forms-are-values a (fst-nf a b nf)) x))

  normal-forms-are-values : ∀ {ty} (t : Term ty) → NF t → IsValue t
  normal-forms-are-values true nf = V-True
  normal-forms-are-values false nf = V-False
  normal-forms-are-values (if t then t₁ else t₂) nf = contradiction (nf (if-reduces t t₁ t₂))
  normal-forms-are-values zero nf = V-Zero
  normal-forms-are-values (succ t) nf = V-Succ (normal-forms-are-values t (succ-nf t nf))
  normal-forms-are-values (iszero t) nf = contradiction (nf (iszero-reduces t))
  normal-forms-are-values (tup a b) nf = V-Tup
    (normal-forms-are-values a (fst-nf a b nf))
    (normal-forms-are-values b (snd-nf a b nf))
  normal-forms-are-values (fst t) nf = contradiction (nf (fst-reduces t))
  normal-forms-are-values (snd t) nf = contradiction (nf (snd-reduces t))

  values-are-normal-forms : forall {ty} -> {t : Term ty} -> IsValue t -> NF t
  values-are-normal-forms p (Reduces step) = valuesDoNotStep step p

  lemma-nf-succ : (k : Term NAT) -> NF k -> NF (succ k)
  lemma-nf-succ t nf (Reduces (E-Succ x)) = nf (Reduces x)

  lemma-nf-tup : forall {tl tr} (a : Term tl) (b : Term tr) -> NF a -> NF b -> NF (tup a b)
  lemma-nf-tup a b nfa nfb (Reduces (E-Tup-Fst x)) = nfa (Reduces x)
  lemma-nf-tup a b nfa nfb (Reduces (E-Tup-Snd iv x)) = nfb (Reduces x)

  progress : {ty : Type} -> (t : Term ty) -> Either (NF t) (Red t)
  progress true = Left (values-are-normal-forms V-True)
  progress false = Left (values-are-normal-forms V-False)
  progress (if t then t₁ else t₂) = Right (if-reduces _ _ _)
  progress zero = Left (values-are-normal-forms V-Zero)
  progress (succ t) with progress t
  progress (succ t) | Left x = Left (lemma-nf-succ t x)
  progress (succ t) | Right (Reduces step) = Right (Reduces (E-Succ step))
  progress (iszero t) = Right (iszero-reduces _ )
  progress (tup a b) with progress a
  progress (tup a b) | Left nfa with progress b
  progress (tup a b) | Left nfa | Left nfb = Left (lemma-nf-tup a b nfa nfb)
  progress (tup a b) | Left nfa | Right (Reduces x) = let aval = normal-forms-are-values a nfa
                                                      in Right (Reduces (E-Tup-Snd aval x))
  progress (tup a b) | Right (Reduces x) = Right (Reduces (E-Tup-Fst x))
  progress (fst t) with progress t
  progress (fst t) | Left nf with normal-forms-are-values t nf
  progress (fst _) | Left nf | V-Tup vl vr = Right (Reduces (E-FstTup (V-Tup vl vr)))
  progress (fst t) | Right (Reduces x) = Right (Reduces (E-Fst x))
  progress (snd t) with progress t
  progress (snd t) | Left nf with normal-forms-are-values t nf
  progress (snd _) | Left nf | V-Tup vl vr = Right (Reduces (E-SndTup (V-Tup vl vr)))
  progress (snd t) | Right (Reduces x) = Right (Reduces (E-Snd x))

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
deterministic (E-If-If step₁) (E-If-If step₂) =
  let ih = deterministic step₁ step₂ in cong (λ cond -> if cond then _ else _) ih

deterministic (E-Succ step₁) (E-Succ step₂) = cong succ (deterministic step₁ step₂)

deterministic E-IsZeroZero E-IsZeroZero = refl
deterministic E-IsZeroZero (E-IsZero ())

deterministic (E-IsZeroSucc iv₁) (E-IsZeroSucc iv₂) = refl
deterministic (E-IsZeroSucc iv) (E-IsZero step) = contradiction (valuesDoNotStep step (V-Succ iv))

deterministic (E-IsZero ()) E-IsZeroZero
deterministic (E-IsZero step) (E-IsZeroSucc iv) = contradiction (valuesDoNotStep step (V-Succ iv))
deterministic (E-IsZero step₁) (E-IsZero step₂) = cong iszero (deterministic step₁ step₂)

deterministic (E-FstTup iv) (E-FstTup _) = refl
deterministic (E-FstTup iv) (E-Fst step) = contradiction (valuesDoNotStep step iv)

deterministic (E-SndTup iv) (E-SndTup _) = refl
deterministic (E-SndTup iv) (E-Snd step) = contradiction (valuesDoNotStep step iv)

deterministic (E-Fst step) (E-FstTup iv) = contradiction (valuesDoNotStep step iv)
deterministic (E-Fst step₁) (E-Fst step₂) = cong fst (deterministic step₁ step₂)

deterministic (E-Snd step) (E-SndTup iv) = contradiction (valuesDoNotStep step iv)
deterministic (E-Snd step₁) (E-Snd step₂) = cong snd (deterministic step₁ step₂)

deterministic (E-Tup-Fst step₁) (E-Tup-Snd iv step₂) = contradiction (valuesDoNotStep step₁ iv)
deterministic (E-Tup-Fst step₁) (E-Tup-Fst step₂) =
  let ih = deterministic step₁ step₂ in cong (λ a -> tup a _) ih

deterministic (E-Tup-Snd iv step) (E-Tup-Fst step₂) = contradiction (valuesDoNotStep step₂ iv)
deterministic (E-Tup-Snd iv₁ step₁) (E-Tup-Snd iv₂ step₂) =
  let ih = deterministic step₁ step₂ in cong (λ b -> tup _ b) ih

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

-- The signature of this map function looks really intimidating, but what the function does
-- is quite trivial: it maps something like E-If-If or E-Succ over a list of steps.
map : forall {ty₁ ty₂ : Type} {t₁ t₂ : Term ty₁} {f : Term ty₁ -> Term ty₂}
    -> (g : forall {u₁ u₂} -> Step u₁ u₂ -> Step (f u₁) (f u₂)) -> Steps t₁ t₂ -> Steps (f t₁) (f t₂)
map g Nil = Nil
map g (Cons step steps) = Cons (g step) (map g steps)

-- Use the the deterministic property of the small step semantics to
-- show that normal forms are unique
uniqueness-of-normal-forms :
  ∀ {ty} {t t₁ t₂ : Term ty} →
  Steps t t₁ → Steps t t₂ → NF t₁ → NF t₂ → t₁ == t₂
uniqueness-of-normal-forms Nil Nil nf₁ nf₂ = refl
uniqueness-of-normal-forms Nil (Cons step steps) nf₁ nf₂ with nf₁ (Reduces step)
... | ()
uniqueness-of-normal-forms (Cons step steps) Nil nf₁ nf₂ with nf₂ (Reduces step)
... | ()
uniqueness-of-normal-forms (Cons s₁ steps₁) (Cons s₂ steps₂) with deterministic s₁ s₂
... | refl = uniqueness-of-normal-forms steps₁ steps₂

------------------------------------------------------------------------
-- Big-step semantics.

-- Define an equivalent big step semantics
data _⇓_ : {ty : Type} -> Term ty → Value ty → Set where
  B-True        : (true ⇓ vtrue)
  B-False       : (false ⇓ vfalse)
  B-If-True     : forall {ty : Type} {cond : Term BOOL} {t : Term ty} {f : Term ty} {v : Value ty}
                  -> (cond ⇓ vtrue) -> (t ⇓ v) -> (if cond then t else f) ⇓ v
  B-If-False    : forall {ty : Type} {cond : Term BOOL} {t : Term ty} {f : Term ty} {v : Value ty}
                  -> (cond ⇓ vfalse) -> (f ⇓ v) -> (if cond then t else f) ⇓ v
  B-Zero        : (zero ⇓ vnat Zero)
  B-Succ        : forall {t : Term NAT} {n : Nat}
                  -> (t ⇓ (vnat n)) -> (succ t) ⇓ vnat (Succ n)
  B-IsZero-Zero : forall {t : Term NAT}
                  -> (t ⇓ (vnat Zero)) -> (iszero t) ⇓ vtrue
  B-IsZero-Succ : forall {t : Term NAT} {n : Nat}
                  -> (t ⇓ (vnat (Succ n))) -> (iszero t) ⇓ vfalse
  B-Fst         : forall {tl tr} {t : Term (TUP tl tr)} {a : Value tl} {b : Value tr}
                  -> (t ⇓ vtup a b) -> (fst t) ⇓ a
  B-Snd         : forall {tl tr} {t : Term (TUP tl tr)} {a : Value tl} {b : Value tr}
                  -> (t ⇓ vtup a b) -> (snd t) ⇓ b
  B-Tup         : forall {tl tr} {t₁ : Term tl} {t₂ : Term tr} {a : Value tl} {b : Value tr}
                  -> (t₁ ⇓ a) -> (t₂ ⇓ b) -> (tup t₁ t₂) ⇓ (vtup a b)

-- Show how to convert from big step to small step semantics
big-to-small : ∀ {ty} {t : Term ty} {v : Value ty} → t ⇓ v → Steps t ⌜ v ⌝
big-to-small B-True = Nil
big-to-small B-False = Nil
big-to-small (B-If-True bs-cond bs-body) =
  let steps-cond = map E-If-If (big-to-small bs-cond)
      steps-body = big-to-small bs-body
  in steps-cond  ++ [ E-If-True ] ++ steps-body
big-to-small (B-If-False bs-cond bs-body) =
  let steps-cond = map E-If-If (big-to-small bs-cond)
      steps-body = big-to-small bs-body
  in steps-cond ++ [ E-If-False ] ++ steps-body
big-to-small B-Zero = Nil
big-to-small (B-Succ bs) = map E-Succ (big-to-small bs)
big-to-small (B-IsZero-Zero bs) = (map E-IsZero (big-to-small bs)) ++ [ E-IsZeroZero ]
big-to-small (B-IsZero-Succ bs) =
  let steps = big-to-small bs
      isValue = isValueComplete (vnat _)
  in (map E-IsZero steps) ++ [ E-IsZeroSucc isValue ]
big-to-small (B-Fst bs) =
  let steps = big-to-small bs
      isValue = isValueComplete (vtup _ _)
  in (map E-Fst steps) ++ [ E-FstTup isValue ]
big-to-small (B-Snd bs) =
  let steps = big-to-small bs
      isValue = isValueComplete (vtup _ _)
  in (map E-Snd steps) ++ [ E-SndTup isValue ]
big-to-small {_} {_} {vtup a b} (B-Tup bsl bsr) =
  let stepsl = big-to-small bsl
      stepsr = big-to-small bsr
      isValue = isValueComplete a
  in (map E-Tup-Fst stepsl) ++ (map (E-Tup-Snd isValue) stepsr)

-- Note: below are a few two-stage with clauses.
-- If these are merged into a single with, the code doesn't typecheck any more.

-- Conversion from small- to big-step representations.
value-to-value : forall {ty} {t : Term ty} -> (p : IsValue t) -> t ⇓ toVal p
value-to-value V-True = B-True
value-to-value V-False = B-False
value-to-value V-Zero = B-Zero
value-to-value (V-Succ p) with value-to-value p
... | bsv with toVal p
... | vnat x = B-Succ bsv
value-to-value (V-Tup pl pr) with value-to-value pl
... | bsvl with toVal pl
... | vl with value-to-value pr
... | bsvr with toVal pr
... | vr = B-Tup bsvl bsvr

prepend-step : {ty : Type} -> {t t' : Term ty} {v : Value ty} → Step t t' -> t' ⇓ v → t ⇓ v
prepend-step E-If-True bs = B-If-True B-True bs
prepend-step E-If-False bs = B-If-False B-False bs
prepend-step (E-If-If st) (B-If-True bcond bb) = B-If-True (prepend-step st bcond) bb
prepend-step (E-If-If st) (B-If-False bcond bb) = B-If-False (prepend-step st bcond) bb
prepend-step (E-Succ st) (B-Succ bs) = B-Succ (prepend-step st bs)
prepend-step E-IsZeroZero B-True = B-IsZero-Zero B-Zero
prepend-step (E-IsZeroSucc p) B-False with value-to-value p
... | bsv with toVal p
... | vnat x = let bssv = B-Succ bsv in B-IsZero-Succ bssv
prepend-step (E-IsZero st) (B-IsZero-Zero bs) = B-IsZero-Zero (prepend-step st bs)
prepend-step (E-IsZero st) (B-IsZero-Succ bs) = B-IsZero-Succ (prepend-step st bs)
prepend-step (E-FstTup (V-Tup vl vr)) bs = B-Fst (B-Tup bs (value-to-value vr))
prepend-step (E-SndTup (V-Tup vl vr)) bs = B-Snd (B-Tup (value-to-value vl) bs)
prepend-step (E-Fst st) (B-Fst bs) = B-Fst (prepend-step st bs)
prepend-step (E-Snd st) (B-Snd bs) = B-Snd (prepend-step st bs)
prepend-step (E-Tup-Fst st) (B-Tup bsl bsr) = B-Tup (prepend-step st bsl) bsr
prepend-step (E-Tup-Snd iv st) (B-Tup bsl bsr) = B-Tup bsl (prepend-step st bsr)

-- And conversion in the other direction
small-to-big : {ty : Type} -> {t t' : Term ty} -> (p : IsValue t') → Steps t t' → t ⇓ toVal p
small-to-big p Nil = value-to-value p
small-to-big p (Cons step steps) = prepend-step step (small-to-big p steps)

--------------------------------------------------------------------------------
-- Relating denotational semantics and big-step semantics

-- Prove completeness of the big-step semantics when using the
-- evaluation function: each term should reduce to its evaluation.

-- Note: one would think that all those with clauses are not necessary,
-- and that recursive calls would suffice (especially those for evaluation),
-- but I can't get that to work, Agda insists ...
⇓-complete : ∀ {ty} (t : Term ty) → t ⇓ ⟦ t ⟧
⇓-complete true = B-True
⇓-complete false = B-False
⇓-complete (if t then t₁ else t₂) with ⇓-complete t
⇓-complete (if t then t₁ else t₂) | bs with ⟦ t ⟧
⇓-complete (if t then t₁ else t₂) | bs | vtrue = B-If-True bs (⇓-complete t₁)
⇓-complete (if t then t₁ else t₂) | bs | vfalse = B-If-False bs (⇓-complete t₂)
⇓-complete zero = B-Zero
⇓-complete (succ t) with ⇓-complete t
⇓-complete (succ t) | bs with ⟦ t ⟧
⇓-complete (succ t) | bs | vnat x = B-Succ bs
⇓-complete (iszero t) with ⇓-complete t
⇓-complete (iszero t) | bs with ⟦ t ⟧
⇓-complete (iszero t) | bs | vnat Zero = B-IsZero-Zero bs
⇓-complete (iszero t) | bs | vnat (Succ x) = B-IsZero-Succ bs
⇓-complete (tup a b) = B-Tup (⇓-complete a) (⇓-complete b)
⇓-complete (fst t) with ⇓-complete t
⇓-complete (fst t) | bs with ⟦ t ⟧
⇓-complete (fst t) | bs | vtup a b = B-Fst bs
⇓-complete (snd t) with ⇓-complete t
⇓-complete (snd t) | bs with ⟦ t ⟧
⇓-complete (snd t) | bs | vtup a b = B-Snd bs

-- A lemma to help prove the (succ t) case. It is like cong succ, but for values.
cong-succ : {a b : Nat} -> (vnat a == vnat b) -> (vnat (Succ a) == vnat (Succ b))
cong-succ refl = refl

-- If a tuple is equal, then the projections are equal too.
cong-fst : forall {tl tr} {a a' : Value tl} {b b' : Value tr} -> (vtup a b == vtup a' b') -> a == a'
cong-fst refl = refl

cong-snd : forall {tl tr} {a a' : Value tl} {b b' : Value tr} -> (vtup a b == vtup a' b') -> b == b'
cong-snd refl = refl

-- Conversely, if the elements are equal, then their embeddings are equal.
cong-tup : forall {tl tr} {a a' : Value tl} {b b' : Value tr}
           -> (a == a') -> (b == b') -> (vtup a b == vtup a' b')
cong-tup refl refl = refl

-- Prove soundness of the big-step semantics: when a term can be
-- big-step evaluated to a value, this value should be the evaluation
-- of that term.
⇓-sound : ∀ {ty} {v : Value ty} -> (t : Term ty)  → t ⇓ v → v == ⟦ t ⟧
⇓-sound true B-True = refl
⇓-sound false B-False = refl
⇓-sound (if t then t₁ else t₂) (B-If-True bc bs) with ⇓-sound _ bc
⇓-sound (if t then t₁ else t₂) (B-If-True bc bs) | ih with ⟦ t ⟧
⇓-sound (if t then t₁ else t₂) (B-If-True bc bs) | ih | vtrue = ⇓-sound _ bs
⇓-sound (if t then t₁ else t₂) (B-If-True bc bs) | () | vfalse
⇓-sound (if t then t₁ else t₂) (B-If-False bc bs) with ⇓-sound _ bc
⇓-sound (if t then t₁ else t₂) (B-If-False bc bs) | ih with ⟦ t ⟧
⇓-sound (if t then t₁ else t₂) (B-If-False bc bs) | () | vtrue
⇓-sound (if t then t₁ else t₂) (B-If-False bc bs) | ih | vfalse = ⇓-sound _ bs
⇓-sound zero B-Zero = refl
⇓-sound (succ t) (B-Succ bs) with ⇓-sound _ bs
⇓-sound (succ t) (B-Succ bs) | ih with ⟦ t ⟧
⇓-sound (succ t) (B-Succ bs) | ih | vnat x = cong-succ ih
⇓-sound (iszero t) (B-IsZero-Zero bs) with ⇓-sound _ bs
⇓-sound (iszero t) (B-IsZero-Zero bs) | ih with ⟦ t ⟧
⇓-sound (iszero t) (B-IsZero-Zero bs) | ih | vnat Zero = refl
⇓-sound (iszero t) (B-IsZero-Zero bs) | () | vnat (Succ x)
⇓-sound (iszero t) (B-IsZero-Succ bs) with ⇓-sound _ bs
⇓-sound (iszero t) (B-IsZero-Succ bs) | ih with ⟦ t ⟧
⇓-sound (iszero t) (B-IsZero-Succ bs) | () | vnat Zero
⇓-sound (iszero t) (B-IsZero-Succ bs) | ih | vnat (Succ x) = refl
⇓-sound (fst t) (B-Fst bs) with ⇓-sound _ bs
⇓-sound (fst t) (B-Fst bs) | ih with ⟦ t ⟧
⇓-sound (fst t) (B-Fst bs) | ih | vtup a b = cong-fst ih
⇓-sound (snd t) (B-Snd bs) with ⇓-sound _ bs
⇓-sound (snd t) (B-Snd bs) | ih with ⟦ t ⟧
⇓-sound (snd t) (B-Snd bs) | ih | vtup a b = cong-snd ih
⇓-sound (tup a b) (B-Tup bsl bsr) with ⇓-sound _ bsl
⇓-sound (tup a b) (B-Tup bsl bsr) | ihl with ⟦ a ⟧
⇓-sound (tup a b) (B-Tup bsl bsr) | ihl | vl with ⇓-sound _ bsr
⇓-sound (tup a b) (B-Tup bsl bsr) | ihl | vl | ihr with ⟦ b ⟧
⇓-sound (tup a b) (B-Tup bsl bsr) | ihl | vl | ihr | vr = cong-tup ihl ihr
