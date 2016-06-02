Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => saturday
    | saturday => sunday
    | sunday => monday
  end.

Eval compute in (next_weekday friday).

Eval compute in (next_weekday (next_weekday friday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = monday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. reflexivity. Qed.

Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | false => true
    | true => negb b2
  end.

Example test_nandb1: (nandb true false) = true.
Proof. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. reflexivity. Qed.

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | false => false
    | true => match b2 with
                | false => false
                | true => b3
              end
  end.

Example test_andb31: (andb3 true true true) = true.
Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. reflexivity. Qed.

Check true.
Check (negb true).
Check negb.

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S k => k
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S k) => k
  end.

Check (S (S (S (S O)))).
Eval compute in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).

Module Playground2.

Fixpoint plus (n:nat) (m:nat) : nat :=
  match n with
    | O => m
    | S k => S (plus k m)
  end.

Eval compute in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S k => plus m (mult k m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
    | O, _ => O
    | S _, O => n
    | S k, S l => minus k l
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
    | O => S O
    | S k => mult n (factorial k)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed.

Notation "x + y" := (plus x y) (at level 50, left associativity) : nat_scope.
Notation "x - y" := (minus x y) (at level 50, left associativity) : nat_scope.
Notation "x * y" := (mult x y) (at level 40, left associativity) : nat_scope.

Check (( 0 + 1 ) + 1).

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
   | O => match m with
           | O => true
           | S m' => false
           end
   | S n' => match m with
              | O => false
              | S m' => beq_nat n' m'
              end
 end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
       match m with
       | O => false
       | S m' => ble_nat n' m'
       end
  end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool := andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof. intros n. reflexivity. Qed.

Theorem plus_n_O : forall n, n + 0 = n.
Proof. simpl. Abort.

Theorem plus_1_l : forall n, 1 + n = S n.
Proof. intros n. reflexivity. Qed.

Theorem mult_0_l : forall n, 0 * n = 0.
Proof. intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m, 
  n = m ->
  n + n = m + m.
Proof. intros n m. intros H. rewrite -> H. reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o. intros H. intros H'. rewrite -> H. rewrite H'. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof. intros n m. rewrite -> plus_O_n. reflexivity. Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof. intros n. simpl. Abort. 

Theorem plus_1_neq_0 : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof. intros n. destruct n as [| n']. reflexivity. reflexivity. Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof. intros b. destruct b. reflexivity. reflexivity. Qed.

(* Exercises zero_nbeq_plus_1 *)

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof. intros n. destruct n. reflexivity. reflexivity. Qed.

(* Exercises boolean_functions *)

Theorem identity_fn_applied_twice :
 forall (f : bool -> bool),
 (forall (x : bool), f x = x) ->
 forall (b : bool), f (f b) = b.
Proof. intros f x b. rewrite -> x. rewrite -> x. reflexivity. Qed.

Theorem negation_fn_applied_twice :
 forall (f : bool -> bool),
 (forall (x : bool), f x = negb x) ->
 forall (b : bool), f (f b) = b.
Proof. intros f x b. rewrite -> x. rewrite -> x. destruct b. reflexivity. reflexivity. Qed.

(* Exercises andb_eq_orb *) 

Theorem andb_eq_orb :
 forall b c : bool,
 (andb b c = orb b c) ->
 b = c.
Proof. intros b c. destruct b. destruct c. reflexivity. simpl.
auto. simpl. auto. Qed.

(* Exercises binary *)

Inductive bin : Type :=
  | Z : bin
  | T : bin -> bin
  | M : bin -> bin.

Fixpoint incr (b:bin) : bin :=
  match b with
  | Z => M Z
  | T b' => M b'
  | M b' => T (incr b') 
  end.

Fixpoint bin_to_nat (b:bin) : nat :=
  match b with
  | Z => 0
  | T b' => bin_to_nat b' + bin_to_nat b'
  | M b' => 1 + (bin_to_nat b' + bin_to_nat b')
  end.

Example test_bin_incr1 : bin_to_nat (incr Z) = 1.
Proof. reflexivity. Qed.
Example test_bin_incr2 : bin_to_nat (incr (M Z)) = 2.
Proof. reflexivity. Qed.
Example test_bin_incr3 : bin_to_nat (incr (T (M Z))) = 3.
Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (incr (T (T (M Z)))) = 5.
Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (T (M Z))) = 1 + bin_to_nat (T (M Z)).
Proof. reflexivity. Qed.

(* Chapter Induction *)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c =  true -> b = true.
Proof. intros b c H. destruct b. Case "b=true". reflexivity.
Case "b = false". rewrite <- H. reflexivity. Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof. intros b c H. destruct b. Case "b=true". rewrite <- H.
reflexivity. Case "b=false". destruct c. SCase "c=true". reflexivity.
SCase "c=false". rewrite <- H. reflexivity. Qed.

Theorem plus_0_r_firsttry : forall n : nat,
  n + 0 = n.
Proof. intros n. simpl. Abort.

Theorem plus_0_r_secondtry : forall n : nat,
  n + 0 = n.
Proof.
 intros n. destruct n as [| n'].
 Case "n = 0".
   reflexivity.
 Case "n = S n'".
   simpl.
Abort.

Theorem plus_0_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.


Theorem minus_diag : forall n : nat,
  minus n n = 0.
Proof. 
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n +  n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> plus_comm.
Abort.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H : n + m = m + n).
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

(* Exercises mult_comm *)

Theorem plus_swap : forall n m p : nat,
 n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + (m + p) = (m + p) + n).
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. rewrite <- plus_assoc.
  assert (H' : p + n = n + p).
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H'. reflexivity.
Qed.

Theorem mul_Sm : forall m n : nat,
  m * S n = m + (m * n).
Proof.
  intros m n. induction m as [|m'].
  Case "m = 0".
    simpl. reflexivity.
  Case "m = S m'".
    simpl. rewrite -> IHm'. rewrite -> plus_swap. reflexivity.
Qed.    

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> mult_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. rewrite -> mul_Sm. reflexivity.
Qed.

(* Exercises evenb_n oddb_Sn *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity.
Qed.

(* More exercises *)

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b as [| b'].
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity. 
Qed.
    
Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b as [| b'].
  Case "b = true".
    simpl. destruct c as [| c'].
    SCase "c = true".
      simpl. reflexivity.
    SCase "c = false".
      simpl. reflexivity.
  Case "b = false".
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

(* Exercises beq_net_refl *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
   simpl. rewrite <- IHn'. reflexivity.
Qed.

(* Exercises plus_swap' *)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm. replace (n + p) with (p + n).
  Case "replace case 1".
    rewrite <- plus_assoc. reflexivity.
  Case "replace case 2".
    rewrite -> plus_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [| b' | b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. reflexivity.
  Case "b = M b'".
    simpl. rewrite -> plus_n_Sm. rewrite -> IHb'. simpl. reflexivity.
Qed.

(* Exercises Binary inverse *)

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
Qed.

(*

There exists an arbitrary number of representations of the same binary number.
For example the natural number 1 can be represented as M Z. But also as M (T Z). 
The implementation of nat_to_bin is deterministic in that it will always return 
the exact same binary representation for a given natural number. nat_to_bin 1 
will always return M Z and never M (T Z).

*)

Fixpoint onlyT (b:bin) : bool :=
  match b with
  | Z => true
  | T b' => onlyT b'
  | M b' => false
  end.

Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | T b' => match onlyT b' with
            | true => Z
            | false => T (normalize b')
            end
  | M b' => M (normalize b')
  end.
    

Theorem onlyT_normalize : forall b : bin,
  onlyT b = true -> normalize b = Z.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. intros H. rewrite -> H. reflexivity.
  Case "b = M b'".
    simpl. intros contra. inversion contra.
Qed.

Theorem onlyT_bin_eq_0 : forall b : bin,
  onlyT b = true -> bin_to_nat b = 0.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. intros H. rewrite -> IHb'. simpl. reflexivity. rewrite -> H. reflexivity.
  Case "b = M b'".
    simpl. intros contra. inversion contra.
Qed.
      

Theorem onlyT_bin_add : forall b : bin,
  onlyT b = true -> nat_to_bin(bin_to_nat b + bin_to_nat b) = Z.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    intros H. simpl. reflexivity.
  Case "b = T b'".
    simpl. intros H. rewrite -> onlyT_bin_eq_0. simpl. reflexivity. rewrite -> H. reflexivity.
  Case "b = M b'".
    simpl. intros contra. inversion contra.
Qed.

Theorem T_bin_norm_eq : forall b : bin,
  onlyT b = false -> nat_to_bin(bin_to_nat b + bin_to_nat b) = T (nat_to_bin (bin_to_nat b)).
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. intros contra. inversion contra.
  Case "b = T b'".
    simpl. intros H. rewrite -> IHb'.  Abort.

Theorem binary_inverse : forall b : bin,
  nat_to_bin(bin_to_nat b) = normalize b.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. pose proof onlyT_bin_add as H. remember (onlyT b') as M. destruct M.
    SCase "M = True". 
      rewrite -> H. reflexivity. rewrite -> HeqM. reflexivity. 
    SCase "M = False".
      rewrite <- IHb'. simpl. Abort.
      
(* Chapter: Lists *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Check (pair 3 5).

Definition fst (p:natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p:natprod) : nat :=
  match p with
  | pair x y => y
  end.

Eval compute in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Eval compute in (fst (3,5)).

Definition fst' (p:natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p:natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p:natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall n m : nat,
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall p : natprod,
  p = (fst p, snd p).
Proof.
  simpl.
Abort.

Theorem surjective_pairing : forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

(* Exercises snd_fst_is_swap *)

Theorem snd_fst_is_swap : forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.

(* Exercises fst_swap_is_snd *)

Theorem fst_swap_is_snd : forall p : natprod,
  fst (swap_pair p) = snd p.
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity.
Qed.


Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | 0 => nil
  | S count' => n :: (repeat n count')
  end.

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => 0
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3 : [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

(* Exercies list_funs *)

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match h with
              | O => nonzeros t
              | S _ => h :: nonzeros t
              end
  end.

Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => match oddb h with
              | false => oddmembers t
              | true => h :: oddmembers t
              end
  end.

Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l:natlist) : nat := length (oddmembers l).

Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
Proof. simpl. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. simpl. reflexivity. Qed.

(* Exercise alternate *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: l1' => match l2 with
              | nil => l1
              | h' :: l2' => h :: h' :: (alternate l1' l2')
              end
  end.

Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
Proof. simpl. reflexivity. Qed.

Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
Proof. simpl. reflexivity. Qed.

Example test_alternate4: alternate [] [20;30] = [20;30].
Proof. simpl. reflexivity. Qed.



Definition bag := natlist.

(* Exercises bag_functions *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => O
  | h :: t => match beq_nat h v with
              | true => S (count v t)
              | false => count v t
              end
  end.

Example test_count1 : count 1 [1;2;3;1;4;1] = 3.
Proof. simpl. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. simpl. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. simpl. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool := 
  match count v s with
  | O => false
  | S _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* Exercise bag_more_functions *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => t
              | false => h :: (remove_one v t)
              end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. simpl. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t => match beq_nat h v with
              | true => remove_all v t
              | false => h :: (remove_all v t)
              end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. simpl. reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. simpl. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
  | nil => true
  | h :: t => match member h s2 with
              | false => false
              | true => subset t (remove_one h s2)
              end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. simpl. reflexivity. Qed.

Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
Proof. simpl. reflexivity. Qed.

Theorem bag_theorem: forall b : bag, forall n : nat,
  count n (add n b) = 1 + count n b.
Proof.
  intros b n. destruct b as [|h t].
  Case "b = []".
    simpl. rewrite <- beq_nat_refl. reflexivity.
  Case "b = h :: t".
    simpl. rewrite <- beq_nat_refl. reflexivity.
Qed.



Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l : natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = []".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. reflexivity.
Qed.



Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| h t].
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = h::t".
    simpl. rewrite -> IHt. reflexivity.
Qed.

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil => [v]
  | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [|n l'].
  Case "l = []".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite <- IHl'.
Abort.


Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = []".
    simpl. reflexivity.
  Case "l = n' :: l'".
    simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    simpl. reflexivity.
  Case "l = n :: l'".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity.
Qed.







(* --------------------------- Start of Exercises ------------------------*)









Module Exercises.

(* All required exercises *)

(* Exercises Chapter induction *)

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H. destruct b. 
  Case "b=true".
    rewrite <- H. reflexivity. 
  Case "b=false". 
    destruct c. 
    SCase "c=true". 
      reflexivity.
    SCase "c=false". 
      rewrite <- H. reflexivity. 
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n +  n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

(*
Destruct n splits the current goal in different subgoals, each
for what the value of n could be.
Induction n does the same but adds the hypothesis as an assumption
to the induction case.
*)

Theorem plus_swap : forall n m p : nat,
 n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H: n + (m + p) = (m + p) + n).
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. rewrite <- plus_assoc.
  assert (H' : p + n = n + p).
    Case "proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H'. reflexivity.
Qed.

Theorem mul_Sm : forall m n : nat,
  m * S n = m + (m * n).
Proof.
  intros m n. induction m as [|m'].
  Case "m = 0".
    simpl. reflexivity.
  Case "m = S m'".
    simpl. rewrite -> IHm'. rewrite -> plus_swap. reflexivity.
Qed.    

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n. induction n as [| n'].
  Case "n = 0".
    simpl. rewrite -> mult_0_r. reflexivity.
  Case "n = S n'".
    simpl. rewrite <- IHn'. rewrite -> mul_Sm. reflexivity.
Qed.

(* Exercises evenb_n oddb_Sn *)
Theorem evenb_n__oddb_Sn : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> negb_involutive. simpl. reflexivity.
Qed.

(* More exercises *)

Theorem ble_nat_refl : forall n : nat,
  true = ble_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b as [| b'].
  Case "b = true".
    reflexivity.
  Case "b = false".
    reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p'].
  Case "p = 0".
    simpl. rewrite -> H. reflexivity.
  Case "p = S p'".
    simpl. rewrite -> IHp'. reflexivity. 
Qed.
    
Theorem S_nbeq_0 : forall n : nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat,
  1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_0_r. reflexivity.
Qed.

Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  intros b c. destruct b as [| b'].
  Case "b = true".
    simpl. destruct c as [| c'].
    SCase "c = true".
      simpl. reflexivity.
    SCase "c = false".
      simpl. reflexivity.
  Case "b = false".
    simpl. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. rewrite -> mult_plus_distr_r. reflexivity.
Qed.

(* Exercises beq_net_refl *)

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
   simpl. rewrite <- IHn'. reflexivity.
Qed.

(* Exercises plus_swap' *)
Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite -> plus_comm. replace (n + p) with (p + n).
  Case "replace case 1".
    rewrite <- plus_assoc. reflexivity.
  Case "replace case 2".
    rewrite -> plus_comm. reflexivity.
Qed.

Theorem bin_to_nat_pres_incr : forall b : bin,
  bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b. induction b as [| b' | b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. reflexivity.
  Case "b = M b'".
    simpl. rewrite -> plus_n_Sm. rewrite -> IHb'. simpl. reflexivity.
Qed.

(* Exercises Binary inverse *)

Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | 0 => Z
  | S n' => incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat : forall n : nat,
  bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> bin_to_nat_pres_incr. rewrite -> IHn'. reflexivity.
Qed.

(*

There exists an arbitrary number of representations of the same binary number.
For example the natural number 1 can be represented as M Z. But also as M (T Z). 
The implementation of nat_to_bin is deterministic in that it will always return 
the exact same binary representation for a given natural number. nat_to_bin 1 
will always return M Z and never M (T Z).

*)

(* 
If the given binary number contains an M, then clearly it does not
consists of only T's, so false is returned. 
Otherwise, we just keep recursively calling the associated binary number
until we come to Z. In that case we did not see an M and therefore the given 
binary number could only contain T's
*)
Fixpoint onlyT (b:bin) : bool :=
  match b with
  | Z => true
  | T b' => onlyT b'
  | M b' => false
  end.

(*
We try to convert binary numbers that contain a sequence of the form
T T T Z to Z. Where the number of T's is arbitrary, but are not interleaved
by M's.
*)
Fixpoint normalize (b:bin) : bin :=
  match b with
  | Z => Z
  | T b' => match onlyT b' with
            | true => Z
            | false => T (normalize b')
            end
  | M b' => M (normalize b')
  end.
    

(* Two additional theorems for proving a case in binary inverse *)
Theorem onlyT_bin_eq_0 : forall b : bin,
  onlyT b = true -> bin_to_nat b = 0.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. intros H. rewrite -> IHb'. simpl. reflexivity. rewrite -> H. reflexivity.
  Case "b = M b'".
    simpl. intros contra. inversion contra.
Qed.
      

Theorem onlyT_bin_add : forall b : bin,
  onlyT b = true -> nat_to_bin(bin_to_nat b + bin_to_nat b) = Z.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    intros H. simpl. reflexivity.
  Case "b = T b'".
    simpl. intros H. rewrite -> onlyT_bin_eq_0. simpl. reflexivity. rewrite -> H. reflexivity.
  Case "b = M b'".
    simpl. intros contra. inversion contra.
Qed.

Theorem nat_bin_mul : forall b : bin,
  nat_to_bin(bin_to_nat(T b)) = nat_to_bin(2 * bin_to_nat b).
Proof.
  intros b. induction b  as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    simpl. rewrite -> plus_0_r. reflexivity.
  Case "b = M b'".
    simpl. rewrite -> plus_0_r. reflexivity.
Qed.

(* I was not able to finish the last part of this exercise *)
Theorem binary_inverse : forall b : bin,
  nat_to_bin(bin_to_nat b) = normalize b.
Proof.
  intros b. induction b as [|b'|b'].
  Case "b = Z".
    simpl. reflexivity.
  Case "b = T b'".
    rewrite -> nat_bin_mul.
    simpl. pose proof onlyT_bin_add as H. remember (onlyT b') as M. destruct M.
    SCase "M = True". Abort.
      (*rewrite -> H. reflexivity. rewrite -> HeqM. reflexivity. 
    SCase "M = False".
      rewrite <- IHb'. simpl. Abort.*)



(* End exercises chapter induction *)

(* Exercises chapter lists *)

(* list exercises part 1 *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem snoc_rev : forall h : nat, forall t : natlist,
  rev (snoc t h) = h :: (rev t).
Proof.
  intros h t. induction t as [| h' t'].
  Case "t = []".
    simpl. reflexivity.
  Case "t = h'::t'".
    simpl. rewrite -> IHt'. simpl. reflexivity.
Qed. 

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl. rewrite -> snoc_rev. rewrite -> IHt. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4. induction l1 as [| h t].
  Case "l1 = []".
    simpl. rewrite -> app_assoc. reflexivity.
  Case "l1 = h :: t".
    simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  intros l n. induction l as [| h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2. induction l1 as [| h t].
  Case "l1 = []".
    simpl. rewrite -> app_nil_end. reflexivity.
  Case "l1 = h :: t".
    simpl. rewrite -> snoc_append. rewrite -> IHt. 
    rewrite -> app_assoc. rewrite <- snoc_append. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2. induction l1  as [| h t].
  Case "l1 = []".
    simpl. reflexivity.
  Case "l1 = h :: t".
    simpl. rewrite -> IHt. destruct h as [|h'].
    SCase "h = O".
      reflexivity.
    SCase "h = S h'".
      simpl. reflexivity.
Qed.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1 with
  | [] => beq_nat (length l2) 0
  | h :: l1' => match l2 with
                | [] => false
                | h' :: l2' => andb (beq_nat h h') (beq_natlist l1' l2')
                end
  end.

Example test_beq_natlist1 : beq_natlist nil nil = true.
Proof. simpl. reflexivity. Qed.

Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
Proof. simpl. reflexivity. Qed.

Example test_beq_natlist3: beq_natlist [1;2;3] [1;2;4] = false.
Proof. simpl. reflexivity. Qed.

Theorem beq_natlist_refl : forall l :natlist,
  true = beq_natlist l l.
Proof.
  intros l. induction l as [| h t].
  Case "l = []".
    simpl. reflexivity.
  Case "l = h :: t".
    simpl. rewrite <- IHt. rewrite <- beq_nat_refl.
    simpl. reflexivity.
Qed.

(* List exercises, part 2 *)

Theorem cons_snoc_app : forall (h:nat) (t:natlist),
  app t (cons h []) = snoc t h.
Proof.
  intros h t. induction t as [| h' t'].
  Case "t = []".
    simpl. reflexivity.
  Case "t = h' :: t'".
    simpl. rewrite -> IHt'. reflexivity.
Qed.

Theorem count_member_nonzer : forall s : bag,
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intros s. induction s as [| h t].
  Case "s = []".
    simpl. reflexivity.
  Case "s = h :: t".
    simpl. reflexivity.
Qed.

Theorem ble_n_Sn : forall n : nat,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    simpl. reflexivity.
  Case "n = S n'".
    simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem remove_decreases_count : forall s : bag,
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  intros s. induction s as [| h t].
  Case "s = []".
    simpl. reflexivity.
  Case "s = h :: t".
    simpl. induction h as [| h'].
    SCase "h = 0".
      simpl. rewrite -> ble_n_Sn. reflexivity.
    SCase "h = S h'".
      simpl. rewrite -> IHt. reflexivity.
Qed.

Theorem bag_count_sum : forall b1 b2 : bag, forall n : nat,
  count n b1 + count n b2 = count n (sum b1 b2).
Proof.
  intros b1 b2 n. induction b1 as [|h t].
  Case "b1 = []".
    simpl. reflexivity.
  Case "b1 = h :: t".
    simpl. destruct (beq_nat h n) as [|].
    SCase "h == n".
      simpl. rewrite -> IHt. reflexivity.
    SCase "h != n".
      rewrite -> IHt. reflexivity.
Qed.

Theorem rev_injective : forall l1 l2 : natlist,
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2 H. induction l1 as [| h t].
  Case "l1 = []".
    rewrite <- rev_involutive. rewrite <- H. simpl. reflexivity.
  Case "l1 = h :: t".
    rewrite <- rev_involutive. rewrite <- H. rewrite -> rev_involutive. reflexivity.
Qed.

Theorem or_comm : forall p q : bool,
  orb p q = orb q p.
Proof.
  intros p q. destruct p.
  Case "p = True".
    simpl. destruct q. reflexivity. simpl. reflexivity.
  Case "p = False".
    simpl. destruct q. reflexivity. simpl. reflexivity.
Qed.

Theorem or_assoc : forall p q r : bool,
  orb (orb p q) r = orb p (orb q r).
Proof.
  intros p q r. destruct p. 
    simpl. reflexivity.
    destruct q.
      simpl. reflexivity.
      destruct r.
        simpl. reflexivity.
        simpl. reflexivity.
Qed.

(* End of exercises chapter lists *)

End Exercises.

