Require Import Arith.

Inductive exp : Type := 
    | Apply : exp -> exp -> exp
    | Lambda : exp -> exp
    | Index : nat -> exp.

Fixpoint subst t1 t2 i := match t1 with 
    | Apply e1 e2 => Apply(subst e1 t2 i) (subst e2 t2 i)
    | Lambda e =>  Lambda (subst e t2 (i+1))
    | Index j => if Nat.eqb i j then t2 else Index(j)
end.

Fixpoint beta_red t := match t with 
    | Apply (Lambda(t1)) t2 => subst t1 t2 0
    | Apply t1 t2 => Apply (beta_red t1) (beta_red t2)
    | Lambda t1 => Lambda (beta_red t1)
    | t1 => t1
end.

Fixpoint beta_red_n t n := match n with
    | 0 => t
    | S m => beta_red_n (beta_red t) (m)
end.

Notation "\lam T" := (Lambda T) (at level 200).
Notation "@( T U )" := (Apply (T, U)) (at level 200).
Notation "( $ U )" := (Index U) (at level 200).


(* SUCC := λn.λf.λx.f (n f x) *)
Definition succ := Lambda(Lambda(Lambda(
    Apply 
        (Index 1)
        (Apply
            (Apply 
                (Index 2)
                (Index 1)
            )
            (Index 0)
        )
    )
)).

Definition zero := Lambda (Lambda (Index 0)).
Definition one := beta_red_n (Apply succ zero) 10.

Compute one.

(* SUM := λm.λn.λf.λx.m f (n f x) *)

Definition sum := Lambda(Lambda(Lambda(Lambda(
    Apply
        (Apply
            (Index 3) 
            (Index 1)
        )
        (Apply
            (Apply 
                (Index 2)
                (Index 1)
            )
            (Index 0)
        )
)))).

Print sum.


Definition two := beta_red_n (Apply succ one) 10.

Definition four := beta_red_n (Apply(Apply sum two) two) 30.

Compute beta_red_n (Apply(Apply sum four) two) 30.


Fixpoint count_s t := match t with
    | Apply (Index 1) (t1) => let maybe_n := count_s (t1) in
        match maybe_n with 
            | None => None
            | Some n => Some (n + 1)
        end
    | Index 0 => Some 0
    | _ => None
end.

Definition lambda_to_num t := match t with 
    | Lambda(Lambda(t1)) => count_s t1
    | _ => None
end.

Compute lambda_to_num (beta_red_n(Apply(Apply(sum four)) (four)) 40).

Fixpoint num_to_s n := match n with
    | 0 => Index 0
    | S n1 => Apply (Index 1) (num_to_s n1)
end.

Definition num_to_lambda n := Lambda(Lambda(num_to_s n)).

Compute num_to_lambda 5 .

Compute lambda_to_num (beta_red_n(Apply(Apply sum (num_to_lambda 10)) (num_to_lambda 7)) 40).

(* 2+2=4, no matter what Orwell and Radiohead say.... *)
Lemma two_plus_2 : exists k1 k2 : nat , 
beta_red_n (Apply (Apply sum two) (two)) k1 = beta_red_n (four) k2.
Proof.
    exists 10, 10.
    simpl.
    reflexivity.
Qed.

(* sum 1 is the same as succ *)
Lemma sum1' : exists k1 k2 , 
    beta_red_n (Apply(sum) (num_to_lambda 1)) k1 = beta_red_n (succ) k2.
Proof.
    exists 10, 10.
    simpl.
    reflexivity.
Qed.


Inductive red_step : exp -> exp -> Prop := 
    | red_beta : forall t1 t2 : exp , red_step (Apply (Lambda(t1)) t2)  (subst t1 t2 0)
    | red_apply1 : forall t1 t2 t1' , red_step t1 t1' 
        -> red_step (Apply t1 t2) (Apply t1' t2)
    | red_apply2 : forall t1 t2 t2' , red_step t2 t2' 
        -> red_step (Apply t1 t2) (Apply t1 t2')
    | red_lambda : forall t t' , red_step t t' 
        -> red_step (Lambda t) (Lambda t').


Inductive eq_clos (R : exp -> exp -> Prop) : (exp -> exp -> Prop) :=
    | eq_id   : forall e1 e2 : exp , 
        R e1 e2 -> eq_clos R e1 e2
    | eq_refl : forall e : exp , eq_clos R e e
    | eq_tran : forall e1 e2 e3 : exp, 
        (eq_clos R e1 e2) /\ (eq_clos R e2 e3) -> eq_clos R e1 e3
    | eq_sym : forall e1 e2 : exp,
        eq_clos R e1 e2 -> eq_clos R e2 e1.

Notation "A =b B" := (eq_clos red_step A B) (at level 200).

Notation "A ->b B" := (red_step A B) (at level 200).