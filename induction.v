(* Peano numerals *)
Inductive my_nat : Type :=
  | Z
  | S (n : my_nat).

(* Recursive definition of sum *)
Fixpoint my_sum n m := match n with
  | Z => m
  | S (n') => S(my_sum n' m) 
end.

(* Notation can be defined to make proofs more readable *)
Notation "0" := (Z).
Notation "A .+ B" := (my_sum A B) (at level 50).

(* Recursive definition of multiplication *)
Fixpoint my_mult n m := match n with
  | Z => Z
  | S (n') => (my_mult n' m) .+ m
end.

(* Check is used to view the type of a term *)
Check my_mult.

Notation "A .* B" := (my_mult A B) (at level 50).

(* Our first theorem *)
Theorem add_0_r : forall n : my_nat,
    n .+ 0 = n.
Proof.
    (* We proceed by induction. This creates two subgoals. *)
    induction n.
    -   (* Base case: n = 0 *)
        unfold my_sum.
        reflexivity.
    -   (* Inductive case *)
        unfold my_sum.
        fold my_sum.
        rewrite IHn.
        reflexivity.
Qed.

Check add_0_r.


(* From now on, we use the simpl tactic       *)
(* Reduces a term to something still readable *)
(* instead of fully normalizing it.           *)

Theorem mul_0_r : forall n : my_nat,
  n .* 0 = 0.
Proof.
    induction n.
    -   simpl.
        reflexivity.
    -   simpl.
        rewrite IHn.
        simpl.
        reflexivity.
Qed.

(* Solutions to Exercises *)

Theorem plus_n_Sm : forall n m : my_nat,
  S (n .+ m) = n .+ (S m).
Proof.
induction n.
-   intro.
    simpl.
    reflexivity.
-   intro.
    simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_comm : forall n m : my_nat,
  n .+ m = m .+ n.
Proof.
    induction n.
    - intro.
      simpl.
      symmetry.
      apply add_0_r.
    - intro.
      simpl.
      specialize (IHn m).
      rewrite IHn.
      apply plus_n_Sm.
Qed.

Theorem add_assoc : forall n m p : my_nat,
  n .+ (m .+ p) = (n .+ m) .+ p.
Proof.
  induction n.
  - simpl.
    intros.
    reflexivity.
  - intros.
    simpl.
    specialize (IHn m p).
    rewrite IHn.
    reflexivity.
Qed.
