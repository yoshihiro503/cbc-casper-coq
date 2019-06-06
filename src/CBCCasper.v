(**
   see https://github.com/cbc-casper/cbc-casper-paper/blob/master/cbc-casper-paper-draft.pdf
 *)

Require Import Classical.

Variable set : Set -> Set.
Variable union : forall {E: Set}, set E -> set E -> set E.
Variable incl : forall {E: Set}, set E -> set E -> Prop.
Axiom incl_union_l : forall {E: Set} (A B: set E), incl A (union A B).
Axiom incl_union_r : forall {E: Set} (A B: set E), incl B (union A B).

(*Variable number : Set.*)
Definition number := nat.

Variable validator : Set.
Variable V : set validator.
Variable t : number.

Variable message : Set.
Definition State := set message.

Inductive Transition : State -> State -> Prop :=
| Trans : forall state1 state2, incl state1 state2 -> Transition state1 state2.

Variable F : State -> number.
Definition Sigma_t state := F state <= t.

(** * Safety Proof *)

Inductive Future : State -> State -> Prop :=
| FutureBase : forall state, Sigma_t state -> Future state state
| FutureTrans : forall state state',
    Sigma_t state -> Sigma_t state' -> Transition state state' -> Future state state' .

(** Theorem 1 *)
Theorem two_party_common_futures :
  forall state1 state2,
    Sigma_t state1 ->
    Sigma_t state2 ->
    F (union state1 state2) <= t ->
    exists state, Future state1 state /\ Future state2 state.
Proof.
  intros state1 state2 sigma1 sigma2 le_f.
  exists (union state1 state2). split.
  - apply FutureTrans; auto.
    apply Trans, incl_union_l.
  - apply FutureTrans; auto.
    apply Trans, incl_union_r.
Qed.

(** lemma 1 *)
Lemma monotonic_futures : forall state state',
    Sigma_t state ->
    Sigma_t state' ->
    Future state state' <-> (forall s, Future state' s -> Future state s).
Proof.
Admitted.

Definition Decided (p: State -> Prop) state : Prop := forall state', Future state state' -> p state'.

Definition neg {A : Type} (P: A -> Prop) := fun x => ~P x.

(** Lemma 2 *)
Lemma forward_consistency : forall state state' p,
    Sigma_t state ->
    Sigma_t state' ->
    Future state state' ->
    Decided p state -> Decided p state'.
Proof.
  intros state state' p sigma1 sigma2 fut dec.
  intros state'' fut''.
  rewrite monotonic_futures in fut; auto.
Qed.

(** Lemma 3 *)
Lemma backward_consistency : forall state state' p,
    Sigma_t state ->
    Sigma_t state' ->
    Future state state' ->
    Decided p state' -> ~Decided (neg p) state.
Proof.
  intros state state' p sigma1 sigma2 fut dec.
  apply ex_not_not_all.
  unfold Decided in dec.
  exists state'. intro H. elim H; auto.
  apply dec; now constructor.
Qed.


  (** Theorem 3 *)
Theorem two_party_consensus_safety : forall state1 state2 p,
    Sigma_t state1 ->
    Sigma_t state2 ->
    F (union state1 state2) <= t ->
    ~ (Decided p state1 /\ Decided (neg p) state2).
Proof.
  intros state1 state2 p sigma1 sigma2 le_f.
  destruct (two_party_common_futures state1 state2) as [s [fut1 fut2]]; auto.
  apply or_not_and, imply_to_or.
  intros dec1.
  cut (Sigma_t s); [|inversion fut2; auto]. intro sigma_s.
  apply (backward_consistency state2 s) with (p := p); auto.
  apply (forward_consistency state1 s) with (p := p); auto.
Qed.
