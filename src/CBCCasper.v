(**
   see https://github.com/cbc-casper/cbc-casper-paper/blob/master/cbc-casper-paper-draft.pdf
 *)

Require Import Classical List.

Definition list_pred_union {A:Type} (ps: list (A -> Prop)) : A -> Prop := fun x => List.Exists (fun p => p x) ps.

Variable set : Set -> Set.
Variable empty_set : forall {A:Set}, set A.
Variable union : forall {E: Set}, set E -> set E -> set E.
Definition unions {A: Set} (xss : list (set A)) :=
  List.fold_right (fun x acc => union x acc) empty_set xss.

Variable incl : forall {E: Set}, set E -> set E -> Prop.
Axiom incl_union_l : forall {E: Set} (A B: set E), incl A (union A B).
Axiom incl_union_r : forall {E: Set} (A B: set E), incl B (union A B).
Axiom incl_refl : forall {E: Set} (A: set E), incl A A.
Axiom incl_trans : forall {E: Set} (A B C: set E), incl A B -> incl B C -> incl A C.


(*Variable number : Set.*)
Definition number := nat.

Variable validator : Set.
Variable V : set validator.
Variable t : number.
Variable C : Set.

Variable message : Set.
Definition State := set message.

Variable Eps : State -> C -> Prop.

Inductive Transition : State -> State -> Prop :=
| Trans : forall state1 state2, incl state1 state2 -> Transition state1 state2.

Lemma Transition_refl : forall s, Transition s s.
Proof.
  intros s. apply Trans, incl_refl.
Qed.

Lemma Transition_trans : forall s1 s2 s3,
    Transition s1 s2 -> Transition s2 s3 -> Transition s1 s3.
Proof.
  intros s1 s2 s3 tr1 tr2.
  inversion tr1 as [x y incl1]. clear x y H H0.
  inversion tr2 as [x y incl2]. clear x y H H0.
  now apply Trans, incl_trans with (B := s2).
Qed.

Variable F : State -> number.
Definition Sigma_t state := F state <= t.

(** * Safety Proof *)

Inductive Future : State -> State -> Prop :=
| FutureTrans : forall state state',
    Sigma_t state -> Sigma_t state' -> Transition state state' -> Future state state' .

Lemma Future_refl : forall s,
    Sigma_t s -> Future s s.
Proof.
  intros s sigma. apply FutureTrans; auto.
  now apply Transition_refl.
Qed.

Lemma Future_trans : forall s1 s2 s3,
    Future s1 s2 -> Future s2 s3 -> Future s1 s3.
Proof.
  intros s1 s2 s3 fut1 fut2.
  inversion fut1 as [x y sigma1 sigma2 trans1]. clear x y H H0.
  inversion fut2 as [x y _ sigma3 trans2]. clear x y H H0.
  apply FutureTrans; auto.
  now apply Transition_trans with (s2 := s2).
Qed.

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
  intros state state' sigma sigma'.
  split.
  - intros fut s fut0.
    apply Future_trans with (s2 := state'); auto.
  - intros impl. apply impl.
    now apply Future_refl.
Qed.

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
  apply dec. now apply Future_refl.
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

(** Definition 3.5 *)
Definition Consistent (Q : (State -> Prop) -> Prop) :=
  exists state, forall q, Q q -> q state.

(** Definition 3.6 *)
Definition Decisions state p := Decided p state.

(** Theorem 4 *)
Theorem n_party_consensus_safety_for_properties_of_protocol_states :
  forall states,
    List.Forall Sigma_t states ->
    F (unions states) <= t -> Consistent (list_pred_union (List.map Decisions states)).
Proof.
Admitted.
