Require Import List.
Open Scope list_scope.

Lemma list_Forall_map : forall X Y (P : Y -> Prop) (f : X -> Y) l,
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
Admitted.

Lemma list_Exists_map : forall X Y (P : Y -> Prop) (f : X -> Y) l,
  Exists P (map f l) <-> Exists (fun x => P (f x)) l.
Proof.
Admitted.

Lemma list_Exists_Forall_and : forall X (P Q: X -> Prop) l,
    Exists P l ->
    Forall Q l ->
    Exists (fun x => P x /\ Q x) l.
Proof.
  intros X P Q l ex all.
  rewrite (Exists_exists P l) in ex. destruct ex as [x [x_in px]].
  rewrite Exists_exists. exists x.
  rewrite Forall_forall in all.
  split; [|split]; now auto.
Qed.
