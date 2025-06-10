
Require Import ProcSyn.
Require Import Semantics.
Import unscoped.UnscopedNotations.




Lemma conga_resp_sub: forall P Q sigma,
  conga P Q -> conga (P [sigma]) (Q [sigma]).
Proof.
intros.
inversion H; asimpl; eauto with picalc.
Qed.

Lemma cong_resp_sub: forall P Q sigma,
  cong P Q -> cong (P [sigma]) (Q [sigma]).
Proof.
intros.
generalize dependent sigma.
induction H; try(asimpl; eauto with picalc).
intro.
set ( D := conga_resp_sub P Q sigma H).
eauto with picalc.
Qed.

Hint Resolve cong_resp_sub: sublem.
