Require Export Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.



Notation ch x := x __chan.


Lemma shift_succ: forall n, 
  shift_sb >> subst_chan (shiftn_sb n) = shiftn_sb (S n).
Proof.
intros.
unfold shift_sb, shiftn_sb.
unfold funcomp. cbn. fe. intro.
replace (n+ S x) with (S(n+x)); try lia; auto.
Qed.

Lemma shift_succ_pr: forall n (P:proc), 
  P [shift_sb][shiftn_sb n] = P[shiftn_sb (S n)].
Proof.
intros. asimpl. auto. erewrite shift_succ. auto.
Qed.

Lemma shift_permute_pr: forall (sigma: nat->chan) (P:proc),
  P[shift_sb][up sigma] = P[sigma][shift_sb].
Proof.
intros. asimpl. auto.
Qed.






Lemma sc_extr_n: forall n P Q,
  cong (Par (iter_nu n P) Q)   (iter_nu n (Par P (Q[shiftn_sb n ]) )).
Proof.
intro n. induction n; intros. 
asimpl. eauto with picalc.

unfold shiftn_sb. simpl.
assert(
(fun x : nat => ch (S (n + x)) )=
fun x : nat => ch ((n+1)+x)
). fe. intro. 
replace (S (n+x)) with ((n+1)+x); try lia; auto.
rewrite H. replace (n+1) with (S n); try lia; auto.
replace (fun x : nat => ch (S n + x)) with (shiftn_sb (S n)); auto.

eapply Cg_trans.
eapply Cg_nuPar.
eapply Cg_trans. 
eapply Cg_trans.
eapply Cg_ctxNu. 
eapply (IHn P (Q[shift_sb])). 
erewrite shift_succ_pr. eapply Cg_refl.
eauto with picalc.
Qed.


Definition swap_sb2 x := match x with
 | 0 => ch 1
 | 1 => ch 0
 | _ => ch x
end.

Axiom skip: forall A, A.


Lemma sub_comp_pr: forall (P:proc) (sigma1 sigma2: nat -> chan), 
  P[sigma1][sigma2] = P [sigma1 >> subst_chan sigma2].
Proof.  
asimpl. auto.
Qed.




Lemma swap_up_up: forall sigma, 
  swap_sb >> subst_chan (up (up sigma)) = up (up sigma) >> subst_chan swap_sb.
Proof.
intros. unfold swap_sb, funcomp.
fe. intro. destruct x. auto.
cbn. asimpl. cbv. destruct x; auto. 
destruct (sigma x); auto.
Qed.

Lemma swap_up_up_pr: forall (P:proc) sigma, 
  P[swap_sb][up (up sigma)] = P [up (up sigma)][swap_sb].
Proof.  
intros.
do 2 (erewrite sub_comp_pr).
erewrite swap_up_up. auto.
Qed.
 



Lemma cong_sb: forall P Q sigma,
  cong P Q -> cong P[sigma] Q[sigma].
Proof.
intros. generalize dependent sigma.
induction H; intros; cbn in *; eauto with picalc.
erewrite shift_permute_pr. eauto with picalc.
erewrite swap_up_up_pr. eauto with picalc.
Qed.




