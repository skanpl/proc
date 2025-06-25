Require Import ProcSyn.
Require Import Semantics.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.

Ltac fe := apply functional_extensionality.



(* autosubst problem (or maybe not):
induction htpotheses are too weak
and doesn't take into acount that 
a term is bellow a binder in the IH

Goal forall P:proc, P=P.
intro.
induction P.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.
*) 


Lemma shift_succ_comp: forall P n, 
  (shiftn_pr (n+1)  P) = shiftn_pr n (shift_pr P).
Proof.
intros. symmetry.
generalize dependent n.
induction P; intro; auto; simpl.

erewrite IHP1, IHP2. 
auto.

case c. intro.
simpl. 
erewrite IHP.
replace (n+S n0) with (n+1+n0); try lia.
auto.
 

unfold shift_pr.
simpl.
case c. intro.
case c0. intro.
cbn.
erewrite IHP.
replace (n+ S n0)with (n+1+n0) ;try lia.
replace (n+ S n1)with (n+1+n1) ;try lia.
auto.

erewrite IHP.
auto.
Qed.



Lemma shift_zero: forall P, shiftn_pr 0 P = P.
Proof.
intro. 
induction P; intros ;cbn; eauto with picalc.
erewrite IHP1, IHP2. auto.
case c. intro. erewrite IHP. auto.
case c. intro. case c0. intro. erewrite IHP. auto.
erewrite IHP. auto.
Qed.


Lemma iter_nu_scope_extr: forall n P Q,
  cong (Par (iter_nu n P) Q)   (iter_nu n (Par P (shiftn_pr n Q) )).
Proof. 
intros.
generalize dependent Q. 
induction n; intro; simpl.    
case Q;intros; cbn; eauto with picalc; try erewrite shift_zero.
erewrite shift_zero.
eauto with picalc.  
case c. eauto with picalc. 
case c. intro. case c0. eauto with picalc.
eauto with picalc.    

eapply Cg_trans.
eapply Cg_cgb. eapply Cgb_nuPar.
eapply Cg_ctxNu.
replace (S n) with (n+1); try lia.
erewrite shift_succ_comp.
eapply IHn.
Qed.


Lemma iter_nu_succ: forall x P, 
  Nu (iter_nu x P) = iter_nu (S x) P.
Proof.
intros.
induction x; auto.
Qed.
