Require Export Semantics.
Require Export SubLem.

Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.micromega.Lia.






(*------------------ rule extensions ----------------------------------*)
Proposition sc_extr_n: forall n P Q,
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

Proposition nuN_ctx: forall P Q n, 
  cong P Q -> cong (iter_nu n P) (iter_nu n Q).
Proof.
intros P Q n.
induction n; intros; eauto with picalc; simpl.
eauto with picalc.
Qed.

Proposition nuN_zero: forall n, 
  cong (iter_nu n Zero) Zero.
Proof.
intro. 
induction n; simpl; eauto with picalc.
Qed.

Hint Resolve nuN_zero sc_extr_n nuN_ctx: picalc.
(*----------------- misc  ------------------------------*)

Lemma inact_nuN: forall n P,
  cong (iter_nu n (Par P Zero)) (iter_nu n P). 
Proof.
intro. induction n; eauto with picalc.
Qed.

Lemma down_bdsend: forall a x , down a = LbdSend x -> 
  exists x', a = LbdSend x'.
Proof. 
intros.
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.
(*-----------------------------------------------------*)


Lemma red_normal: forall P Q ,
  red P Q -> exists n S x y R1 R2 , 
    cong P  (iter_nu n  (Par  (Par (Send x y R1) (Rcv x R2))    S) ) 
     /\
    cong Q  (iter_nu n  (Par (Par R1 (R2 [y..])  )   S)) .
Proof.
intros.
induction H; firstorder.
- (*how do you factor this out?*)
  exists x. repeat eexists.  
  eapply Cg_trans. 
  eapply Cg_trans. 
  eapply Cg_ctxParL. apply H0. 
  eapply sc_extr_n.
  eapply nuN_ctx.
  eapply Cg_parAssoc.

  eapply Cg_trans. 
  eapply Cg_trans. 
  eapply Cg_ctxParL. apply H1. 
  eapply sc_extr_n.
  eapply nuN_ctx. 
  eapply Cg_parAssoc.

- exists x. repeat eexists.  
  eauto with picalc. eauto with picalc.

- exists 0. repeat eexists. simpl.
  eauto with picalc. eauto with picalc.

- exists (S x). repeat eexists. simpl.  
  eauto with picalc. eauto with picalc.
Qed.



Lemma ltsend_normal: forall Q Q' x y n, 
  lt Q (Lsend x y)  Q' -> exists R S,  
    cong Q (iter_nu n (Par (Send x y R) S) ) /\ 
    cong Q' (iter_nu n (Par R S) ).
Proof.
intros.
generalize dependent Q'.
induction Q; intros.

- inversion H.
  
- inversion H; subst.   
  + destruct (IHQ1 P'). auto. 
    do 2 destruct H0.  
    repeat eexists. 
    eauto with picalc.  
    eauto with picalc.
 
  + destruct (IHQ2 Q'0). auto.
    do 2 destruct H0.
    repeat eexists.
    eapply Cg_trans. 
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H0.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
    
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_trans.
    eapply Cg_ctxParR. apply H1.
    eapply Cg_parCom.
	eapply sc_extr_n. eauto with picalc.
        
- inversion H.
  
- inversion H. subst.
  exists Q', Zero. split.
  induction n; simpl in *; eauto with picalc.  
  (*euuuhhh*) 





