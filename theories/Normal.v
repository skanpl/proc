
Require Import ProcSyn.
Require Import Semantics.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import Util.


(* ----------- some lemmas ---------------------------*)
Lemma conga_resp_sub: forall P Q sigma,
  conga P Q -> conga (P [sigma]) (Q [sigma]).
Proof.
intros.
inversion H; asimpl; eauto with picalc.
Qed.




(*
 
Lemma iter_nu_cong: forall P Q R n,
  cong P (iter_nu n Q) -> cong (Par P R) (Par (iter_nu n Q) R).  
Proof.
intros. 
induction n; unfold iter_nu; eauto with picalc.
Qed.
 
*)





(*--------------------------------------------------------*)




(*
Lemma cong_resp_sub: forall P Q sigma,
  cong P Q -> cong (P [sigma]) (Q [sigma]).
Proof.
intros. 
generalize dependent sigma.  
induction H; try(asimpl; eauto with picalc).
intro.
econstructor.
eauto using conga_resp_sub.
intro.
   
inversion H; eauto with picalc. 
subst.     
eapply Cg_cgb.
cbn.  
case Q0; intros; cbn; eauto with picalc.
*)



 





Lemma sc_extr_extd: forall x P R Q1 Q2, 
  cong P (iter_nu x (Par Q1 Q2)) -> 
  cong (Par P R) (iter_nu x (Par Q1 (Par Q2 (shiftn_pr x R))) ). 
Proof.
intros.
eapply Cg_trans.

eapply Cg_ctxParL.
apply H.

eapply Cg_trans.
eapply Cg_sym.

eauto with picalc.



(*
Lemma red_normal: forall P Q ,
  red P Q -> exists n S x y R1 R2 , 
     cong P  (iter_nu n  (Par  (Par (Send x y R1) (Rcv x R2))    S) ) 
     /\
     cong Q  (iter_nu n  (Par (Par R1 (R2 [y..])  )   S)) .
Proof.
intros.
induction H.   
firstorder. 
exists x. 
repeat eexists. 
*)
