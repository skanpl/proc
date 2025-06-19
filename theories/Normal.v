
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





 
Lemma iter_nu_cong: forall P Q R n,
  cong P (iter_nu n Q) -> cong (Par P R) (Par (iter_nu n Q) R).  
Proof.
intros. 
induction n; unfold iter_nu; eauto with picalc.
Qed.
 






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
asimpl.


rewrite bind_simpl.
eapply Cgb_nuPar.
eauto with picalc.



eapply Cg_cgb.
eauto with picalc.












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


(*
generalize dependent x.
intro. induction x.
firstorder.
simpl in *. 
repeat eexists.
eauto with picalc. eauto with picalc.
firstorder. simpl in *.
set (lem:= IHx H0 H1).
*)


repeat eexists.
apply Cg_ctxParL with (Q:=R) in H0.
induction x.  
simpl in *. 
eauto with picalc.
simpl in *. 

econstructor in  H0. eapply Cga_nuPar in H0. 



eapply Cg_sym in .



set (lem:= IHx  H1 H0).
eauto with picalc.

eapply Cg_ctxParL in H1.

*)
