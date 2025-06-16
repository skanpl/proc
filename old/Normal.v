
Require Import ProcSyn.
Require Import Semantics.
Require Import SubCompatible.
Import unscoped.UnscopedNotations.
Require Import CongLtLemma.

 
Lemma red_normal: forall P Q ,
  red P Q -> exists S x y R1 R2, 
     cong P  (Par  (Par (Send x y R1) (Rcv x R2))    S)   /\
     cong Q  (Par (Par R1 (R2 [y..])  )   S) .
Proof.
intros.
induction H. 
firstorder.
repeat eexists.
eauto with picalc.
eauto with picalc.

firstorder.
repeat eexists.
eauto with picalc.

eauto with picalc.
   
asimpl.
econstructor .
repeat eexists.
eauto with picalc.
eauto with picalc.
Qed.




Lemma ltsend_normal: forall Q Q' x y, 
  lt Q (Lsend x y)  Q' -> exists R S,  
    cong Q (Par (Send x y R) S) /\ 
    cong Q'(Par R S).
Proof.
intros.
generalize dependent Q'.
induction Q.
 
(*======Q Zero======*)
firstorder.
exfalso. inversion H.

(*======Q Par======*)
firstorder.
inversion H. (*caseAn on Q1|Q2 ->! ....*)
subst.
set (D := IHQ1 P' H4).
firstorder. 
repeat eexists.
eauto with picalc.
eauto with picalc.

subst.
set (D:= IHQ2 Q'0).
firstorder.
    
repeat eexists.  
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParR.
eapply H0.
econstructor.
eapply Cga_parCom.
econstructor.
eapply Cga_parAssoc.

eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParR.
eapply H1.
econstructor.
eapply Cga_parCom.
eauto with picalc .
(*======Q Rcv======*)
firstorder. 
exfalso. inversion H.  
(*======Q Send======*) 
firstorder.  
inversion H.
subst.
repeat eexists.
eauto with picalc.
eauto with picalc.
Qed.


 
Lemma ltrcv_normal: forall Q Q' x y,
  lt Q (Lrcv x y) Q' ->  exists R S,
    cong Q (Par (Rcv x R) S)  /\  
    cong Q' (Par (R[y..]) S) .
Proof.
intros.
generalize dependent Q'.
induction Q.

(*======Q Zero======*)
firstorder.
exfalso. inversion H.
(*======Q Par======*)
firstorder.
inversion H.  (*caseAn on Q1|Q2 --->? *)
subst.
set (D:= IHQ1 P' H4).
firstorder. 
repeat eexists.
eauto with picalc.
eauto with picalc.
 
subst.
set (D:= IHQ2 Q'0 H4).
firstorder.
repeat eexists. 
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParR.
eapply H0.
econstructor. eapply Cga_parCom.
econstructor. eapply Cga_parAssoc.

eapply Cg_trans.  
eapply Cg_trans.
eapply Cg_ctxParR.
eapply H1.
econstructor. eapply Cga_parCom.
econstructor. eapply Cga_parAssoc.

(*======Q Rcv======*) 
firstorder.
inversion H.
subst. 
repeat eexists.
eauto with picalc.
eauto with picalc.
(*======Q Send======*)
firstorder.  
exfalso. inversion H.
Qed.














