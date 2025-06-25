Require Import ProcSyn.
Require Import Semantics.
Require Import SubCompatible.
Import unscoped.UnscopedNotations.
Require Import CongLtLemma.
Require Import Normal.




Theorem lttau_impl_red: forall P Q,
  lt P Ltau Q -> red P Q.
Proof.
intros. 
generalize dependent Q.
induction P.

(*======P Zero======*)
firstorder. 
exfalso. inversion H.
(*======P Par======*)
firstorder.  
inversion H. (*caseAn on P1|P2--->tau ...*)  

eauto with picalc.

subst.
set (D:= IHP2 Q' H4).
eauto with picalc.

 
subst.
set (rnl := ltrcv_normal P2 Q' x y H3).
set (snl := ltsend_normal P1 P' x y H2).
firstorder.
(*the derivation tree*)
eapply Red_struc.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParL.
eapply H0.
eapply Cg_ctxParR.
eapply H4.
econstructor. eapply Cga_parAssoc.
eapply Cg_ctxParR. 
econstructor. eapply Cga_parCom.
eapply Cg_sym. 
econstructor. eapply Cga_parAssoc. 
eapply Cg_ctxParL.  
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.

eapply Red_par.
eapply Red_par.
eapply Red_comm.

eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParL.
eapply H1.
eapply Cg_ctxParR.
eapply H5.
econstructor. eapply Cga_parAssoc.
eapply Cg_ctxParR.
econstructor. eapply Cga_parCom.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
eapply Cg_ctxParL.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
 
(*the other one*)
subst.
set (snl := ltsend_normal P2 Q' x y H3).
set (rnl := ltrcv_normal P1 P' x y H2).
firstorder. 
eapply Red_struc.

eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_ctxParL.
eapply H0.
eapply Cg_ctxParR.
eapply H4.
econstructor. eapply Cga_parAssoc.
eapply Cg_ctxParR.
econstructor. eapply Cga_parCom.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
eapply Cg_ctxParL.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
  
eapply Red_par.
eapply Red_par.
eapply Red_struc. 
econstructor. eapply Cga_parCom.
eapply Red_comm.
eapply Cg_refl.

eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.
eapply Cg_trans.

eapply Cg_ctxParL.
eapply H1.
eapply Cg_ctxParR.
eapply H5.
econstructor. eapply Cga_parCom.
econstructor. eapply Cga_parAssoc.

eapply Cg_ctxParR.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.

eapply Cg_ctxParR.
eapply Cg_ctxParL.
econstructor. eapply Cga_parCom.

eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
  
eapply Cg_ctxParL.
eapply Cg_sym.
econstructor. eapply Cga_parAssoc.
 
eapply Cg_refl.
(*======case Q Rcv======*)
firstorder.
exfalso. inversion H.
(*======case Q Send======*)
firstorder.
exfalso. inversion H.
Qed.




Theorem red_impl_lt: forall P Q, red P Q -> 
  exists Q', lt P Ltau Q' /\ cong Q Q'.
Proof.
intros.
set (lem:= red_normal P Q). 
 
firstorder. 
assert(
lt
(Par (Par (Send x0 x1 x2) (Rcv x0 x3)) x)
Ltau
(Par (Par x2 x3[x1..]) x)
).
apply Lt_parL.
eapply Lt_commL.
eapply Lt_send.
eapply Lt_rcv.
set (lem:= cong_resp_lt (Par (Par (Send x0 x1 x2) (Rcv x0 x3)) x) P (Par (Par x2 x3[x1..]) x) Q Ltau).
eapply Cg_sym in H0.
firstorder.
eexists. split. 
eauto with picalc .
eapply Cg_trans.
eauto with picalc .
auto with picalc .
Qed.

