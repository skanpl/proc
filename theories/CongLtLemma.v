Require Import Semantics.
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.







 (*
Lemma lt_assocR: forall P Q R P0 a, 
  lt (Par P Q) a P0 -> 
  exists Q0, lt (Par P (Par Q R)) a Q0.
Proof.
intros.  
inversion H; eauto with picalc.
subst. 
eexists.
eapply Lt_closeL.
eauto with picalc.
cbn. 
eauto with picalc.
Qed.*)




Lemma extr_rl_assoc: forall P Q R, 
  cong (Nu (Par (Par P[shift_sb] Q)  R) )  (Par P (Nu (Par Q R))).
Proof.
intros.
eapply Cg_sym.
eapply Cg_trans.

eapply Cg_trans.
eapply Cg_parCom.
eapply Cg_nuPar.

eapply Cg_ctxNu.
eapply Cg_trans.
eapply Cg_parCom.
eapply Cg_sym.
eapply Cg_parAssoc.
Qed.






 
Lemma cong_resp_lt: forall P Q P' Q' a, 
  cong P Q -> 
     (lt P a P'  -> exists Q0, lt Q a Q0 /\ cong P' Q0)  /\
      (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof.
intros. 
generalize dependent P'.
generalize dependent Q'.
generalize dependent a. 
induction H.      
  
(*=========case commutative par ===================*)
- firstorder.
inversion H; eauto with picalc.
inversion H; eauto with picalc.
(*========== case  assoc par  ==============================*)
(* LHS *)
- firstorder.    
inversion H; try eauto with picalc. (*caseAn on (P|Q)|R-->a ...*)
subst.
   
(**)  
inversion H2; subst; eauto with picalc. (*caseAn on P|Q -->a ...*)

firstorder; inversion H0.

eexists. split.
eapply Lt_closeL.
eauto with picalc.
cbn. 
eauto with picalc.
eauto with picalc.
 
eexists. split.
eauto with picalc.
eauto with picalc.
(**)
        
(**)
inversion H4; subst. (*caseAn P|Q -->a ...*)
firstorder; inversion H0.
firstorder; inversion H0.

eauto with picalc.
eauto with picalc.
(**)

eexists; split; eauto with picalc.
 
inversion H2; eauto with picalc.
 
inversion H2; eauto with picalc.

(*******)
inversion H2; eauto with picalc. (*casAn P|Q -->a ...*)
subst; firstorder; inversion H0.
subst; firstorder; inversion H0.

subst.
eexists. split.
eapply Lt_closeL.
eauto with picalc. 
cbn. eauto with picalc.
eauto with picalc.

subst. 
eexists. split.
eauto with picalc.
eauto with picalc.
eapply extr_rl_assoc.
(******)
   
subst.
cbn in *.
inversion H2; subst.
eexists. split. 
eapply Lt_closeR.
eauto with picalc.
eauto with picalc.
eauto with picalc.

eexists. split. 
eauto with picalc. 
eapply extr_rl_assoc.  
(* assoc RHS *)  
inversion H; eauto with picalc. (*caseAn P|(Q|R) --->a ...*)
subst.
  
    
(*___*)
inversion H2; eauto with picalc. (*caseAn Q|R --->a ...*) (*gen 4 new goals *)

subst; eauto with picalc.
  
subst; firstorder; inversion H0.

subst.
eexists. split. 
eapply Lt_closeL.
eauto with picalc.  
eauto with picalc. 
eapply extr_rl_assoc.

subst.
eexists. split.
eapply Lt_closeR.
cbn. 
eauto with picalc. 
eauto with picalc.
eapply extr_rl_assoc. 
(*__________*)

(*___*)  
subst.    
inversion H4; eauto with picalc.  (*caseAn Q|R  -->a ...*)
subst.     
firstorder; inversion H0.
subst.
  
eexists. split.
eauto with picalc. 
cbn.
eauto with picalc.
(*___*)

    
inversion H5; eauto with picalc.

inversion H5; eauto with picalc.

(*__*)
subst. cbn in *.   
inversion H5; eauto with picalc. (*caseAn Q[shift]|R[shift] -->? ...*) 
subst.
eexists; split; eauto with picalc. 
eexists; split; eauto with picalc.
(*__*)


(*__*)
subst.
inversion H5; eauto with picalc. (*caseAn Q|R -->b! ...*)
firstorder; inversion H7.
firstorder; inversion H7.

subst.
eexists; split; eauto with picalc. 

subst.
eexists. split. 
eapply Lt_closeR.
cbn.
eauto with picalc.
eauto with picalc. 
eauto with picalc.
(*==============  case neut    ======================================*)
(*LHS*) 
- firstorder. 
inversion H; eauto with picalc.
inversion H2. inversion H4.
inversion H5. inversion H5.
cbn in *. inversion H5.  
inversion H5. 
       
(*RHS*)  
destruct a; cbn in *; try destruct c, c0; eauto with picalc.
(*destruct c. eauto with picalc.*) 
(*==============  case NuZero    ======================================*)  
- firstorder; inversion H; inversion H1.
(*==============  case NuPar    ======================================*) 
- firstorder.    
 + inversion H;  eauto with picalc; subst. (*caseAn (Nu P)|Q -->a ... *)
  * 
(*____ freeParL____*) 
inversion H2. (*caseAn Nu P -->a ... *)
    
subst. (*case Lt_open*)
firstorder; inversion H0. 
  
subst. (*case Lt_res*)
eexists. split.
eapply Lt_res.
eapply Lt_parL.
eauto with picalc.   

eauto using not_bdsend_down. 
eauto with picalc.
eauto with picalc.
eauto with picalc.
(*_____freeParR____*)
 
 *
eexists. split. 
eapply Lt_res. 
eapply Lt_parR.





