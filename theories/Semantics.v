
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.







Notation ch := var_chan.
Notation up := up_chan_chan.



 
(* the assumed setting:
            Nu
            |
            Nu
            |
           /P\
*)


Definition swap (P:proc) := P [(ch 1) .: ( (ch 0) .:ids )  ].


(*==================================*)

Print proc.

 
Definition shiftn_sb n := fun x => ch (n+x). 
Definition shift_sb := shiftn_sb 1. 


(*
Definition emb (f:nat->nat) := fun x => ch (f x).


Fixpoint shiftn_pr n:= match n with
 | 0   => (fun x => ch x)
 | S n => S >>  (shiftn_pr n)
end.
*)





Inductive cong: proc -> proc -> Prop :=
| Cg_parCom: forall P Q,     cong (Par P Q)  (Par Q P)
| Cg_parAssoc: forall P Q R, cong (Par (Par P Q) R)    (Par P (Par Q R))
| Cg_parNeut: forall P,      cong (Par P Zero) P

| Cg_nuZero: cong (Nu Zero) Zero
| Cg_nuPar: forall P Q,  cong (Par (Nu P) Q)   (Nu (Par P (Q [shift_sb]) ))
| Cg_nuSwap: forall P, cong (Nu (Nu P))  (Nu (Nu (swap P)))

| Cg_refl: forall P,       cong P P
| Cg_sym: forall P Q,     cong Q P -> cong P Q
| Cg_trans: forall P Q R, cong P Q -> cong Q R -> cong P R
| Cg_ctxParL: forall P P' Q, cong P P' -> cong (Par P Q) (Par P' Q)  
| Cg_ctxParR: forall P Q Q', cong Q Q' -> cong (Par P Q) (Par P Q')
| Cg_ctxSend: forall x y P P', cong P P' -> cong (Send x y P) (Send x y P')
| Cg_ctxRcv: forall x P P', cong P P' -> cong (Rcv x P) (Rcv x P')
| Cg_ctxNu: forall P Q,    cong P Q -> cong (Nu P) (Nu Q)
.

(*===== peut etre temporaire ???  ======*)

Inductive lab :=
| Lsend (x y: chan)
| Lrcv (x y: chan)
| LbdSend (x: chan)
| Ltau 
.



Definition not_bdsend a :=
  a = Ltau \/ 
  (exists x y, a = Lsend x y) \/
  (exists x y, a = Lrcv x y)  
.




Definition notinlab a u := match a with
 | Ltau => Ltau = Ltau 
 | Lsend x y | Lrcv x y   => ~(u = x) /\ ~(u = y)
 | LbdSend x  => ~(u = x) /\ ~(u = ch 0)  (*this subtilety is needed i think...*)
 end. 

 


(*
maybe the Lt_res rule should be modified later?
*)
Inductive lt: proc -> lab -> proc -> Prop :=
| Lt_send: forall x y P, lt (Send x y P) (Lsend x y) P 
| Lt_rcv: forall x P y, lt (Rcv x P) (Lrcv x y) (P [y ..])
 
| Lt_parL: forall Q P P' a,  
  lt P a P' -> not_bdsend a -> 
    lt (Par P Q) a (Par P' Q) 
| Lt_parR: forall P Q Q' a,  
  lt Q a Q' -> not_bdsend a -> 
    lt (Par P Q) a (Par P Q')
| Lt_parL_bs: forall Q P P' x,  
  lt P (LbdSend x) P' -> 
    lt (Par P Q) (LbdSend x) (Par P' (Q[shift_sb] ) ) 
| Lt_parR_bs: forall P Q Q' x,  
  lt Q (LbdSend x) Q' -> 
    lt (Par P Q) (LbdSend x) (Par (P[shift_sb]) Q')

| Lt_commL: forall P Q P' Q' x y, 
  lt P (Lsend x y) P' -> lt Q (Lrcv x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' x y, 
  lt P (Lrcv x y) P' -> lt Q (Lsend x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')


| Lt_open: forall P P' x, 
  lt P (Lsend (ch x) (ch 0)) P' ->  x>0  -> 
     lt (Nu P) (LbdSend (ch x)) P'
| Lt_res: forall P P' a,  
   lt P a P' -> notinlab a (ch 0) -> 
     lt (Nu P) a (Nu P')

| Lt_closeL: forall P P' Q Q' x, 
  lt P (LbdSend x) P' -> lt (Q[shift_sb]) (Lrcv x (ch 0)) Q' -> 
    lt (Par P Q) Ltau (Nu (Par P' Q'))
    
| Lt_closeR: forall P P' Q Q' x, 
  lt (P[shift_sb]) (Lrcv x (ch 0)) P' -> lt Q (LbdSend x) Q' ->
    lt (Par P Q) Ltau (Nu (Par P' Q'))  
.
(*========================*)



Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P' [y..]) )
| Red_nu: forall P Q,    red P Q -> red (Nu P) (Nu Q)
.

 
Hint Constructors chan proc cong lab lt red: picalc. 

Fixpoint iter_nu n P := match n with
 | 0   => P
 | S n => Nu (iter_nu n P)
 end.



Lemma not_bdsend_rcv: forall x y, not_bdsend (Lrcv x y).
Proof. 
intros.  
cbv. right. right. eauto.
Qed.

Lemma not_bdsend_send: forall x y, not_bdsend (Lsend x y).
Proof.
intros.
cbv. right. left. eauto.
Qed.

Lemma not_bdsend_tau: not_bdsend (Ltau).
Proof.
cbv. auto. 
Qed.

 
Hint Resolve not_bdsend_rcv not_bdsend_send not_bdsend_tau: picalc. 








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
cbn. (*why does this work but not asimpl ????*)
eauto with picalc.
Qed.*)




 
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
firstorder.
inversion H; eauto with picalc.
inversion H; eauto with picalc.
(*========== case  assoc par  ==============================*)
(* LHS *)
firstorder.    
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
firstorder. 
inversion H; eauto with picalc.
inversion H2. inversion H4.
inversion H5. inversion H5.
cbn in *. inversion H5. 
inversion H5. 
    
(*RHS*) 
inversion H; eauto with picalc.
subst.
induction a; cbn in *; eauto with picalc.
(*==============  case NuZero    ======================================*)  
firstorder; inversion H; inversion H1.
(*==============  case NuPar    ======================================*) 
firstorder.    
inversion H; eauto with picalc. (*caseAn (Nu P)|Q -->a ... *)
subst.   
(*____ freeParL____*) 
inversion H2. (*caseAn Nu P -->a ... *)
   
subst. (*case Lt_open*)
firstorder; inversion H0. 
  
subst. (*case Lt_res*)
eexists. split.
eapply Lt_res.
eapply Lt_parL.
eauto with picalc.
eauto with picalc.
eauto with picalc.
eauto with picalc.
(*_____freeParR____*)
 
subst. 
eexists. split. 
eapply Lt_res. 
eapply Lt_parR.
(*found a problematic situation, 
which we dont find on paper*)












