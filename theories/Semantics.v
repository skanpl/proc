
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






Inductive conga: proc -> proc -> Prop :=
| Cga_parCom: forall P Q,     conga (Par P Q)  (Par Q P)
| Cga_parAssoc: forall P Q R, conga (Par (Par P Q) R)    (Par P (Par Q R))
| Cga_parNeut: forall P,      conga (Par P Zero) P

| Cgb_nuZero: conga (Nu Zero) Zero
| Cgb_nuPar: forall P Q,  conga (Par (Nu P) Q)   (Nu (Par P (Q [shift_sb]) ))
| Cgb_nuSwap: forall P, conga (Nu (Nu P))  (Nu (Nu (swap P)))
.






(*  cong = conga + equivrel + ctxrules *)
Inductive cong: proc -> proc -> Prop :=
| Cg_cga: forall P Q,     conga P Q -> cong P Q
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
| LbdSend (x y: chan)
| Ltau 
.



Definition not_bdsend a :=
  a = Ltau \/ 
  (exists x y, a = Lsend x y) \/
  (exists x y, a = Lrcv x y)  
.

Definition notinlab a u := 
  a = Ltau \/
  forall x y, 
  (a = Lsend x y -> ~(u = x) /\ ~(u = y) )   /\
  (a = Lrcv x y -> ~(u = x) /\ ~(u = y) )    /\
  (a = LbdSend x y -> ~(u = x) /\ ~(u = y) ) .



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
  lt P (LbdSend x (ch 0)) P' -> 
    lt (Par P Q) (LbdSend x (ch 0)) (Par P' (Q[shift_sb] ) ) 
| Lt_parR_bs: forall P Q Q' x,  
  lt Q (LbdSend x (ch 0)) Q' -> 
    lt (Par P Q) (LbdSend x (ch 0)) (Par (P[shift_sb]) Q')

| Lt_commL: forall P Q P' Q' x y, 
  lt P (Lsend x y) P' -> lt Q (Lrcv x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' x y, 
  lt P (Lrcv x y) P' -> lt Q (Lsend x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')


| Lt_open: forall P P' x, 
  lt P (Lsend (ch x) (ch 0)) P' ->  x>0  -> 
     lt (Nu P) (LbdSend (ch x) (ch 0)) P'
| Lt_res: forall P P' a,  
   lt P a P' -> notinlab a (ch 0) -> 
     lt (Nu P) a (Nu P')

| Lt_closeL: forall P P' Q Q' x, 
  lt P (LbdSend x (ch 0)) P' -> lt (Q[shift_sb]) (Lrcv x (ch 0)) Q' -> 
    lt (Par P Q) Ltau (Nu (Par P' Q'))
    
| Lt_closeR: forall P P' Q Q' x, 
  lt (P[shift_sb]) (Lrcv x (ch 0)) P' -> lt Q (LbdSend x (ch 0)) Q' ->
    lt (Par P Q) Ltau (Nu (Par P' Q'))  
.
(*========================*)



Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P' [y..]) )
| Red_nu: forall P Q,    red P Q -> red (Nu P) (Nu Q)
.

 
Hint Constructors chan proc conga cong lab lt red: picalc. 

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




Lemma Lconga_resp_lt: forall P Q P' a, 
  lt P a P'-> conga P Q -> exists Q', lt Q a Q' /\ conga P' Q'.
Proof.
intros. 
inversion H. (*caseAn on P -->a  P' *)
(*====== base cases ======*)  
subst. inversion H0.
subst. inversion H0.
(*====== free parL ======*)
subst. 
inversion H0. (*caseAn on conga*)

(* case commut*)
subst.
eexists. split.
eauto with picalc.
eauto with picalc.

(*case assoc*)
subst.     
inversion H1; eauto with picalc. (* caseAn on P|Q1 -->a P'0 *) 
eexists. split. eauto with picalc.
subst.  
firstorder; inversion H2.
 
eexists. split. eauto with picalc. 
subst. 
firstorder; inversion H2.   
 
subst.    
eexists. split. 
eapply Lt_closeL. eauto with picalc.
cbn.  
eapply Lt_parL.
eauto with picalc. 
eauto with picalc.
eauto with picalc.

(* goal: (seems impossible without transitivvity ...)
the reasonable way would be to do "sc_extr+assoc"
     (Nu (P'|Q')) | Q0
       conga
     Nu (  P'| (Q'|Q0[shift])   )
*)















