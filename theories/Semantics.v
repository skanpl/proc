Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.



Ltac fe := eapply functional_extensionality.


Notation ch := var_chan.
Notation up := up_chan_chan.
 


Fixpoint iter_nu n P := match n with
 | 0   => P
 | S n => Nu (iter_nu n P)
 end.


(*-------- shifts and swap ---------------------*)

Definition shiftn_sb n := fun x => ch (n+x). 
Definition shift_sb := shiftn_sb 1. 


(* the assumed setting:
            Nu
            |
            Nu
            |
           /P\
 *)
Definition swap_sb :=  (ch 1) .: ( (ch 0) .:(shiftn_sb 2) ). (* --> 1.0.SS *)

Proposition swap_def: swap_sb 0 = ch 1 /\ swap_sb 1 = ch 0 /\ 
  forall n, n> 1 -> swap_sb n = ch n.
Proof. 
split; auto.
split; auto.
intros.  
unfold swap_sb. unfold shiftn_sb.
simpl. cbv. 
destruct n; inversion H; auto.
destruct n; inversion H1; auto.
Qed.

(* ------ some functions for the LTS -----------*)
Definition not_bdsend a :=
  a = Ltau \/ 
  (exists x y, a = Lsend x y) \/
  (exists x y, a = Lrcv x y)  
.


Definition notinlab a u := match a with
 | Ltau => True
 | Lsend x y | Lrcv x y   => ~(u = x) /\ ~(u = y)
 | LbdSend x  => ~(u = x)
 end. 


Definition down (a:lab) := a[fun x => ch (x-1)].
(*-----------------------------------------------*)




Inductive cong: proc -> proc -> Prop :=
| Cg_parCom: forall P Q,     cong (Par P Q)  (Par Q P)
| Cg_parAssoc: forall P Q R, cong (Par (Par P Q) R)    (Par P (Par Q R))
| Cg_parNeut: forall P,      cong (Par P Zero) P

| Cg_nuZero: cong (Nu Zero) Zero
| Cg_nuPar: forall P Q,  cong (Par (Nu P) Q)   (Nu (Par P (Q [shift_sb]) ))
| Cg_nuSwap: forall P, cong (Nu (Nu P))  (Nu (Nu (P[swap_sb])))

| Cg_refl: forall P,       cong P P
| Cg_sym: forall P Q,     cong Q P -> cong P Q
| Cg_trans: forall P Q R, cong P Q -> cong Q R -> cong P R
| Cg_ctxParL: forall P P' Q, cong P P' -> cong (Par P Q) (Par P' Q)  
| Cg_ctxParR: forall P Q Q', cong Q Q' -> cong (Par P Q) (Par P Q')
| Cg_ctxSend: forall x y P P', cong P P' -> cong (Send x y P) (Send x y P')
| Cg_ctxRcv: forall x P P', cong P P' -> cong (Rcv x P) (Rcv x P')
| Cg_ctxNu: forall P Q,    cong P Q -> cong (Nu P) (Nu Q)
.


Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P' [y..]) )
| Red_nu: forall P Q,    red P Q -> red (Nu P) (Nu Q)
.


Inductive lt: proc -> lab -> proc -> Prop :=
| Lt_send: forall x y P, lt (Send x y P) (Lsend x y) P 
| Lt_rcv: forall x P y, lt (Rcv x P) (Lrcv x y) (P [y ..])
 
| Lt_parL: forall Q P P' a,  
  lt P a P' -> not_bdsend a -> 
    lt (Par P Q) a (Par P' Q) 
| Lt_parR: forall P Q Q' a,  
  lt Q a Q' -> not_bdsend a -> 
    lt (Par P Q) a (Par P Q')
| Lt_parL_bs: forall Q P P' Q' x,  
  lt P (LbdSend x) P' -> Q'= Q[shift_sb] ->
    lt (Par P Q) (LbdSend x) (Par P' Q' ) 
| Lt_parR_bs: forall P Q Q' P' x,  
  lt Q (LbdSend x) Q' -> P'= P[shift_sb] ->
    lt (Par P Q) (LbdSend x) (Par P' Q')

| Lt_commL: forall P Q P' Q' x y, 
  lt P (Lsend x y) P' -> lt Q (Lrcv x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' x y, 
  lt P (Lrcv x y) P' -> lt Q (Lsend x y) Q' -> 
    lt (Par P Q) Ltau (Par P' Q')


(*
| Lt_open: forall P P' x, 
  lt P (Lsend x (ch 0)) P'-> 
     lt (Nu P) (LbdSend x) P'

| Lt_res: forall P P' a,  
   lt P a[shift_sb] P' -> not_bdsend a -> 
     lt (Nu P) a (Nu P')
*)


| Lt_open: forall P P' x ad, 
  lt P (Lsend x (ch 0)) P' -> x <> ch 0 -> ad = down (LbdSend x) ->
     lt (Nu P) ad P'

(* distinguer 2 cas, suivant émission liée ou pas, ajouter le swap dans le cas d'une émission liée *)

| Lt_res: forall P P' a ad,  
   lt P a P' -> notinlab a (ch 0) -> not_bdsend a -> ad = down a -> 
     lt (Nu P) ad (Nu P')

| Lt_res_bd: forall P P' x ad,  
   lt P (LbdSend x) P' -> x <> ch 0 -> ad = down (LbdSend x) -> 
     lt (Nu P) ad (Nu P'[swap_sb])


| Lt_closeL: forall P P' Q Q' x, 
  lt P (LbdSend x) P' -> lt (Q[shift_sb]) (Lrcv x (ch 0)) Q' -> 
    lt (Par P Q) Ltau (Nu (Par P' Q'))
    
| Lt_closeR: forall P P' Q Q' x, 
  lt (P[shift_sb]) (Lrcv x (ch 0)) P' -> lt Q (LbdSend x) Q' ->
    lt (Par P Q) Ltau (Nu (Par P' Q'))  
.




 
Hint Constructors chan proc cong lab lt red: picalc. 









(* ---------- some lemmas about bdsend  ----------------*)
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


(*-------------------  some lemmas on down ------------------------------*)

Lemma down_tau: forall a, down a = Ltau -> a = Ltau.
Proof.
intros. unfold down in *.
destruct a; cbn in H; inversion H; auto.
Qed.



Lemma down_send: forall a x y , down a = Lsend x y -> 
  exists x' y', a = Lsend x' y'.
Proof. 
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.


Lemma down_rcv: forall a x y , down a = Lrcv x y -> 
  exists x' y', a = Lrcv x' y'.
Proof. 
intros. unfold down in *.
destruct a; cbn in H; inversion H; eauto with picalc.
Qed.



Lemma not_bdsend_down: forall a,
  not_bdsend (down a) -> not_bdsend a.
Proof.
intros.
inversion H. 
eapply down_tau in H0.
rewrite H0.
eauto with picalc.
do 3 destruct H0.
set (lem:= down_send a x x0 H0).
firstorder.

inversion H0.
set (lem:= down_rcv a x x0 H0).
firstorder.
Qed.
(*----------------------------------------------------------*)




Lemma sb_ch_canon: forall (sigma:nat->chan) x, exists y, sigma x = ch y.
Proof.
intros.
case (sigma x).
firstorder. 
exists n. auto.
Qed.









(*
Definition shift_sb2 x := (subst_chan (S >> ch)) (ch x).
Lemma equiv_shift: shift_sb2 = shift_sb.
Proof.
fe. auto.
Qed.
*)


