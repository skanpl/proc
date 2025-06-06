
Require Import ProcSyn.
Require Import Semantics.
Require Import unscoped.
Require Import core.
Require Import SubCompatible.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
 




  
 
Lemma Lconga_resp_lt: forall P Q P' a, 
  lt P a P'-> conga P Q -> exists Q', lt Q a Q' /\ conga P' Q'.
Proof.
intros. 
inversion H.  (*caseAn on lt derivation*)
(*======all the cases of Lt_send======*)  
inversion H0 .
subst. exfalso. inversion H0.
subst. exfalso. inversion H0.
subst. exfalso. inversion H0.
(* ======all the cases of Lt_rcv======*)
inversion H0.
subst. exfalso. inversion H0.
subst. exfalso. inversion H0.
subst. exfalso. inversion H0.
(*======all the cases parL======*)
inversion H0.
(*subcase com*)


subst.     
inversion H5. (*destroy the AST*)
eauto with picalc.
(*subcase assoc*)  

subst.  
inversion H5. (*destruct the AST*)
  subst.  
  inversion H1. (*caseAn on P1|Q1 ->a P'0*)
  eauto with picalc.
  eauto with picalc.
  eauto with picalc.
  eauto with picalc.
  
(*subcase neut*)
  
  eexists. split. 
  subst. 
  inversion H5.
  subst. 
  apply H1.
  subst. inversion H5.
  intuition.

(*======all the cases parR======*)
inversion H0.
(*subcase com*)

eexists. split. 
subst. 
inversion H5. 
subst.
eauto with picalc.
subst. inversion H5. 
intuition.

(*subcase assoc*)
 
subst.

(* caseAn on conga*)
inversion H0.
 
eexists. split.
subst. 
eapply Lt_parL.
eapply H1.
subst.
intuition. 

eexists. split.
subst.
eapply Lt_parR. eapply Lt_parR.
eapply H1.
subst.
intuition.

subst.
exfalso. inversion H1.
(*subcase neut*)
subst.
inversion H5.
subst.
exfalso. inversion H1.
 
(* ======all the cases of Lt_commL======*)
inversion H0. (*caseAn on conga*)
subst. 
inversion H6. (*destruct AST*) 
  
eexists. split.
eauto with picalc. intuition.

subst.
inversion H6.
symmetry in H4;rewrite H4 in H1.
inversion H1.  (*caseAn on   P1|Q1 ->(q!r)   P'0*) 
eexists. split.
eauto with picalc. intuition.
(**)
eexists. split.
eauto with picalc. intuition.

subst. 
inversion H6. subst.
exfalso. inversion H2.


(* ======all the cases of Lt_commR======*)
inversion H0.

subst.
eexists. split.
inversion H6. 
eauto with picalc. intuition.
 
subst.
inversion H6.
symmetry in H4,H5; rewrite H5 in H2; rewrite H4 in H1.
inversion H1. (*caseAn on   P1|Q1 ->(q?r)   P'0*)
eexists. split.
rewrite H5 in *.
eapply Lt_commR.
eauto with picalc. eauto with picalc. intuition.
(**)
eexists. split.
subst.
eapply  Lt_parR.
eauto with picalc. subst. intuition.

subst.
inversion H6.
subst.
exfalso. inversion H2.
Qed.






Lemma Rconga_resp_lt: forall P Q Q' a, 
  lt Q a Q'-> conga P Q -> exists P', lt P a P' /\ conga P' Q'.
Proof.
intros.  
inversion H.  (*caseAn on lt derivation*)
(*======all the cases of Lt_send======*)  
inversion H0 .
subst.   
exfalso.  inversion H5.
subst. 
exfalso. inversion H5.
subst. 
eauto with picalc.
(* ======all the cases of Lt_rcv======*)
inversion H0.
subst.   
exfalso. inversion H5.
subst. 
exfalso. inversion H5.
subst.
eauto with picalc. 
(*======all the cases parL======*)
inversion H0.
(*subcase com*)

 
subst.     
inversion H6. (*destroy the AST*)
eauto with picalc.
(*subcase assoc*)  

subst.  
inversion H6. (*destruct the AST*)
(*rewrite H8 in H1.*)
  (*caseAn on P1|Q1 ->a P'0*)
  subst.
  eauto with picalc.  
(*subcase neut*)
  subst.
  eauto with picalc.  

(*======all the cases parR======*)
inversion H0.
(*subcase com*)

subst.
inversion H6. 
eauto with picalc.

(*subcase assoc*)
subst.
inversion H6.
subst.

inversion H0. (* caseAn on conga*)
 
eexists. split.
subst.
eauto with picalc.

subst. 
eauto with picalc.

subst.
inversion H1. (*case an on Q1|R ->a ...*)
eauto with picalc.
eauto with picalc.
eauto with picalc.
eauto with picalc.
subst. eauto with picalc.

(*subcase neut*)
subst.
eauto with picalc. 
(* ======all the cases of Lt_commL======*)
inversion H0. (*caseAn on conga*)
subst.  
inversion H7. (*destruct AST*) 
eauto with picalc.
  
subst.
inversion H7.
symmetry in  H5; rewrite H5 in H2.
inversion H2. (*caseAn on Q1|R ->a ... *)
subst.
eauto with picalc.
subst.
eauto with picalc.

subst.
eauto with picalc.

(* ======all the cases of Lt_commR======*)
inversion H0.

subst.
eexists. split.
inversion H7.
eauto with picalc. intuition.
 
subst.
inversion H7.
symmetry in H5; rewrite H5 in H2.
inversion H2. (*caseAn on Q1|R ->a ...*)
eauto with picalc.
eauto with picalc.

subst.
eauto with picalc.
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

(*======case conga======*)
intros. firstorder.
assert (exists Q0, lt Q a Q0 /\ conga P' Q0).
eapply Lconga_resp_lt.
eauto with picalc. auto.
firstorder.
eauto with picalc.
(**)
assert( exists P0, lt P a P0 /\ conga P0 Q').
eapply Rconga_resp_lt.
eauto with picalc. auto.
firstorder.
eauto with picalc.
(*======case refl======*)

firstorder.  
eauto with picalc. 
eauto with picalc.
(*======case sym======*)

firstorder. 
set (IHdestr := IHcong a P' P'). 
firstorder. eauto with picalc.
(**)
firstorder.
set (IHdestr := IHcong a Q' Q').
firstorder .
eauto with picalc.

(*======case trans======*)
firstorder.
 
set (D1:= IHcong1 a P' P').  destruct D1. 
set (d1 := H2 H1).
firstorder.
set(D2 := IHcong2 a x x).
firstorder.  eauto with picalc.
(**)
set (D1:= IHcong2 a Q' P'). destruct D1.
firstorder.
set (D2 := IHcong1 a x P'). firstorder. eauto with picalc. 
(*======case parL======*)
firstorder.   
inversion H0. (*caseAn on P|Q ->a  ...*)
subst.
set (D := IHcong a Q' P'1 ). 
firstorder. eauto with picalc. 
 
eauto with picalc.

subst.
set (D:= IHcong (Lsend x y) Q' P'1). 
firstorder. eauto with picalc.

subst.
set (D := IHcong (Lrcv x y) Q' P'1).
firstorder. eauto with picalc.
(**)
inversion H0. (*caseAn on P'|Q ->a  ...*)
subst.
set (D := IHcong a  P'1 Q). 
firstorder. eauto with picalc.
 
eauto with picalc.
 
subst.
set (D := IHcong (Lsend x y) P'1 Q ). 
firstorder. eauto with picalc.

subst.
set (D := IHcong (Lrcv x y) P'1 Q ). 
firstorder.
eauto with picalc.
(*======case parR======*)
firstorder.
inversion H0. (*caseAn on P|Q ->a  ...*)

subst.
eauto with picalc.

subst.
set (D := IHcong a Q Q'1 ). firstorder.
eauto with picalc.

subst. 
set (D:= IHcong (Lrcv x y) P Q'1). firstorder.
eauto with picalc.

subst. 
set (D := IHcong (Lsend x y) P Q'1). firstorder.
eauto with picalc.
(**)
inversion H0. (*caseAn on P|Q' ->a  ...*)
 
eauto with picalc. 

subst.
set (D:= IHcong a Q'1 P). firstorder.
eauto with picalc.
 
subst.
set (D:= IHcong (Lrcv x y) Q'1 P). firstorder.
eauto with picalc.

subst.
set (D:= IHcong (Lsend x y) Q'1 P). firstorder.
eauto with picalc.

(*======case send======*)
firstorder. 
inversion H0.
subst.
eauto with picalc.

inversion H0.
subst.
eauto with picalc.

(*======case rcv======*)
firstorder.
inversion H0.
subst. 
eexists. split.
eauto with picalc.

set (lem := cong_resp_sub P P' (y..)).
firstorder.

inversion H0.
subst.
eexists. split.
eauto with picalc.
set (lem := cong_resp_sub P P' (y..)).
firstorder.
Qed.











(*
Lemma Testcong_resp_lt: forall P Q P' Q' a, 
  cong P Q -> 
     (lt P a P'  -> exists Q0, lt Q a Q0 /\ cong P' Q0)  /\
      (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof.
intros.
induction H. 
(*case conga*)
firstorder.
set (leml := Lconga_resp_lt P Q P' a H0 H).
destruct leml.
firstorder. 
eauto with picalc.
(**)
set (lemr := Rconga_resp_lt P Q Q' a H0 H).
destruct lemr. firstorder. 
eauto with picalc.
(*case refl*)
firstorder.  
eauto with picalc.
eauto with picalc.
(*case sym*)
firstorder.

*)
