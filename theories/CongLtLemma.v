
Require Import Proc.






Lemma conga_resp_lt: forall P Q P' a, 
  lt P a P'-> conga P Q -> exists Q', lt Q a Q' /\ conga P' Q'.
Proof.
intros. 
inversion H.  (*caseAn on lt derivation*)
(*======all the cases of Lt_send======*)  
inversion H0. 
subinall. 
exfalso. inversion H0.
subinall. 
exfalso. inversion H0.
subinall. 
exfalso. inversion H0.
(* ======all the cases of Lt_rcv======*)
inversion H0.
subinall.  
exfalso. inversion H0.
subinall. 
exfalso. inversion H0.
subinall. 
exfalso. inversion H0.
(*======all the cases parL======*)
inversion H0.
(*subcase com*)
subinall.  
inversion H2. (*destroy the AST*)
rewrite H2 in H0.
rewrite H2 in H.
rewrite H9 in H.
rewrite H8 in H1.
exists (Par Q1 P'0). split.
apply (Lt_parR Q1 P1  P'0 a).
apply H1.
apply (Cga_parCom P'0 Q1).
(*subcase assoc*)  

subinall. 
inversion H2. (*destruct the AST*)
rewrite H8 in H1.
  (*caseAn on P1|Q1 ->a P'0*)
  inversion H1.
  exists (Par P'1 (Par Q1 R)). split.
  apply (Lt_parL  (Par Q1 R) P1 P'1 a ).
  apply H13.
  apply (Cga_parAssoc P'1 Q1 R).
  
  exists (Par P1 (Par Q' R)). split.
  apply (Lt_parR P1 (Par Q1 R) (Par Q' R) a).
  apply (Lt_parL R Q1 Q' a).
  apply H13.
  apply (Cga_parAssoc P1 Q' R).
  
  exists ( Par P'1 (Par Q' R) ). split.
  apply (Lt_commL P1 (Par Q1 R) P'1 (Par Q' R) q r).
  apply H11. 
  apply (Lt_parL R Q1 Q' (Lrcv q r)).
  apply H14.
  apply (Cga_parAssoc P'1 Q' R). 

  exists (Par P'1 (Par Q' R)). split.
  apply (Lt_commR P1 (Par Q1 R) P'1 (Par Q' R) q r).
  apply H11.
  apply (Lt_parL  R Q1 Q' (Lsend q r)).
  apply H14.
  apply (Cga_parAssoc P'1 Q' R).
(*subcase neut*)
  subinall.
  inversion H2. (*destroy the AST*)
  rewrite H8 in *.
  exists (P'0). split.
  apply H1.
  apply (Cga_parNeut P'0).
  
(*======all the cases parR======*)
inversion H0.
(*subcase com*)
subinall. 
inversion H2. (*destroy the AST*)
symmetry in H9;rewrite H9.
exists (Par Q' P1). split.
apply (Lt_parL P1 Q0 Q' a).
apply H1.
apply (Cga_parCom P1 Q').
(*subcase assoc*)
subinall.  

(* caseAn on conga*)
inversion H0.

exists (Par Q' (Par Q1 R)). split.
rewrite H10 in *.
apply (Lt_parL (Par Q1 R) P1 Q' a).
apply H1.
apply (Cga_parCom (Par Q1 R) Q').
 
exists (Par P1 (Par Q1 Q')). split.
rewrite H12 in *.
apply (Lt_parR P1 (Par Q1 R) (Par Q1 Q') a).
apply (Lt_parR  Q1 R Q' a).
apply H1.
apply (Cga_parAssoc P1 Q1 Q').

subinall. 
rewrite H7 in *.
exfalso. inversion H1.

(*subcase neut*)
subinall. 
inversion H2. (*destroy AST*)
rewrite H9 in *.
(*caseAn on conga*)
inversion H0.
exfalso. inversion H1.
exfalso. inversion H1.
exfalso. inversion H1.

(* ======all the cases of Lt_commL======*)
inversion H0. (*caseAn on conga*)

subinall. 
inversion H3. (*destruct AST*)
rewrite H9, H10 in *.
symmetry in H4;rewrite H4 in H.
exists (Par Q' P'0). split.
apply (Lt_commR Q1 P1 Q' P'0 q r).
apply H2. apply H1.
apply (Cga_parCom P'0 Q').

subinall.
inversion H3. (*destruct AST*)
rewrite H9 in *.
symmetry in H4;rewrite H4 in H.   
inversion H1.  
(*caseAn on   P1|Q1 ->(q!r)   P'0*)  
(**)
rewrite H10 in H2. 
exists (Par P'1 (Par Q1 Q')). split.
apply (Lt_commL P1 (Par Q1 R) P'1 (Par Q1 Q') q r).
apply H14.
apply (Lt_parR Q1 R Q' (Lrcv q r)).
apply H2.
apply (Cga_parAssoc P'1 Q1 Q').
(**)
rewrite H10  in H2.
exists (Par P1 (Par Q'0 Q')). split.
apply (Lt_parR P1 (Par Q1 R) (Par Q'0 Q') Ltau).
apply (Lt_commL Q1 R Q'0 Q' q r).
apply H14.
apply H2.
apply (Cga_parAssoc P1 Q'0 Q').

subinall. 
inversion H3. (*destroy AST*)
rewrite H10 in *.
exfalso. inversion H2.
(* ======all the cases of Lt_commR======*)
inversion H0.

subinall.
inversion H3. (*destroy AST*)
rewrite H9,H10 in *.
exists (Par Q' P'0). split.
apply (Lt_commL Q1 P1 Q' P'0 q r).
apply H2. apply H1.
apply (Cga_parCom P'0 Q').

subinall.
inversion H3. (*destroy AST*)
subinall.
rewrite H10 in H2. rewrite H9 in H1.
(*caseAn on   P1|Q1 ->(q?r)   P'0*)
inversion H1.
exists (Par P'1 (Par Q1 Q')). split.
apply (Lt_commR P1 (Par Q1 R) P'1 (Par Q1 Q') q r).
apply H14. 
apply (Lt_parR Q1 R Q' (Lsend q r)). apply H2.
apply (Cga_parAssoc P'1 Q1 Q').
(**) 
exists (Par P1 (Par Q'0 Q')). split.
apply (Lt_parR P1 (Par Q1 R) (Par Q'0 Q') Ltau).
apply (Lt_commR Q1 R Q'0 Q' q r).
apply H14. apply H2.
apply (Cga_parAssoc P1 Q'0 Q').

subinall. 
inversion H3. (*destroy AST*)
rewrite H10 in *.
exfalso. inversion H2.
Qed.


(*
    -----------         ----------------------
    P|0 conga P         (P|Q)|R  conga P|(Q|R)


         ---------------
         P|Q   conga Q|P

*)

(*
Lemma cong_inv_conga: forall P Q, 
  conga P Q -> 
    exists P0, P0 cong 
*)


Hint Constructors lt cong conga: core. 

Axiom skip: forall A, A.

Lemma cong_resp_lt: forall P P' Q Q' a,  
  cong P Q -> 
   (lt P a P' -> exists Q0, lt Q a Q0 /\ cong P' Q0) /\
   (lt Q a Q' -> exists P0, lt P a P0 /\ cong P0 Q').
Proof. 
intros. 
generalize dependent P'.
generalize dependent Q'. 
induction H. 
apply skip.
apply skip.

intros. split.
intro. 
assert(exists P0 : proc, lt Q a P0 /\ cong P0 Q').
set (IHr:=IHcong P' P' ).
destruct IHr.
set (ex:= H2 H0).
destruct ex.
exists x. split.
destruct H3.
apply H3.
destruct H3.






(*
Inductive lt: proc -> lab -> proc -> Prop :=
| Lt_send: forall Q R P, lt (Send Q R P) (Lsend Q R) P 
| Lt_rcv: forall Q P q, lt (Rcv Q P) (Lrcv Q q) (P.[q/])
| Lt_parL: forall Q P P' a, lt P a P' -> lt (Par P Q) a (Par P' Q) 
| Lt_parR: forall P Q Q' a, lt Q a Q' -> lt (Par P Q) a (Par P Q')
| Lt_commL: forall P Q P' Q' q r, 
    lt P (Lsend q r) P' -> lt Q (Lrcv q r) Q' -> lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' q r, 
    lt P (Lrcv q r) P' -> lt Q (Lsend q r) Q' -> lt (Par P Q) Ltau (Par P' Q')
.


(*   (proc, |)  commutative monoid up to conga *)
Inductive conga: proc -> proc -> Prop :=
| Cga_parCom: forall P Q,     conga (Par P Q)  (Par Q P)
| Cga_parAssoc: forall P Q R, conga (Par (Par P Q) R)    (Par P (Par Q R))
| Cga_parNeut: forall P,      conga (Par P Zero) P
.

(*  cong = conga + equivrel + ctxrules *)
Inductive cong: proc -> proc -> Prop :=
| Cg_cga: forall P Q,     conga P Q -> cong P Q
| Cg_refl: forall P,       cong P P
| Cg_sym: forall P Q,     cong Q P -> cong P Q
| Cg_trans: forall P Q R, cong P Q -> cong Q R -> cong P R
| Cg_ctxParL: forall P P' Q, cong P P' -> cong (Par P Q) (Par P' Q)  
| Cg_ctxParR: forall P Q Q', cong Q Q' -> cong (Par P Q) (Par P Q')
| Cg_ctxSend: forall Q R P P', cong P P' -> cong (Send Q R P) (Send Q R P')
| Cg_ctxRcv: forall Q P P', cong P P' -> cong (Rcv Q P) (Rcv Q P')
.
*)




(*



Lemma cong_resp_lt: forall P P' a, forall Q,  
  cong P Q->  lt P a P' -> exists Q', lt Q a Q' /\ cong P' Q'.
Proof. 
intros.
induction H. 
(*===basecase conga===*)

assert (exists Q0 : proc, lt Q a Q0 /\ conga P' Q0).
apply (conga_resp_lt P Q P' a). apply H0. apply H.
destruct H1.  
exists x. destruct H1. split. apply H1. apply (Cg_cga P' x). apply H2.
(*===basecase refl===*)

exists P'. split. 
apply H0. apply (Cg_refl P').
(*===indcase sym===*)










attempt with ind on P->a P'
intros. generalize dependent Q.
induction H. 

(*===base case Lt_send===*)
intros.   
inversion H0. (*caseAn on Q!R.P cong Q0   *)
 
exfalso. inversion H.

exists P. split.
apply (Lt_send Q R P). apply (Cg_refl P).

*)
