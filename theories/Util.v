Require Import ProcSyn.
Require Import Semantics.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lia.

Ltac fe := apply functional_extensionality.



Locate "↑__proc".
Locate "↑__chan".
Print up_chan_chan.




(*
Definition up (sigma: nat-> nat) := 
  0 .: (sigma >> shift).

 
Lemma bind_simpl: forall sigma,
 shift >> (up sigma) = sigma >> shift .
Proof.
intro. symmetry.
unfold funcomp, up.
fe.
intro.
unfold shift, funcomp.
auto.
Qed.
*)



(*--------- shifts (maybe useless) ------------*)


Lemma shift0: forall P,  shiftn_pr 0 P = P.
Proof.
intros.  
case P; intros; asimpl; auto.    
Qed.

 

Lemma double_sub_par: forall P Q sigma1 sigma2,
  (Par P Q) [sigma1][sigma2] = Par (P[sigma1][sigma2]) (Q[sigma1][sigma2]). 
Proof. 
asimpl. auto.
Qed.

Lemma sub_par: forall P Q sigma, 
  (Par P Q)[sigma] = Par (P[sigma]) (Q[sigma]). 
Proof.
asimpl. auto.
Qed.

Lemma shift_pr_def: forall P, P [fun x => (1+x)__chan] = shift_pr P.
Proof.
auto. 
Qed.

Lemma shift_succ: forall P n, 
  P [fun x => ((S n) +x)__chan] = shiftn_pr (n+1) P.
Proof.
intros.
asimpl.
unfold shiftn_pr.
asimpl.
replace (S n) with (n+1).
auto. 
lia.
Qed.


Lemma succ_bindsub: forall n,
 ( fun x => ((S n)+x) ) = (fun x => n+x)>> S.
Proof.
intro. fe. intro.
asimpl.
unfold funcomp.
auto.
Qed.
 
Print up_chan_chan.
Print up_proc.

(*
Definition coerce (sigma: nat-> chan) := fun x =>
  match (sigma x) with
  | var_chan x => x
  end.


Lemma up_chan_comp_chan: forall (x:chan) (sigma1 sigma2: nat -> chan),
  x [up_chan_chan sigma1] [up_chan_chan sigma2] =
  x [up_chan_chan ( (coerce sigma1) >> sigma2)].
Proof.
intros.
asimpl.
case x. intro.
cbv.
case n.
auto.
intro.
case (sigma1 n0). intro.
case (sigma2 n1). intro.
auto.
Qed.


Lemma up_chan_comp_pr: forall (P:proc) (sigma1 sigma2: nat -> chan),
  P [up_chan_chan sigma1] [up_chan_chan sigma2] =
  P [up_chan_chan ( (coerce sigma1) >> sigma2)].
Proof.
intros.
induction  P.
auto.

cbn.
erewrite IHP1, IHP2.
auto.
(*TODO*)



Lemma rcv_sub_shiftn: forall x P n,
  (Rcv x P)[fun x=> ((S n) +x)__chan] = 
  (Rcv x P)[fun x => (n+x)__chan] [fun x => (1+x)__chan].
Proof.
intros.
cbn.

asimpl.
(*TODO*)


Lemma sub_shiftn: forall (P:proc) n, 
  P[fun x => ((S n) +x)__chan] = P[fun x => (n+x)__chan][fun x => (1+x)__chan].
Proof.
intros.
case P.
auto.

intros. 
asimpl.
auto.
 
intros. 

asimpl.
auto.
*)


Lemma shift_chan: forall (a:chan) n,   
  a[fun x : nat => (S x)__chan] [fun x : nat => (n + x)__chan] = 
  a[fun x : nat => (n + 1 + x)__chan].
Proof.
intros.
asimpl. 
case a. intro.
asimpl.
unfold funcomp.
replace (n + S n0) with (n+1+n0).
auto. lia.
Qed.




(* autosubst problem:
induction htpotheses are too weak
and doesn't take into acount that 
a term is bellow a binder in the IH
*)
Goal forall P:proc, P=P.
intro.
induction P.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
reflexivity.
Qed.



Lemma shift_succ_comp: forall P n, 
  shiftn_pr n (shift_pr P) = (shiftn_pr (n+1)  P) .
Proof.
intros.
generalize dependent n.
induction P.

intro. auto.

intro. 
unfold shift_pr, shiftn_pr in *.
cbn.
erewrite IHP1, IHP2. auto.

intro.
unfold shift_pr, shiftn_pr in *.
cbn.
erewrite shift_chan. 
replace (fun x => (S x)__chan) with (fun x => (1+x)__chan).
set (lem:= IHP n).
(*check the remark above to understand the prob*)





(*
Lemma shift_succ_comp: forall P n, 
  shiftn_pr n (shift_pr P) = (shiftn_pr (n+1)  P) .
Proof.
intros. 
generalize dependent P.
induction n. intro. 
case P; intros; asimpl; auto.

intro.
simpl.
case P.
cbn.
auto.
 
intros. 
unfold shift_pr, shiftn_pr in *.
replace (S n) with (n+1); try lia.
set (lem:= IHn ((Par p p0) [fun x : nat => (1 + x)__chan])). 
symmetry in lem. 
try erewrite lem.


erewrite double_sub_par.
erewrite sub_par.

erewrite sub_par.


erewrite shift_pr_def.
rewrite (shift_pr_def p0).
*)





(*TODO*) 
(*--------------------------------------------*)



Lemma iter_nu_scope_extr: forall n P Q,
  cong (Par (iter_nu n P) Q)   (iter_nu n (Par P (shiftn_pr n Q) )).
Proof. 
intros.
generalize dependent Q. 
induction n. intro.
unfold shiftn_pr. simpl.   
rewrite iden_ren in *.
asimpl.   
eauto with picalc.
    
intro. 
simpl.
eapply Cg_trans.
eapply Cg_cgb. eapply Cgb_nuPar.
eapply Cg_ctxNu.
eapply (IHn (shift_pr Q )).
(*TODO*)
