
Require Import ProcSyn.
Require Import Semantics.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.





(* ----------- some lemmas ---------------------------*)
Lemma iter_nu_cong: forall P Q R n,
  cong P (iter_nu n Q) -> cong (Par P R) (Par (iter_nu n Q) R).  
Proof.
intros. 
induction n; unfold iter_nu; eauto with picalc.
Qed.



Lemma conga_resp_sub: forall P Q sigma,
  conga P Q -> conga (P [sigma]) (Q [sigma]).
Proof.
intros.
inversion H; asimpl; eauto with picalc.
Qed.
 
Definition up (sigma: nat-> nat) := 
  0 .: (sigma >> shift).


 
Lemma bind_simpl: forall sigma,
 shift >> (up sigma) = sigma >> shift .
Proof.
intro.
symmetry.
unfold funcomp. unfold up.
apply functional_extensionality.
intro.
unfold shift. unfold funcomp.
cbv. auto.
Qed.

Ltac fe := apply functional_extensionality.

Lemma iden_ren_proc: forall P:proc,  P [fun x => var_chan (x+0)] = P [fun x => var_chan (x)]. 
Proof.
intros.
assert ((fun x : nat => (x + 0)__chan) = fun x : nat => x __chan).
fe.
intros.
auto.
rewrite H.
auto.
Qed.


Lemma iden_ren_chan: forall x:chan,  x [fun x => var_chan (x+0)] = x [fun x => var_chan (x)]. 
Proof.
intros.
assert ((fun x : nat => (x + 0)__chan) = fun x : nat => x __chan).
fe.
intros.
auto.
rewrite H.
auto.
Qed.



Lemma shift0: forall P, shiftn_pr 0 P = P.
Proof.
intros.
case P. 
cbn. 
auto.

intros. 
cbn.
set (lem0 := iden_ren_proc p0).
set (lem := iden_ren_proc p).   
rewrite lem,lem0 in *. 
asimpl.
auto.
 
intros.
cbn.
set (lem0 := iden_ren_chan c).
set (lem := iden_ren_proc p).
rewrite lem0.





Lemma shift_succ: forall P n, 
  shiftn_pr n (shift_pr P) = (shiftn_pr (n+1)  P) .
Proof.
intros.
induction n.
simpl. 




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



Inductive congb: proc -> proc -> Prop :=
| Cgb_nuZero: congb (Nu Zero) Zero
| Cgb_nuPar: forall P Q,  congb (Par (Nu P) Q)   (Nu (Par P (shift_pr Q) ))
| Cgb_nuSwap: forall P, congb (Nu (Nu P))  (Nu (Nu (swap 0 P)))
.






(*  cong = conga + equivrel + ctxrules *)
Inductive cong: proc -> proc -> Prop :=
| Cg_cga: forall P Q,     conga P Q -> cong P Q
| Cg_cgb: forall P Q,     congb P Q -> cong P Q
| Cg_refl: forall P,       cong P P
| Cg_sym: forall P Q,     cong Q P -> cong P Q
| Cg_trans: forall P Q R, cong P Q -> cong Q R -> cong P R
| Cg_ctxParL: forall P P' Q, cong P P' -> cong (Par P Q) (Par P' Q)  
| Cg_ctxParR: forall P Q Q', cong Q Q' -> cong (Par P Q) (Par P Q')
| Cg_ctxSend: forall x y P P', cong P P' -> cong (Send x y P) (Send x y P')
| Cg_ctxRcv: forall x P P', cong P P' -> cong (Rcv x P) (Rcv x P')
| Cg_ctxNu: forall P Q,    cong P Q -> cong (Nu P) (Nu Q)
.




(*--------------------------------------------------------*)





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

Qed.










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



(*

 P cong Nux1...Nuxn  (x0!x1.x2| x0?x3)|x 



  P|R  cong   (x!y.R1| x?R2 )| S




*)


