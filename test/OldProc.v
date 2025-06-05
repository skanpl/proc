

Require Import Autosubst.Autosubst.
(**)


(*
Inductive type : Type :=
| TyVar (x : var)
| Arr (A B : type)
| All (A : {bind type}).
Inductive term :=
| TeVar (x : var)
| Abs (A : type) (s : {bind term})
| App (s t : term)
| TAbs (s : {bind type in term})
| TApp (s : term) (A : type).


Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.


Definition bloke (t:term)  (ty: type) := t.[ty.:ids] . 
*)








Inductive chan :=
| Name (x:var)
.


Inductive proc := 
| Zero 
| Par (P Q: proc)
| Send (x y:chan) (P: proc)
| Rcv (x: chan) (P:{bind chan in proc}) 
.


Instance Ids_chan : Ids chan. derive. Defined.
Instance Rename_chan : Rename chan. derive. Defined.
Instance Subst_chan : Subst chan. derive. Defined.
Instance SubstLemmas_chan : SubstLemmas chan. derive. Qed.




Instance Rename_proc : Rename proc. derive. Defined.
Instance Subst_proc : Subst proc. derive. Defined.
Instance HSubst_proc : HSubst chan proc. derive. Defined.

 
Instance Ids_proc : Ids proc. derive. Defined.
Instance HSubstLemmas_term : HSubstLemmas chan proc. derive. Qed.

(**)

(*
Instance Ids_proc : Ids proc. derive. Defined.
Instance SubstLemmas_proc : SubstLemmas proc. derive. Qed.
*)







(*


Inductive proc :=
(*| Var (X: var) *) 
| Zero 
| Par (P Q: proc)
| Send (Q R P: proc)
| Rcv (Q: proc) (P:proc)
(*| Rcv (Q: proc) (P:{bind proc}) *)
.


Definition dummy := Par Zero Zero.
*)






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


Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P'.|[y/]) )
.

(*


*)





Inductive lab :=
| Lsend (x y: chan)
| Lrcv (x y: chan)
| Ltau 
.

Inductive lt: proc -> lab -> proc -> Prop :=
| Lt_send: forall Q R P, lt (Send Q R P) (Lsend Q R) P 
| Lt_rcv: forall Q P q, lt (Rcv Q P) (Lrcv Q q) dummy
(*| Lt_rcv: forall Q P q, lt (Rcv Q P) (Lrcv Q q) (P.[q/]) *)

| Lt_parL: forall Q P P' a, lt P a P' -> lt (Par P Q) a (Par P' Q) 
| Lt_parR: forall P Q Q' a, lt Q a Q' -> lt (Par P Q) a (Par P Q')
| Lt_commL: forall P Q P' Q' q r, 
    lt P (Lsend q r) P' -> lt Q (Lrcv q r) Q' -> lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' q r, 
    lt P (Lrcv q r) P' -> lt Q (Lsend q r) Q' -> lt (Par P Q) Ltau (Par P' Q')
.

 
Hint Constructors proc conga cong lab lt: picalc. 

 

 (*  --- a bunch of tactics for replacement in conga and lt hypotheses  ---  *)
Ltac subinallleft_lt  :=
 try match goal with
| [H: lt ?P ?a ?P', Heq: ?ter=?P|- _] => symmetry in Heq; rewrite Heq in *; symmetry in Heq
end .

  
Ltac subinallright_lt  :=
 try match goal with
| [H: lt ?P ?a ?P', Heq: ?ter=?P'|- _] => symmetry in Heq; rewrite Heq in *; symmetry in Heq
end .

Ltac subinall_lt := subinallleft_lt; subinallright_lt. 

Ltac subinallleft_conga  :=
 try match goal with
| [H: conga ?P ?P', Heq: ?ter=?P|- _] => symmetry in Heq; rewrite Heq in *; symmetry in Heq
end .


Ltac subinallright_conga  :=
 try match goal with
| [H: conga ?P ?P', Heq: ?ter=?P'|- _] => symmetry in Heq; rewrite Heq in *; symmetry in Heq
end .

Ltac subinall_conga := subinallleft_conga; subinallright_conga. 


(*note that if terms are nested it won't work*)
Ltac subinall := subinall_lt ; subinall_conga. 
(*------------------------------*)


 
 
Lemma conga_resp_lt: forall P Q P' a, 
  lt P a P'-> conga P Q -> exists Q', lt Q a Q' /\ conga P' Q'.
Proof.
intros. 
inversion H.  (*caseAn on lt derivation*)
(*======all the cases of Lt_send======*)  
inversion H0 .
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
econstructor . split. eapply Lt_parR.  
symmetry in H8; rewrite H8 in *. eapply H1 .
intuition .   
(*subcase assoc*)  

subinall. 
inversion H2. (*destruct the AST*)
(*rewrite H8 in H1.*)
  (*caseAn on P1|Q1 ->a P'0*)
  subst.  
  inversion H1.
    
  eexists. split.  
  eauto with picalc.
  intuition.

  eexists. split.
  eauto with picalc.
  intuition.

  eexists. split.
  eauto with picalc.
  intuition.

  eexists. split.
  eauto with picalc.
  intuition.

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
(*subinall.*)  

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

 
 
 
 
