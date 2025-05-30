

Require Import Autosubst.Autosubst.





(* 
 The following test illustrates that SubstLemmas fails to be derived if
 we have more than one occurence of the type var in the inductive definition.

Inductive proce :=
| PVar (x: var) 
| PZero 
| PPar (p q: proce)
| PSend (x:proce)   (r p: proce)
| PRcv (x: var) (p:{bind proce})
.
  
Instance Ids_proce : Ids proce. derive. Defined.
Instance Rename_proce : Rename proce. derive. Defined.
Instance Subst_proce : Subst proce. derive. Defined.
Instance SubstLemmas_proce : SubstLemmas proce. derive. Qed.
*)











(*
p,q,r ::= x
       | 0
       | (p|q)
       | q!r.P
       | q?p
*)

Inductive proc :=
| Var (X: var) 
| Zero 
| Par (P Q: proc)
| Send (Q R P: proc)
| Rcv (Q: proc) (P:{bind proc})
.




Instance Ids_proc : Ids proc. derive. Defined.
Instance Rename_proc : Rename proc. derive. Defined.
Instance Subst_proc : Subst proc. derive. Defined.
Instance SubstLemmas_proc : SubstLemmas proc. derive. Qed.


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
| Red_comm: forall Q R P P', red (Par (Send Q R P) (Rcv Q P')) (Par P (P'.[R/]) )
.

Inductive lab :=
| Lsend (Q R: proc)
| Lrcv (Q R: proc)
| Ltau 
.

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



 
 
 
Lemma lemma6: forall P Q P' a, 
  lt P a P'-> conga P Q -> exists Q', lt Q a Q' /\ conga P' Q'.
Proof.
intros. 
induction H.
(*===base cases===*)
   exfalso. inversion H0.
   exfalso.  inversion H0.
(*===indcase parL===*)
   
  (*----caseAn on conga---------*) inversion H0. 
    (*subcase com *)
      exists (Par Q0 P'). split.
      apply (Lt_parR Q0 P P' a).
      apply H.
      apply (Cga_parCom P' Q0).
    (*subcase assoc *) 
      (* caseAn on P->a P*)  inversion H.  
        (*subsubcase send/rcv*)
            subinall_lt.   
            exfalso. inversion H2.
            subinall_lt. 
            exfalso. inversion H2.    
 
           
        (*subsubcase parL*)
            (** --i adapt the notations to mine--*)
            (**) subinall. subinall. 
            (**) set (Ptilde := P0) in *. set (Qtilde := Q1) in *. 

            (**) inversion H2. (*deconstruct the AST*) 
            (**) symmetry in H9; rewrite H9 in *; symmetry in H10; rewrite H10 in *.
            (**) set (Ptilde' := P'0) in *. 
            (** ---------------*)
   
             exists (Par Ptilde' (Par Qtilde Q0)). split. 
             apply (  Lt_parL (Par Qtilde Q0) Ptilde Ptilde' a         ).
             apply H4.   
             clear .  
             apply (Cga_parAssoc Ptilde' Qtilde Q0). 
        (*subsubcase parR*)
             subinall.   subinall. 
             set (Ptilde := P0) in*. set (Qtilde := Q1) in * .  
               
             inversion H2. (*destruct the AST*)
             symmetry in H9, H10 . rewrite  H9,H10 in *. 
             exists (Par Ptilde (Par Q' Q0)). split.
             apply (Lt_parR Ptilde (Par Qtilde Q0) (Par Q' Q0) a).
             apply (Lt_parL Q0 Qtilde Q' a).
             apply H4.
             apply (Cga_parAssoc Ptilde Q' Q0).
        (*subsubcase commL*)       
             set (Ptilde := P1) in *. set (Ptilde' := P'0) in *.
             set (Qtilde := Q2) in *. set (Qtilde':= Q') in *. 
             exists (Par Ptilde' (Par Qtilde' Q0)). split.
             symmetry in H6. rewrite H6 in *. 
             inversion H2. (*destruct the AST*) 
             rewrite H10,H11 in *.
             apply (Lt_commL Ptilde (Par Qtilde Q0) Ptilde' (Par Qtilde' Q0) q r).
             apply H4. apply (Lt_parL Q0 Qtilde Qtilde' (Lrcv q r)). apply H5.
             apply (Cga_parAssoc Ptilde' Qtilde' Q0).
        (*subsubcase commR*)
                               





