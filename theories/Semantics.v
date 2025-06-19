
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.
Require Import Coq.Logic.FunctionalExtensionality.













 
(* the assumed setting  (Bi denotes a binder):
            
                _______ <-- current location
 nu nu  (B1...Bn    i  )
 
 today i discovered that "-" is actually a cutoff  so it actually doesn't work !*)
Definition swap_aux n i := 
 match i-n with
 | 0 => var_chan (1+n)
 | 1 => var_chan (0+n)
 | _ => var_chan i
 end.

 
(*should initially called with n=0.
n is the number of binder we have traversed 
from "Nu Nu"
up to the current point in the AST.
*)
Fixpoint swap n P := match P with
 | Zero         => Zero 
 | Par P Q      => Par (swap n P) (swap n Q)
 | Nu P         => Nu (swap (n+1) P)
 | Send (var_chan i) (var_chan j) P   =>
     let x:= (swap_aux n i) in
     let y:= (swap_aux n j) in 
     Send x y (swap n P)
 | Rcv (var_chan i) P    =>
     let x:= (swap_aux n i) in  
     Rcv x (swap (n+1) P)
 end.

  



Definition swapp (P:proc) := P [(var_chan 1) .: ( (var_chan 0) .:(fun (x:nat) => x __chan) )  ].




(*==================================*)

Definition shiftn_pr n (P:proc) := P [fun x => var_chan (n+x)].  
Definition shift_pr (P:proc) := shiftn_pr 1 P.


Inductive conga: proc -> proc -> Prop :=
| Cga_parCom: forall P Q,     conga (Par P Q)  (Par Q P)
| Cga_parAssoc: forall P Q R, conga (Par (Par P Q) R)    (Par P (Par Q R))
| Cga_parNeut: forall P,      conga (Par P Zero) P
.


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

(* =====================INCOMPLET=========================================
==============================================================*)

Inductive lab :=
| Lsend (x y: chan)
| Lrcv (x y: chan)
| LbdSend (x y: chan)
| Ltau 
.

Inductive lt: proc -> lab -> proc -> Prop :=
| Lt_send: forall x y P, lt (Send x y P) (Lsend x y) P 
| Lt_rcv: forall x P y, lt (Rcv x P) (Lrcv x y) (P [y ..]) 
| Lt_parL: forall Q P P' a, lt P a P' -> lt (Par P Q) a (Par P' Q) 
| Lt_parR: forall P Q Q' a, lt Q a Q' -> lt (Par P Q) a (Par P Q')
| Lt_commL: forall P Q P' Q' x y, 
    lt P (Lsend x y) P' -> lt Q (Lrcv x y) Q' -> lt (Par P Q) Ltau (Par P' Q')
| Lt_commR: forall P Q P' Q' x y, 
    lt P (Lrcv x y) P' -> lt Q (Lsend x y) Q' -> lt (Par P Q) Ltau (Par P' Q')
.
(*=============================================================
==============================================================*)



Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P' [y..]) )
| Red_nu: forall P Q,    red P Q -> red (Nu P) (Nu Q)
.

 
Hint Constructors congb proc conga cong lab lt red: picalc. 


Fixpoint iter_nu n P := match n with
 | 0   => P
 | S n => Nu (iter_nu n P)
 end.




