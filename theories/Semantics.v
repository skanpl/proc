
Require Import ProcSyn.
Require Import unscoped.
Require Import core.
Import ProcSyn.Core.
Import unscoped.UnscopedNotations.

(*Open Scope subst_scope.

Locate ".:".
Print subst_proc.

Definition foo (x:chan) (P:proc) := P  [x ..]. 
Definition bar (sigma : nat -> chan) (P:proc) := P  [sigma]. 
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



Inductive lab :=
| Lsend (x y: chan)
| Lrcv (x y: chan)
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



Inductive red: proc -> proc -> Prop :=
| Red_par: forall P Q R, red P Q -> red (Par P R) (Par Q R)
| Red_struc: forall P P' Q Q',  cong P P' -> red P' Q' -> cong Q Q' -> red P Q
| Red_comm: forall x y P P', red (Par (Send x y P) (Rcv x P')) (Par P (P' [y..]) )
.



 
Hint Constructors proc conga cong lab lt red: picalc. 












(*

  x!y.0| x?(z).z!w.0  ---->  0|y!w.0 



Definition x := var_chan 10.
Definition y := var_chan 20.
Definition z := var_chan 0.
Definition w := var_chan 30.

Definition P1 := Send x y Zero.
Definition P2 := Rcv x (Send z w Zero).
Definition P := Par P1 P2.

Definition res := Par Zero (Send y w Zero).

Axiom skip: forall A, A.

Proposition test: red P res.
Proof.
unfold P. unfold res.
unfold P1. unfold P2. 
try apply (Red_comm x y Zero ((Send z w Zero)) ).
assert ( (Send z w Zero)[y..]  = (Send y w Zero) ) .
asimpl.
unfold y,w .
*)

