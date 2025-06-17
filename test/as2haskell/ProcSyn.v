Require Export unscoped.



Section chan.
Inductive chan  : Type :=
  | var_chan : ( fin ) -> chan .

Definition subst_chan   (sigmachan : ( fin ) -> chan ) (s : chan ) : chan  :=
    match s return chan  with
    | var_chan  s => sigmachan s
    end.

Definition up_chan_chan   (sigma : ( fin ) -> chan ) : ( fin ) -> chan  :=
  (scons) ((var_chan ) (var_zero)) ((funcomp) (subst_chan ((funcomp) (var_chan ) (shift))) sigma).

Definition upId_chan_chan  (sigma : ( fin ) -> chan ) (Eq : forall x, sigma x = (var_chan ) x) : forall x, (up_chan_chan sigma) x = (var_chan ) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_chan ((funcomp) (var_chan ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition idSubst_chan  (sigmachan : ( fin ) -> chan ) (Eqchan : forall x, sigmachan x = (var_chan ) x) (s : chan ) : subst_chan sigmachan s = s :=
    match s return subst_chan sigmachan s = s with
    | var_chan  s => Eqchan s
    end.

Definition upExt_chan_chan   (sigma : ( fin ) -> chan ) (tau : ( fin ) -> chan ) (Eq : forall x, sigma x = tau x) : forall x, (up_chan_chan sigma) x = (up_chan_chan tau) x :=
  fun n => match n with
  | S fin_n => (ap) (subst_chan ((funcomp) (var_chan ) (shift))) (Eq fin_n)
  | 0  => eq_refl
  end.

Definition ext_chan   (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (Eqchan : forall x, sigmachan x = tauchan x) (s : chan ) : subst_chan sigmachan s = subst_chan tauchan s :=
    match s return subst_chan sigmachan s = subst_chan tauchan s with
    | var_chan  s => Eqchan s
    end.

Definition compSubstSubst_chan    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (thetachan : ( fin ) -> chan ) (Eqchan : forall x, ((funcomp) (subst_chan tauchan) sigmachan) x = thetachan x) (s : chan ) : subst_chan tauchan (subst_chan sigmachan s) = subst_chan thetachan s :=
    match s return subst_chan tauchan (subst_chan sigmachan s) = subst_chan thetachan s with
    | var_chan  s => Eqchan s
    end.

Definition up_subst_subst_chan_chan    (sigma : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (theta : ( fin ) -> chan ) (Eq : forall x, ((funcomp) (subst_chan tauchan) sigma) x = theta x) : forall x, ((funcomp) (subst_chan (up_chan_chan tauchan)) (up_chan_chan sigma)) x = (up_chan_chan theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compSubstSubst_chan ((funcomp) (var_chan ) (shift)) (up_chan_chan tauchan) ((funcomp) (up_chan_chan tauchan) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_chan tauchan ((funcomp) (var_chan ) (shift)) ((funcomp) (subst_chan ((funcomp) (var_chan ) (shift))) tauchan) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_chan ((funcomp) (var_chan ) (shift))) (Eq fin_n)))
  | 0  => eq_refl
  end.

Lemma instId_chan  : subst_chan (var_chan ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_chan (var_chan ) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_chan   (sigmachan : ( fin ) -> chan ) : (funcomp) (subst_chan sigmachan) (var_chan ) = sigmachan .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_chan    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (s : chan ) : subst_chan tauchan (subst_chan sigmachan s) = subst_chan ((funcomp) (subst_chan tauchan) sigmachan) s .
Proof. exact (compSubstSubst_chan sigmachan tauchan (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_chan    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) : (funcomp) (subst_chan tauchan) (subst_chan sigmachan) = subst_chan ((funcomp) (subst_chan tauchan) sigmachan) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_chan sigmachan tauchan n)). Qed.

End chan.

Section proc.
Inductive proc  : Type :=
  | Zero : proc 
  | Par : ( proc   ) -> ( proc   ) -> proc 
  | Rcv : ( chan   ) -> ( proc   ) -> proc 
  | Send : ( chan   ) -> ( chan   ) -> ( proc   ) -> proc 
  | Nu : ( proc   ) -> proc .

Lemma congr_Zero  : Zero  = Zero  .
Proof. congruence. Qed.

Lemma congr_Par  { s0 : proc   } { s1 : proc   } { t0 : proc   } { t1 : proc   } (H1 : s0 = t0) (H2 : s1 = t1) : Par  s0 s1 = Par  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Rcv  { s0 : chan   } { s1 : proc   } { t0 : chan   } { t1 : proc   } (H1 : s0 = t0) (H2 : s1 = t1) : Rcv  s0 s1 = Rcv  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Send  { s0 : chan   } { s1 : chan   } { s2 : proc   } { t0 : chan   } { t1 : chan   } { t2 : proc   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Send  s0 s1 s2 = Send  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Nu  { s0 : proc   } { t0 : proc   } (H1 : s0 = t0) : Nu  s0 = Nu  t0 .
Proof. congruence. Qed.

Fixpoint subst_proc   (sigmachan : ( fin ) -> chan ) (s : proc ) : proc  :=
    match s return proc  with
    | Zero   => Zero 
    | Par  s0 s1 => Par  ((subst_proc sigmachan) s0) ((subst_proc sigmachan) s1)
    | Rcv  s0 s1 => Rcv  ((subst_chan sigmachan) s0) ((subst_proc (up_chan_chan sigmachan)) s1)
    | Send  s0 s1 s2 => Send  ((subst_chan sigmachan) s0) ((subst_chan sigmachan) s1) ((subst_proc sigmachan) s2)
    | Nu  s0 => Nu  ((subst_proc (up_chan_chan sigmachan)) s0)
    end.

Fixpoint idSubst_proc  (sigmachan : ( fin ) -> chan ) (Eqchan : forall x, sigmachan x = (var_chan ) x) (s : proc ) : subst_proc sigmachan s = s :=
    match s return subst_proc sigmachan s = s with
    | Zero   => congr_Zero 
    | Par  s0 s1 => congr_Par ((idSubst_proc sigmachan Eqchan) s0) ((idSubst_proc sigmachan Eqchan) s1)
    | Rcv  s0 s1 => congr_Rcv ((idSubst_chan sigmachan Eqchan) s0) ((idSubst_proc (up_chan_chan sigmachan) (upId_chan_chan (_) Eqchan)) s1)
    | Send  s0 s1 s2 => congr_Send ((idSubst_chan sigmachan Eqchan) s0) ((idSubst_chan sigmachan Eqchan) s1) ((idSubst_proc sigmachan Eqchan) s2)
    | Nu  s0 => congr_Nu ((idSubst_proc (up_chan_chan sigmachan) (upId_chan_chan (_) Eqchan)) s0)
    end.

Fixpoint ext_proc   (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (Eqchan : forall x, sigmachan x = tauchan x) (s : proc ) : subst_proc sigmachan s = subst_proc tauchan s :=
    match s return subst_proc sigmachan s = subst_proc tauchan s with
    | Zero   => congr_Zero 
    | Par  s0 s1 => congr_Par ((ext_proc sigmachan tauchan Eqchan) s0) ((ext_proc sigmachan tauchan Eqchan) s1)
    | Rcv  s0 s1 => congr_Rcv ((ext_chan sigmachan tauchan Eqchan) s0) ((ext_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (upExt_chan_chan (_) (_) Eqchan)) s1)
    | Send  s0 s1 s2 => congr_Send ((ext_chan sigmachan tauchan Eqchan) s0) ((ext_chan sigmachan tauchan Eqchan) s1) ((ext_proc sigmachan tauchan Eqchan) s2)
    | Nu  s0 => congr_Nu ((ext_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (upExt_chan_chan (_) (_) Eqchan)) s0)
    end.

Fixpoint compSubstSubst_proc    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (thetachan : ( fin ) -> chan ) (Eqchan : forall x, ((funcomp) (subst_chan tauchan) sigmachan) x = thetachan x) (s : proc ) : subst_proc tauchan (subst_proc sigmachan s) = subst_proc thetachan s :=
    match s return subst_proc tauchan (subst_proc sigmachan s) = subst_proc thetachan s with
    | Zero   => congr_Zero 
    | Par  s0 s1 => congr_Par ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s1)
    | Rcv  s0 s1 => congr_Rcv ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (up_chan_chan thetachan) (up_subst_subst_chan_chan (_) (_) (_) Eqchan)) s1)
    | Send  s0 s1 s2 => congr_Send ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s1) ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s2)
    | Nu  s0 => congr_Nu ((compSubstSubst_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (up_chan_chan thetachan) (up_subst_subst_chan_chan (_) (_) (_) Eqchan)) s0)
    end.

Lemma instId_proc  : subst_proc (var_chan ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_proc (var_chan ) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_proc    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) (s : proc ) : subst_proc tauchan (subst_proc sigmachan s) = subst_proc ((funcomp) (subst_chan tauchan) sigmachan) s .
Proof. exact (compSubstSubst_proc sigmachan tauchan (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_proc    (sigmachan : ( fin ) -> chan ) (tauchan : ( fin ) -> chan ) : (funcomp) (subst_proc tauchan) (subst_proc sigmachan) = subst_proc ((funcomp) (subst_chan tauchan) sigmachan) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_proc sigmachan tauchan n)). Qed.

End proc.













Global Instance Subst_chan   : Subst1 (( fin ) -> chan ) (chan ) (chan ) := @subst_chan   .

Global Instance Subst_proc   : Subst1 (( fin ) -> chan ) (proc ) (proc ) := @subst_proc   .

Global Instance VarInstance_chan  : Var (fin) (chan ) := @var_chan  .

Notation "x '__chan'" := (var_chan x) (at level 5, format "x __chan") : subst_scope.

Notation "x '__chan'" := (@ids (_) (_) VarInstance_chan x) (at level 5, only printing, format "x __chan") : subst_scope.

Notation "'var'" := (var_chan) (only printing, at level 1) : subst_scope.

Class Up_chan X Y := up_chan : ( X ) -> Y.

Notation "↑__chan" := (up_chan) (only printing) : subst_scope.

Notation "↑__chan" := (up_chan_chan) (only printing) : subst_scope.

Global Instance Up_chan_chan   : Up_chan (_) (_) := @up_chan_chan   .

Notation "s [ sigmachan ]" := (subst_chan sigmachan s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmachan ]" := (subst_chan sigmachan) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmachan ]" := (subst_proc sigmachan s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmachan ]" := (subst_proc sigmachan) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_chan,  Subst_proc,  VarInstance_chan.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_chan,  Subst_proc,  VarInstance_chan in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_chan| progress rewrite ?compComp_chan| progress rewrite ?compComp'_chan| progress rewrite ?instId_proc| progress rewrite ?compComp_proc| progress rewrite ?compComp'_proc| progress rewrite ?varL_chan| progress (unfold up_ren, up_chan_chan)| progress (cbn [subst_chan subst_proc])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_chan in *| progress rewrite ?compComp_chan in *| progress rewrite ?compComp'_chan in *| progress rewrite ?instId_proc in *| progress rewrite ?compComp_proc in *| progress rewrite ?compComp'_proc in *| progress rewrite ?varL_chan in *| progress (unfold up_ren, up_chan_chan in *)| progress (cbn [subst_chan subst_proc] in *)| fsimpl in *].

Ltac substify := auto_unfold.

Ltac renamify := auto_unfold.
