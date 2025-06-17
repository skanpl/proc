Require Export fintype.



Section chan.
Inductive chan (nchan : nat) : Type :=
  | var_chan : (fin) (nchan) -> chan (nchan).

Definition subst_chan { mchan : nat } { nchan : nat } (sigmachan : (fin) (mchan) -> chan (nchan)) (s : chan (mchan)) : chan (nchan) :=
    match s return chan (nchan) with
    | var_chan (_) s => sigmachan s
    end.

Definition up_chan_chan { m : nat } { nchan : nat } (sigma : (fin) (m) -> chan (nchan)) : (fin) ((S) (m)) -> chan ((S) nchan) :=
  (scons) ((var_chan ((S) nchan)) (var_zero)) ((funcomp) (subst_chan ((funcomp) (var_chan (_)) (shift))) sigma).

Definition upId_chan_chan { mchan : nat } (sigma : (fin) (mchan) -> chan (mchan)) (Eq : forall x, sigma x = (var_chan (mchan)) x) : forall x, (up_chan_chan sigma) x = (var_chan ((S) mchan)) x :=
  fun n => match n with
  | Some fin_n => (ap) (subst_chan ((funcomp) (var_chan (_)) (shift))) (Eq fin_n)
  | None  => eq_refl
  end.

Definition idSubst_chan { mchan : nat } (sigmachan : (fin) (mchan) -> chan (mchan)) (Eqchan : forall x, sigmachan x = (var_chan (mchan)) x) (s : chan (mchan)) : subst_chan sigmachan s = s :=
    match s return subst_chan sigmachan s = s with
    | var_chan (_) s => Eqchan s
    end.

Definition upExt_chan_chan { m : nat } { nchan : nat } (sigma : (fin) (m) -> chan (nchan)) (tau : (fin) (m) -> chan (nchan)) (Eq : forall x, sigma x = tau x) : forall x, (up_chan_chan sigma) x = (up_chan_chan tau) x :=
  fun n => match n with
  | Some fin_n => (ap) (subst_chan ((funcomp) (var_chan (_)) (shift))) (Eq fin_n)
  | None  => eq_refl
  end.

Definition ext_chan { mchan : nat } { nchan : nat } (sigmachan : (fin) (mchan) -> chan (nchan)) (tauchan : (fin) (mchan) -> chan (nchan)) (Eqchan : forall x, sigmachan x = tauchan x) (s : chan (mchan)) : subst_chan sigmachan s = subst_chan tauchan s :=
    match s return subst_chan sigmachan s = subst_chan tauchan s with
    | var_chan (_) s => Eqchan s
    end.

Definition compSubstSubst_chan { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) (thetachan : (fin) (mchan) -> chan (lchan)) (Eqchan : forall x, ((funcomp) (subst_chan tauchan) sigmachan) x = thetachan x) (s : chan (mchan)) : subst_chan tauchan (subst_chan sigmachan s) = subst_chan thetachan s :=
    match s return subst_chan tauchan (subst_chan sigmachan s) = subst_chan thetachan s with
    | var_chan (_) s => Eqchan s
    end.

Definition up_subst_subst_chan_chan { k : nat } { lchan : nat } { mchan : nat } (sigma : (fin) (k) -> chan (lchan)) (tauchan : (fin) (lchan) -> chan (mchan)) (theta : (fin) (k) -> chan (mchan)) (Eq : forall x, ((funcomp) (subst_chan tauchan) sigma) x = theta x) : forall x, ((funcomp) (subst_chan (up_chan_chan tauchan)) (up_chan_chan sigma)) x = (up_chan_chan theta) x :=
  fun n => match n with
  | Some fin_n => (eq_trans) (compSubstSubst_chan ((funcomp) (var_chan (_)) (shift)) (up_chan_chan tauchan) ((funcomp) (up_chan_chan tauchan) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstSubst_chan tauchan ((funcomp) (var_chan (_)) (shift)) ((funcomp) (subst_chan ((funcomp) (var_chan (_)) (shift))) tauchan) (fun x => eq_refl) (sigma fin_n))) ((ap) (subst_chan ((funcomp) (var_chan (_)) (shift))) (Eq fin_n)))
  | None  => eq_refl
  end.

Lemma instId_chan { mchan : nat } : subst_chan (var_chan (mchan)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_chan (var_chan (mchan)) (fun n => eq_refl) ((id) x))). Qed.

Lemma varL_chan { mchan : nat } { nchan : nat } (sigmachan : (fin) (mchan) -> chan (nchan)) : (funcomp) (subst_chan sigmachan) (var_chan (mchan)) = sigmachan .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_chan { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) (s : chan (mchan)) : subst_chan tauchan (subst_chan sigmachan s) = subst_chan ((funcomp) (subst_chan tauchan) sigmachan) s .
Proof. exact (compSubstSubst_chan sigmachan tauchan (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_chan { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) : (funcomp) (subst_chan tauchan) (subst_chan sigmachan) = subst_chan ((funcomp) (subst_chan tauchan) sigmachan) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_chan sigmachan tauchan n)). Qed.

End chan.

Section proc.
Inductive proc (nchan : nat) : Type :=
  | Zero : proc (nchan)
  | Par : proc  (nchan) -> proc  (nchan) -> proc (nchan)
  | Rcv : chan  (nchan) -> proc  ((S) nchan) -> proc (nchan)
  | Send : chan  (nchan) -> chan  (nchan) -> proc  (nchan) -> proc (nchan)
  | Nu : proc  ((S) nchan) -> proc (nchan).

Lemma congr_Zero { mchan : nat } : Zero (mchan) = Zero (mchan) .
Proof. congruence. Qed.

Lemma congr_Par { mchan : nat } { s0 : proc  (mchan) } { s1 : proc  (mchan) } { t0 : proc  (mchan) } { t1 : proc  (mchan) } (H1 : s0 = t0) (H2 : s1 = t1) : Par (mchan) s0 s1 = Par (mchan) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Rcv { mchan : nat } { s0 : chan  (mchan) } { s1 : proc  ((S) mchan) } { t0 : chan  (mchan) } { t1 : proc  ((S) mchan) } (H1 : s0 = t0) (H2 : s1 = t1) : Rcv (mchan) s0 s1 = Rcv (mchan) t0 t1 .
Proof. congruence. Qed.

Lemma congr_Send { mchan : nat } { s0 : chan  (mchan) } { s1 : chan  (mchan) } { s2 : proc  (mchan) } { t0 : chan  (mchan) } { t1 : chan  (mchan) } { t2 : proc  (mchan) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Send (mchan) s0 s1 s2 = Send (mchan) t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Nu { mchan : nat } { s0 : proc  ((S) mchan) } { t0 : proc  ((S) mchan) } (H1 : s0 = t0) : Nu (mchan) s0 = Nu (mchan) t0 .
Proof. congruence. Qed.

Fixpoint subst_proc { mchan : nat } { nchan : nat } (sigmachan : (fin) (mchan) -> chan (nchan)) (s : proc (mchan)) : proc (nchan) :=
    match s return proc (nchan) with
    | Zero (_)  => Zero (nchan)
    | Par (_) s0 s1 => Par (nchan) ((subst_proc sigmachan) s0) ((subst_proc sigmachan) s1)
    | Rcv (_) s0 s1 => Rcv (nchan) ((subst_chan sigmachan) s0) ((subst_proc (up_chan_chan sigmachan)) s1)
    | Send (_) s0 s1 s2 => Send (nchan) ((subst_chan sigmachan) s0) ((subst_chan sigmachan) s1) ((subst_proc sigmachan) s2)
    | Nu (_) s0 => Nu (nchan) ((subst_proc (up_chan_chan sigmachan)) s0)
    end.

Fixpoint idSubst_proc { mchan : nat } (sigmachan : (fin) (mchan) -> chan (mchan)) (Eqchan : forall x, sigmachan x = (var_chan (mchan)) x) (s : proc (mchan)) : subst_proc sigmachan s = s :=
    match s return subst_proc sigmachan s = s with
    | Zero (_)  => congr_Zero 
    | Par (_) s0 s1 => congr_Par ((idSubst_proc sigmachan Eqchan) s0) ((idSubst_proc sigmachan Eqchan) s1)
    | Rcv (_) s0 s1 => congr_Rcv ((idSubst_chan sigmachan Eqchan) s0) ((idSubst_proc (up_chan_chan sigmachan) (upId_chan_chan (_) Eqchan)) s1)
    | Send (_) s0 s1 s2 => congr_Send ((idSubst_chan sigmachan Eqchan) s0) ((idSubst_chan sigmachan Eqchan) s1) ((idSubst_proc sigmachan Eqchan) s2)
    | Nu (_) s0 => congr_Nu ((idSubst_proc (up_chan_chan sigmachan) (upId_chan_chan (_) Eqchan)) s0)
    end.

Fixpoint ext_proc { mchan : nat } { nchan : nat } (sigmachan : (fin) (mchan) -> chan (nchan)) (tauchan : (fin) (mchan) -> chan (nchan)) (Eqchan : forall x, sigmachan x = tauchan x) (s : proc (mchan)) : subst_proc sigmachan s = subst_proc tauchan s :=
    match s return subst_proc sigmachan s = subst_proc tauchan s with
    | Zero (_)  => congr_Zero 
    | Par (_) s0 s1 => congr_Par ((ext_proc sigmachan tauchan Eqchan) s0) ((ext_proc sigmachan tauchan Eqchan) s1)
    | Rcv (_) s0 s1 => congr_Rcv ((ext_chan sigmachan tauchan Eqchan) s0) ((ext_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (upExt_chan_chan (_) (_) Eqchan)) s1)
    | Send (_) s0 s1 s2 => congr_Send ((ext_chan sigmachan tauchan Eqchan) s0) ((ext_chan sigmachan tauchan Eqchan) s1) ((ext_proc sigmachan tauchan Eqchan) s2)
    | Nu (_) s0 => congr_Nu ((ext_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (upExt_chan_chan (_) (_) Eqchan)) s0)
    end.

Fixpoint compSubstSubst_proc { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) (thetachan : (fin) (mchan) -> chan (lchan)) (Eqchan : forall x, ((funcomp) (subst_chan tauchan) sigmachan) x = thetachan x) (s : proc (mchan)) : subst_proc tauchan (subst_proc sigmachan s) = subst_proc thetachan s :=
    match s return subst_proc tauchan (subst_proc sigmachan s) = subst_proc thetachan s with
    | Zero (_)  => congr_Zero 
    | Par (_) s0 s1 => congr_Par ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s1)
    | Rcv (_) s0 s1 => congr_Rcv ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (up_chan_chan thetachan) (up_subst_subst_chan_chan (_) (_) (_) Eqchan)) s1)
    | Send (_) s0 s1 s2 => congr_Send ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s0) ((compSubstSubst_chan sigmachan tauchan thetachan Eqchan) s1) ((compSubstSubst_proc sigmachan tauchan thetachan Eqchan) s2)
    | Nu (_) s0 => congr_Nu ((compSubstSubst_proc (up_chan_chan sigmachan) (up_chan_chan tauchan) (up_chan_chan thetachan) (up_subst_subst_chan_chan (_) (_) (_) Eqchan)) s0)
    end.

Lemma instId_proc { mchan : nat } : subst_proc (var_chan (mchan)) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_proc (var_chan (mchan)) (fun n => eq_refl) ((id) x))). Qed.

Lemma compComp_proc { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) (s : proc (mchan)) : subst_proc tauchan (subst_proc sigmachan s) = subst_proc ((funcomp) (subst_chan tauchan) sigmachan) s .
Proof. exact (compSubstSubst_proc sigmachan tauchan (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_proc { kchan : nat } { lchan : nat } { mchan : nat } (sigmachan : (fin) (mchan) -> chan (kchan)) (tauchan : (fin) (kchan) -> chan (lchan)) : (funcomp) (subst_proc tauchan) (subst_proc sigmachan) = subst_proc ((funcomp) (subst_chan tauchan) sigmachan) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_proc sigmachan tauchan n)). Qed.

End proc.

Arguments var_chan {nchan}.

Arguments Zero {nchan}.

Arguments Par {nchan}.

Arguments Rcv {nchan}.

Arguments Send {nchan}.

Arguments Nu {nchan}.

Global Instance Subst_chan { mchan : nat } { nchan : nat } : Subst1 ((fin) (mchan) -> chan (nchan)) (chan (mchan)) (chan (nchan)) := @subst_chan (mchan) (nchan) .

Global Instance Subst_proc { mchan : nat } { nchan : nat } : Subst1 ((fin) (mchan) -> chan (nchan)) (proc (mchan)) (proc (nchan)) := @subst_proc (mchan) (nchan) .

Global Instance VarInstance_chan { mchan : nat } : Var ((fin) (mchan)) (chan (mchan)) := @var_chan (mchan) .

Notation "x '__chan'" := (var_chan x) (at level 5, format "x __chan") : subst_scope.

Notation "x '__chan'" := (@ids (_) (_) VarInstance_chan x) (at level 5, only printing, format "x __chan") : subst_scope.

Notation "'var'" := (var_chan) (only printing, at level 1) : subst_scope.

Class Up_chan X Y := up_chan : X -> Y.

Notation "↑__chan" := (up_chan) (only printing) : subst_scope.

Notation "↑__chan" := (up_chan_chan) (only printing) : subst_scope.

Global Instance Up_chan_chan { m : nat } { nchan : nat } : Up_chan (_) (_) := @up_chan_chan (m) (nchan) .

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
