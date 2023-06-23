Require Export unscoped.



Section sort.
Inductive sort  : Type :=
  | U : sort 
  | L : sort .

Lemma congr_U  : U  = U  .
Proof. congruence. Qed.

Lemma congr_L  : L  = L  .
Proof. congruence. Qed.

End sort.


Section termtele.
Inductive term  : Type :=
  | var_term : ( fin ) -> term 
  | Sort : ( sort   ) -> term 
  | Const : ( name   ) -> term 
  | Pi0 : ( term   ) -> ( term   ) -> ( sort   ) -> term 
  | Pi1 : ( term   ) -> ( term   ) -> ( sort   ) -> term 
  | Lam0 : ( term   ) -> ( term   ) -> ( sort   ) -> term 
  | Lam1 : ( term   ) -> ( term   ) -> ( sort   ) -> term 
  | App0 : ( term   ) -> ( term   ) -> term 
  | App1 : ( term   ) -> ( term   ) -> term 
  | Ind0 : ( name   ) -> ( list (term  ) ) -> term 
  | Ind1 : ( name   ) -> ( list (term  ) ) -> term 
  | Cons0 : ( name   ) -> ( list (term  ) ) -> term 
  | Cons1 : ( name   ) -> ( list (term  ) ) -> term 
  | Case0 : ( term   ) -> ( tele   ) -> ( list (tele  ) ) -> term 
  | Case1 : ( term   ) -> ( tele   ) -> ( list (tele  ) ) -> term 
  | Fix : ( term   ) -> ( term   ) -> term 
  | Bind0 : ( term   ) -> ( tele   ) -> term 
  | Bind1 : ( term   ) -> ( tele   ) -> term 
 with tele  : Type :=
  | Base : ( term   ) -> tele .

Lemma congr_Sort  { s0 : sort   } { t0 : sort   } (H1 : s0 = t0) : Sort  s0 = Sort  t0 .
Proof. congruence. Qed.

Lemma congr_Const  { s0 : name   } { t0 : name   } (H1 : s0 = t0) : Const  s0 = Const  t0 .
Proof. congruence. Qed.

Lemma congr_Pi0  { s0 : term   } { s1 : term   } { s2 : sort   } { t0 : term   } { t1 : term   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Pi0  s0 s1 s2 = Pi0  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Pi1  { s0 : term   } { s1 : term   } { s2 : sort   } { t0 : term   } { t1 : term   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Pi1  s0 s1 s2 = Pi1  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Lam0  { s0 : term   } { s1 : term   } { s2 : sort   } { t0 : term   } { t1 : term   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Lam0  s0 s1 s2 = Lam0  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Lam1  { s0 : term   } { s1 : term   } { s2 : sort   } { t0 : term   } { t1 : term   } { t2 : sort   } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Lam1  s0 s1 s2 = Lam1  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_App0  { s0 : term   } { s1 : term   } { t0 : term   } { t1 : term   } (H1 : s0 = t0) (H2 : s1 = t1) : App0  s0 s1 = App0  t0 t1 .
Proof. congruence. Qed.

Lemma congr_App1  { s0 : term   } { s1 : term   } { t0 : term   } { t1 : term   } (H1 : s0 = t0) (H2 : s1 = t1) : App1  s0 s1 = App1  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Ind0  { s0 : name   } { s1 : list (term  ) } { t0 : name   } { t1 : list (term  ) } (H1 : s0 = t0) (H2 : s1 = t1) : Ind0  s0 s1 = Ind0  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Ind1  { s0 : name   } { s1 : list (term  ) } { t0 : name   } { t1 : list (term  ) } (H1 : s0 = t0) (H2 : s1 = t1) : Ind1  s0 s1 = Ind1  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Cons0  { s0 : name   } { s1 : list (term  ) } { t0 : name   } { t1 : list (term  ) } (H1 : s0 = t0) (H2 : s1 = t1) : Cons0  s0 s1 = Cons0  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Cons1  { s0 : name   } { s1 : list (term  ) } { t0 : name   } { t1 : list (term  ) } (H1 : s0 = t0) (H2 : s1 = t1) : Cons1  s0 s1 = Cons1  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Case0  { s0 : term   } { s1 : tele   } { s2 : list (tele  ) } { t0 : term   } { t1 : tele   } { t2 : list (tele  ) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Case0  s0 s1 s2 = Case0  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Case1  { s0 : term   } { s1 : tele   } { s2 : list (tele  ) } { t0 : term   } { t1 : tele   } { t2 : list (tele  ) } (H1 : s0 = t0) (H2 : s1 = t1) (H3 : s2 = t2) : Case1  s0 s1 s2 = Case1  t0 t1 t2 .
Proof. congruence. Qed.

Lemma congr_Fix  { s0 : term   } { s1 : term   } { t0 : term   } { t1 : term   } (H1 : s0 = t0) (H2 : s1 = t1) : Fix  s0 s1 = Fix  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Bind0  { s0 : term   } { s1 : tele   } { t0 : term   } { t1 : tele   } (H1 : s0 = t0) (H2 : s1 = t1) : Bind0  s0 s1 = Bind0  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Bind1  { s0 : term   } { s1 : tele   } { t0 : term   } { t1 : tele   } (H1 : s0 = t0) (H2 : s1 = t1) : Bind1  s0 s1 = Bind1  t0 t1 .
Proof. congruence. Qed.

Lemma congr_Base  { s0 : term   } { t0 : term   } (H1 : s0 = t0) : Base  s0 = Base  t0 .
Proof. congruence. Qed.

Definition upRen_term_term   (xi : ( fin ) -> fin) : ( fin ) -> fin :=
  (up_ren) xi.

Fixpoint ren_term   (xiterm : ( fin ) -> fin) (s : term ) : term  :=
    match s return term  with
    | var_term  s => (var_term ) (xiterm s)
    | Sort  s0 => Sort  ((fun x => x) s0)
    | Const  s0 => Const  ((fun x => x) s0)
    | Pi0  s0 s1 s2 => Pi0  ((ren_term xiterm) s0) ((ren_term (upRen_term_term xiterm)) s1) ((fun x => x) s2)
    | Pi1  s0 s1 s2 => Pi1  ((ren_term xiterm) s0) ((ren_term (upRen_term_term xiterm)) s1) ((fun x => x) s2)
    | Lam0  s0 s1 s2 => Lam0  ((ren_term xiterm) s0) ((ren_term (upRen_term_term xiterm)) s1) ((fun x => x) s2)
    | Lam1  s0 s1 s2 => Lam1  ((ren_term xiterm) s0) ((ren_term (upRen_term_term xiterm)) s1) ((fun x => x) s2)
    | App0  s0 s1 => App0  ((ren_term xiterm) s0) ((ren_term xiterm) s1)
    | App1  s0 s1 => App1  ((ren_term xiterm) s0) ((ren_term xiterm) s1)
    | Ind0  s0 s1 => Ind0  ((fun x => x) s0) ((list_map (ren_term xiterm)) s1)
    | Ind1  s0 s1 => Ind1  ((fun x => x) s0) ((list_map (ren_term xiterm)) s1)
    | Cons0  s0 s1 => Cons0  ((fun x => x) s0) ((list_map (ren_term xiterm)) s1)
    | Cons1  s0 s1 => Cons1  ((fun x => x) s0) ((list_map (ren_term xiterm)) s1)
    | Case0  s0 s1 s2 => Case0  ((ren_term xiterm) s0) ((ren_tele xiterm) s1) ((list_map (ren_tele xiterm)) s2)
    | Case1  s0 s1 s2 => Case1  ((ren_term xiterm) s0) ((ren_tele xiterm) s1) ((list_map (ren_tele xiterm)) s2)
    | Fix  s0 s1 => Fix  ((ren_term xiterm) s0) ((ren_term (upRen_term_term xiterm)) s1)
    | Bind0  s0 s1 => Bind0  ((ren_term xiterm) s0) ((ren_tele (upRen_term_term xiterm)) s1)
    | Bind1  s0 s1 => Bind1  ((ren_term xiterm) s0) ((ren_tele (upRen_term_term xiterm)) s1)
    end
 with ren_tele   (xiterm : ( fin ) -> fin) (s : tele ) : tele  :=
    match s return tele  with
    | Base  s0 => Base  ((ren_term xiterm) s0)
    end.

Definition up_term_term   (sigma : ( fin ) -> term ) : ( fin ) -> term  :=
  (scons) ((var_term ) (var_zero)) ((funcomp) (ren_term (shift)) sigma).

Fixpoint subst_term   (sigmaterm : ( fin ) -> term ) (s : term ) : term  :=
    match s return term  with
    | var_term  s => sigmaterm s
    | Sort  s0 => Sort  ((fun x => x) s0)
    | Const  s0 => Const  ((fun x => x) s0)
    | Pi0  s0 s1 s2 => Pi0  ((subst_term sigmaterm) s0) ((subst_term (up_term_term sigmaterm)) s1) ((fun x => x) s2)
    | Pi1  s0 s1 s2 => Pi1  ((subst_term sigmaterm) s0) ((subst_term (up_term_term sigmaterm)) s1) ((fun x => x) s2)
    | Lam0  s0 s1 s2 => Lam0  ((subst_term sigmaterm) s0) ((subst_term (up_term_term sigmaterm)) s1) ((fun x => x) s2)
    | Lam1  s0 s1 s2 => Lam1  ((subst_term sigmaterm) s0) ((subst_term (up_term_term sigmaterm)) s1) ((fun x => x) s2)
    | App0  s0 s1 => App0  ((subst_term sigmaterm) s0) ((subst_term sigmaterm) s1)
    | App1  s0 s1 => App1  ((subst_term sigmaterm) s0) ((subst_term sigmaterm) s1)
    | Ind0  s0 s1 => Ind0  ((fun x => x) s0) ((list_map (subst_term sigmaterm)) s1)
    | Ind1  s0 s1 => Ind1  ((fun x => x) s0) ((list_map (subst_term sigmaterm)) s1)
    | Cons0  s0 s1 => Cons0  ((fun x => x) s0) ((list_map (subst_term sigmaterm)) s1)
    | Cons1  s0 s1 => Cons1  ((fun x => x) s0) ((list_map (subst_term sigmaterm)) s1)
    | Case0  s0 s1 s2 => Case0  ((subst_term sigmaterm) s0) ((subst_tele sigmaterm) s1) ((list_map (subst_tele sigmaterm)) s2)
    | Case1  s0 s1 s2 => Case1  ((subst_term sigmaterm) s0) ((subst_tele sigmaterm) s1) ((list_map (subst_tele sigmaterm)) s2)
    | Fix  s0 s1 => Fix  ((subst_term sigmaterm) s0) ((subst_term (up_term_term sigmaterm)) s1)
    | Bind0  s0 s1 => Bind0  ((subst_term sigmaterm) s0) ((subst_tele (up_term_term sigmaterm)) s1)
    | Bind1  s0 s1 => Bind1  ((subst_term sigmaterm) s0) ((subst_tele (up_term_term sigmaterm)) s1)
    end
 with subst_tele   (sigmaterm : ( fin ) -> term ) (s : tele ) : tele  :=
    match s return tele  with
    | Base  s0 => Base  ((subst_term sigmaterm) s0)
    end.

Definition upId_term_term  (sigma : ( fin ) -> term ) (Eq : forall x, sigma x = (var_term ) x) : forall x, (up_term_term sigma) x = (var_term ) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint idSubst_term  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : term ) : subst_term sigmaterm s = s :=
    match s return subst_term sigmaterm s = s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term sigmaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term sigmaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_id (idSubst_term sigmaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_id (idSubst_term sigmaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_id (idSubst_term sigmaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_id (idSubst_term sigmaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_tele sigmaterm Eqterm) s1) ((list_id (idSubst_tele sigmaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_tele sigmaterm Eqterm) s1) ((list_id (idSubst_tele sigmaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_term (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_tele (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((idSubst_term sigmaterm Eqterm) s0) ((idSubst_tele (up_term_term sigmaterm) (upId_term_term (_) Eqterm)) s1)
    end
 with idSubst_tele  (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = (var_term ) x) (s : tele ) : subst_tele sigmaterm s = s :=
    match s return subst_tele sigmaterm s = s with
    | Base  s0 => congr_Base ((idSubst_term sigmaterm Eqterm) s0)
    end.

Definition upExtRen_term_term   (xi : ( fin ) -> fin) (zeta : ( fin ) -> fin) (Eq : forall x, xi x = zeta x) : forall x, (upRen_term_term xi) x = (upRen_term_term zeta) x :=
  fun n => match n with
  | S fin_n => (ap) (shift) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint extRen_term   (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (Eqterm : forall x, xiterm x = zetaterm x) (s : term ) : ren_term xiterm s = ren_term zetaterm s :=
    match s return ren_term xiterm s = ren_term zetaterm s with
    | var_term  s => (ap) (var_term ) (Eqterm s)
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term xiterm zetaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term xiterm zetaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_ext (extRen_term xiterm zetaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_ext (extRen_term xiterm zetaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_ext (extRen_term xiterm zetaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_ext (extRen_term xiterm zetaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_tele xiterm zetaterm Eqterm) s1) ((list_ext (extRen_tele xiterm zetaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_tele xiterm zetaterm Eqterm) s1) ((list_ext (extRen_tele xiterm zetaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_tele (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((extRen_term xiterm zetaterm Eqterm) s0) ((extRen_tele (upRen_term_term xiterm) (upRen_term_term zetaterm) (upExtRen_term_term (_) (_) Eqterm)) s1)
    end
 with extRen_tele   (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (Eqterm : forall x, xiterm x = zetaterm x) (s : tele ) : ren_tele xiterm s = ren_tele zetaterm s :=
    match s return ren_tele xiterm s = ren_tele zetaterm s with
    | Base  s0 => congr_Base ((extRen_term xiterm zetaterm Eqterm) s0)
    end.

Definition upExt_term_term   (sigma : ( fin ) -> term ) (tau : ( fin ) -> term ) (Eq : forall x, sigma x = tau x) : forall x, (up_term_term sigma) x = (up_term_term tau) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint ext_term   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : term ) : subst_term sigmaterm s = subst_term tauterm s :=
    match s return subst_term sigmaterm s = subst_term tauterm s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term sigmaterm tauterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term sigmaterm tauterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_ext (ext_term sigmaterm tauterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_ext (ext_term sigmaterm tauterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_ext (ext_term sigmaterm tauterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_ext (ext_term sigmaterm tauterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_tele sigmaterm tauterm Eqterm) s1) ((list_ext (ext_tele sigmaterm tauterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_tele sigmaterm tauterm Eqterm) s1) ((list_ext (ext_tele sigmaterm tauterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_term (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_tele (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((ext_term sigmaterm tauterm Eqterm) s0) ((ext_tele (up_term_term sigmaterm) (up_term_term tauterm) (upExt_term_term (_) (_) Eqterm)) s1)
    end
 with ext_tele   (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (Eqterm : forall x, sigmaterm x = tauterm x) (s : tele ) : subst_tele sigmaterm s = subst_tele tauterm s :=
    match s return subst_tele sigmaterm s = subst_tele tauterm s with
    | Base  s0 => congr_Base ((ext_term sigmaterm tauterm Eqterm) s0)
    end.

Definition up_ren_ren_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> fin) (theta : ( fin ) -> fin) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (upRen_term_term tau) (upRen_term_term xi)) x = (upRen_term_term theta) x :=
  up_ren_ren xi tau theta Eq.

Fixpoint compRenRen_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (rhoterm : ( fin ) -> fin) (Eqterm : forall x, ((funcomp) zetaterm xiterm) x = rhoterm x) (s : term ) : ren_term zetaterm (ren_term xiterm s) = ren_term rhoterm s :=
    match s return ren_term zetaterm (ren_term xiterm s) = ren_term rhoterm s with
    | var_term  s => (ap) (var_term ) (Eqterm s)
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_comp (compRenRen_term xiterm zetaterm rhoterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_comp (compRenRen_term xiterm zetaterm rhoterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_comp (compRenRen_term xiterm zetaterm rhoterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_comp (compRenRen_term xiterm zetaterm rhoterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_tele xiterm zetaterm rhoterm Eqterm) s1) ((list_comp (compRenRen_tele xiterm zetaterm rhoterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_tele xiterm zetaterm rhoterm Eqterm) s1) ((list_comp (compRenRen_tele xiterm zetaterm rhoterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_term (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_tele (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0) ((compRenRen_tele (upRen_term_term xiterm) (upRen_term_term zetaterm) (upRen_term_term rhoterm) (up_ren_ren (_) (_) (_) Eqterm)) s1)
    end
 with compRenRen_tele    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (rhoterm : ( fin ) -> fin) (Eqterm : forall x, ((funcomp) zetaterm xiterm) x = rhoterm x) (s : tele ) : ren_tele zetaterm (ren_tele xiterm s) = ren_tele rhoterm s :=
    match s return ren_tele zetaterm (ren_tele xiterm s) = ren_tele rhoterm s with
    | Base  s0 => congr_Base ((compRenRen_term xiterm zetaterm rhoterm Eqterm) s0)
    end.

Definition up_ren_subst_term_term    (xi : ( fin ) -> fin) (tau : ( fin ) -> term ) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) tau xi) x = theta x) : forall x, ((funcomp) (up_term_term tau) (upRen_term_term xi)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint compRenSubst_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) tauterm xiterm) x = thetaterm x) (s : term ) : subst_term tauterm (ren_term xiterm s) = subst_term thetaterm s :=
    match s return subst_term tauterm (ren_term xiterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_comp (compRenSubst_term xiterm tauterm thetaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_comp (compRenSubst_term xiterm tauterm thetaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_comp (compRenSubst_term xiterm tauterm thetaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_comp (compRenSubst_term xiterm tauterm thetaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_tele xiterm tauterm thetaterm Eqterm) s1) ((list_comp (compRenSubst_tele xiterm tauterm thetaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_tele xiterm tauterm thetaterm Eqterm) s1) ((list_comp (compRenSubst_tele xiterm tauterm thetaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_term (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_tele (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0) ((compRenSubst_tele (upRen_term_term xiterm) (up_term_term tauterm) (up_term_term thetaterm) (up_ren_subst_term_term (_) (_) (_) Eqterm)) s1)
    end
 with compRenSubst_tele    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) tauterm xiterm) x = thetaterm x) (s : tele ) : subst_tele tauterm (ren_tele xiterm s) = subst_tele thetaterm s :=
    match s return subst_tele tauterm (ren_tele xiterm s) = subst_tele thetaterm s with
    | Base  s0 => congr_Base ((compRenSubst_term xiterm tauterm thetaterm Eqterm) s0)
    end.

Definition up_subst_ren_term_term    (sigma : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) (ren_term zetaterm) sigma) x = theta x) : forall x, ((funcomp) (ren_term (upRen_term_term zetaterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenRen_term (shift) (upRen_term_term zetaterm) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compRenRen_term zetaterm (shift) ((funcomp) (shift) zetaterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstRen_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (ren_term zetaterm) sigmaterm) x = thetaterm x) (s : term ) : ren_term zetaterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s return ren_term zetaterm (subst_term sigmaterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstRen_term sigmaterm zetaterm thetaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstRen_term sigmaterm zetaterm thetaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstRen_term sigmaterm zetaterm thetaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstRen_term sigmaterm zetaterm thetaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_tele sigmaterm zetaterm thetaterm Eqterm) s1) ((list_comp (compSubstRen_tele sigmaterm zetaterm thetaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_tele sigmaterm zetaterm thetaterm Eqterm) s1) ((list_comp (compSubstRen_tele sigmaterm zetaterm thetaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_term (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_tele (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0) ((compSubstRen_tele (up_term_term sigmaterm) (upRen_term_term zetaterm) (up_term_term thetaterm) (up_subst_ren_term_term (_) (_) (_) Eqterm)) s1)
    end
 with compSubstRen_tele    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (ren_term zetaterm) sigmaterm) x = thetaterm x) (s : tele ) : ren_tele zetaterm (subst_tele sigmaterm s) = subst_tele thetaterm s :=
    match s return ren_tele zetaterm (subst_tele sigmaterm s) = subst_tele thetaterm s with
    | Base  s0 => congr_Base ((compSubstRen_term sigmaterm zetaterm thetaterm Eqterm) s0)
    end.

Definition up_subst_subst_term_term    (sigma : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (theta : ( fin ) -> term ) (Eq : forall x, ((funcomp) (subst_term tauterm) sigma) x = theta x) : forall x, ((funcomp) (subst_term (up_term_term tauterm)) (up_term_term sigma)) x = (up_term_term theta) x :=
  fun n => match n with
  | S fin_n => (eq_trans) (compRenSubst_term (shift) (up_term_term tauterm) ((funcomp) (up_term_term tauterm) (shift)) (fun x => eq_refl) (sigma fin_n)) ((eq_trans) ((eq_sym) (compSubstRen_term tauterm (shift) ((funcomp) (ren_term (shift)) tauterm) (fun x => eq_refl) (sigma fin_n))) ((ap) (ren_term (shift)) (Eq fin_n)))
  | 0  => eq_refl
  end.

Fixpoint compSubstSubst_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s :=
    match s return subst_term tauterm (subst_term sigmaterm s) = subst_term thetaterm s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_comp (compSubstSubst_term sigmaterm tauterm thetaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_tele sigmaterm tauterm thetaterm Eqterm) s1) ((list_comp (compSubstSubst_tele sigmaterm tauterm thetaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_tele sigmaterm tauterm thetaterm Eqterm) s1) ((list_comp (compSubstSubst_tele sigmaterm tauterm thetaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_term (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_tele (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0) ((compSubstSubst_tele (up_term_term sigmaterm) (up_term_term tauterm) (up_term_term thetaterm) (up_subst_subst_term_term (_) (_) (_) Eqterm)) s1)
    end
 with compSubstSubst_tele    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (thetaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (subst_term tauterm) sigmaterm) x = thetaterm x) (s : tele ) : subst_tele tauterm (subst_tele sigmaterm s) = subst_tele thetaterm s :=
    match s return subst_tele tauterm (subst_tele sigmaterm s) = subst_tele thetaterm s with
    | Base  s0 => congr_Base ((compSubstSubst_term sigmaterm tauterm thetaterm Eqterm) s0)
    end.

Definition rinstInst_up_term_term   (xi : ( fin ) -> fin) (sigma : ( fin ) -> term ) (Eq : forall x, ((funcomp) (var_term ) xi) x = sigma x) : forall x, ((funcomp) (var_term ) (upRen_term_term xi)) x = (up_term_term sigma) x :=
  fun n => match n with
  | S fin_n => (ap) (ren_term (shift)) (Eq fin_n)
  | 0  => eq_refl
  end.

Fixpoint rinst_inst_term   (xiterm : ( fin ) -> fin) (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (var_term ) xiterm) x = sigmaterm x) (s : term ) : ren_term xiterm s = subst_term sigmaterm s :=
    match s return ren_term xiterm s = subst_term sigmaterm s with
    | var_term  s => Eqterm s
    | Sort  s0 => congr_Sort ((fun x => (eq_refl) x) s0)
    | Const  s0 => congr_Const ((fun x => (eq_refl) x) s0)
    | Pi0  s0 s1 s2 => congr_Pi0 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Pi1  s0 s1 s2 => congr_Pi1 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam0  s0 s1 s2 => congr_Lam0 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | Lam1  s0 s1 s2 => congr_Lam1 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1) ((fun x => (eq_refl) x) s2)
    | App0  s0 s1 => congr_App0 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term xiterm sigmaterm Eqterm) s1)
    | App1  s0 s1 => congr_App1 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term xiterm sigmaterm Eqterm) s1)
    | Ind0  s0 s1 => congr_Ind0 ((fun x => (eq_refl) x) s0) ((list_ext (rinst_inst_term xiterm sigmaterm Eqterm)) s1)
    | Ind1  s0 s1 => congr_Ind1 ((fun x => (eq_refl) x) s0) ((list_ext (rinst_inst_term xiterm sigmaterm Eqterm)) s1)
    | Cons0  s0 s1 => congr_Cons0 ((fun x => (eq_refl) x) s0) ((list_ext (rinst_inst_term xiterm sigmaterm Eqterm)) s1)
    | Cons1  s0 s1 => congr_Cons1 ((fun x => (eq_refl) x) s0) ((list_ext (rinst_inst_term xiterm sigmaterm Eqterm)) s1)
    | Case0  s0 s1 s2 => congr_Case0 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_tele xiterm sigmaterm Eqterm) s1) ((list_ext (rinst_inst_tele xiterm sigmaterm Eqterm)) s2)
    | Case1  s0 s1 s2 => congr_Case1 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_tele xiterm sigmaterm Eqterm) s1) ((list_ext (rinst_inst_tele xiterm sigmaterm Eqterm)) s2)
    | Fix  s0 s1 => congr_Fix ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_term (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1)
    | Bind0  s0 s1 => congr_Bind0 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_tele (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1)
    | Bind1  s0 s1 => congr_Bind1 ((rinst_inst_term xiterm sigmaterm Eqterm) s0) ((rinst_inst_tele (upRen_term_term xiterm) (up_term_term sigmaterm) (rinstInst_up_term_term (_) (_) Eqterm)) s1)
    end
 with rinst_inst_tele   (xiterm : ( fin ) -> fin) (sigmaterm : ( fin ) -> term ) (Eqterm : forall x, ((funcomp) (var_term ) xiterm) x = sigmaterm x) (s : tele ) : ren_tele xiterm s = subst_tele sigmaterm s :=
    match s return ren_tele xiterm s = subst_tele sigmaterm s with
    | Base  s0 => congr_Base ((rinst_inst_term xiterm sigmaterm Eqterm) s0)
    end.

Lemma rinstInst_term   (xiterm : ( fin ) -> fin) : ren_term xiterm = subst_term ((funcomp) (var_term ) xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_term xiterm (_) (fun n => eq_refl) x)). Qed.

Lemma rinstInst_tele   (xiterm : ( fin ) -> fin) : ren_tele xiterm = subst_tele ((funcomp) (var_term ) xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => rinst_inst_tele xiterm (_) (fun n => eq_refl) x)). Qed.

Lemma instId_term  : subst_term (var_term ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_term (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma instId_tele  : subst_tele (var_term ) = id .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => idSubst_tele (var_term ) (fun n => eq_refl) ((id) x))). Qed.

Lemma rinstId_term  : @ren_term   (id) = id .
Proof. exact ((eq_trans) (rinstInst_term ((id) (_))) instId_term). Qed.

Lemma rinstId_tele  : @ren_tele   (id) = id .
Proof. exact ((eq_trans) (rinstInst_tele ((id) (_))) instId_tele). Qed.

Lemma varL_term   (sigmaterm : ( fin ) -> term ) : (funcomp) (subst_term sigmaterm) (var_term ) = sigmaterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma varLRen_term   (xiterm : ( fin ) -> fin) : (funcomp) (ren_term xiterm) (var_term ) = (funcomp) (var_term ) xiterm .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun x => eq_refl)). Qed.

Lemma compComp_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : term ) : subst_term tauterm (subst_term sigmaterm s) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_term sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp_tele    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) (s : tele ) : subst_tele tauterm (subst_tele sigmaterm s) = subst_tele ((funcomp) (subst_term tauterm) sigmaterm) s .
Proof. exact (compSubstSubst_tele sigmaterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma compComp'_term    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_term tauterm) (subst_term sigmaterm) = subst_term ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_term sigmaterm tauterm n)). Qed.

Lemma compComp'_tele    (sigmaterm : ( fin ) -> term ) (tauterm : ( fin ) -> term ) : (funcomp) (subst_tele tauterm) (subst_tele sigmaterm) = subst_tele ((funcomp) (subst_term tauterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compComp_tele sigmaterm tauterm n)). Qed.

Lemma compRen_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (s : term ) : ren_term zetaterm (subst_term sigmaterm s) = subst_term ((funcomp) (ren_term zetaterm) sigmaterm) s .
Proof. exact (compSubstRen_term sigmaterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma compRen_tele    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) (s : tele ) : ren_tele zetaterm (subst_tele sigmaterm s) = subst_tele ((funcomp) (ren_term zetaterm) sigmaterm) s .
Proof. exact (compSubstRen_tele sigmaterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma compRen'_term    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetaterm) (subst_term sigmaterm) = subst_term ((funcomp) (ren_term zetaterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_term sigmaterm zetaterm n)). Qed.

Lemma compRen'_tele    (sigmaterm : ( fin ) -> term ) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_tele zetaterm) (subst_tele sigmaterm) = subst_tele ((funcomp) (ren_term zetaterm) sigmaterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => compRen_tele sigmaterm zetaterm n)). Qed.

Lemma renComp_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (s : term ) : subst_term tauterm (ren_term xiterm s) = subst_term ((funcomp) tauterm xiterm) s .
Proof. exact (compRenSubst_term xiterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma renComp_tele    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) (s : tele ) : subst_tele tauterm (ren_tele xiterm s) = subst_tele ((funcomp) tauterm xiterm) s .
Proof. exact (compRenSubst_tele xiterm tauterm (_) (fun n => eq_refl) s). Qed.

Lemma renComp'_term    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) : (funcomp) (subst_term tauterm) (ren_term xiterm) = subst_term ((funcomp) tauterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_term xiterm tauterm n)). Qed.

Lemma renComp'_tele    (xiterm : ( fin ) -> fin) (tauterm : ( fin ) -> term ) : (funcomp) (subst_tele tauterm) (ren_tele xiterm) = subst_tele ((funcomp) tauterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renComp_tele xiterm tauterm n)). Qed.

Lemma renRen_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (s : term ) : ren_term zetaterm (ren_term xiterm s) = ren_term ((funcomp) zetaterm xiterm) s .
Proof. exact (compRenRen_term xiterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma renRen_tele    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) (s : tele ) : ren_tele zetaterm (ren_tele xiterm s) = ren_tele ((funcomp) zetaterm xiterm) s .
Proof. exact (compRenRen_tele xiterm zetaterm (_) (fun n => eq_refl) s). Qed.

Lemma renRen'_term    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_term zetaterm) (ren_term xiterm) = ren_term ((funcomp) zetaterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_term xiterm zetaterm n)). Qed.

Lemma renRen'_tele    (xiterm : ( fin ) -> fin) (zetaterm : ( fin ) -> fin) : (funcomp) (ren_tele zetaterm) (ren_tele xiterm) = ren_tele ((funcomp) zetaterm xiterm) .
Proof. exact ((FunctionalExtensionality.functional_extensionality _ _ ) (fun n => renRen_tele xiterm zetaterm n)). Qed.

End termtele.







































Global Instance Subst_term   : Subst1 (( fin ) -> term ) (term ) (term ) := @subst_term   .

Global Instance Subst_tele   : Subst1 (( fin ) -> term ) (tele ) (tele ) := @subst_tele   .

Global Instance Ren_term   : Ren1 (( fin ) -> fin) (term ) (term ) := @ren_term   .

Global Instance Ren_tele   : Ren1 (( fin ) -> fin) (tele ) (tele ) := @ren_tele   .

Global Instance VarInstance_term  : Var (fin) (term ) := @var_term  .

Notation "x '__term'" := (var_term x) (at level 5, format "x __term") : subst_scope.

Notation "x '__term'" := (@ids (_) (_) VarInstance_term x) (at level 5, only printing, format "x __term") : subst_scope.

Notation "'var'" := (var_term) (only printing, at level 1) : subst_scope.

Class Up_term X Y := up_term : ( X ) -> Y.

Notation "↑__term" := (up_term) (only printing) : subst_scope.

Notation "↑__term" := (up_term_term) (only printing) : subst_scope.

Global Instance Up_term_term   : Up_term (_) (_) := @up_term_term   .

Notation "s [ sigmaterm ]" := (subst_term sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_term sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiterm ⟩" := (ren_term xiterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiterm ⟩" := (ren_term xiterm) (at level 1, left associativity, only printing) : fscope.

Notation "s [ sigmaterm ]" := (subst_tele sigmaterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "[ sigmaterm ]" := (subst_tele sigmaterm) (at level 1, left associativity, only printing) : fscope.

Notation "s ⟨ xiterm ⟩" := (ren_tele xiterm s) (at level 7, left associativity, only printing) : subst_scope.

Notation "⟨ xiterm ⟩" := (ren_tele xiterm) (at level 1, left associativity, only printing) : fscope.

Ltac auto_unfold := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_tele,  Ren_term,  Ren_tele,  VarInstance_term.

Tactic Notation "auto_unfold" "in" "*" := repeat unfold subst1,  subst2,  Subst1,  Subst2,  ids,  ren1,  ren2,  Ren1,  Ren2,  Subst_term,  Subst_tele,  Ren_term,  Ren_tele,  VarInstance_term in *.

Ltac asimpl' := repeat first [progress rewrite ?instId_term| progress rewrite ?compComp_term| progress rewrite ?compComp'_term| progress rewrite ?instId_tele| progress rewrite ?compComp_tele| progress rewrite ?compComp'_tele| progress rewrite ?rinstId_term| progress rewrite ?compRen_term| progress rewrite ?compRen'_term| progress rewrite ?renComp_term| progress rewrite ?renComp'_term| progress rewrite ?renRen_term| progress rewrite ?renRen'_term| progress rewrite ?rinstId_tele| progress rewrite ?compRen_tele| progress rewrite ?compRen'_tele| progress rewrite ?renComp_tele| progress rewrite ?renComp'_tele| progress rewrite ?renRen_tele| progress rewrite ?renRen'_tele| progress rewrite ?varL_term| progress rewrite ?varLRen_term| progress (unfold up_ren, upRen_term_term, up_term_term)| progress (cbn [subst_term subst_tele ren_term ren_tele])| fsimpl].

Ltac asimpl := repeat try unfold_funcomp; auto_unfold in *; asimpl'; repeat try unfold_funcomp.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case (asimpl; cbn; eauto).

Tactic Notation "asimpl" "in" "*" := auto_unfold in *; repeat first [progress rewrite ?instId_term in *| progress rewrite ?compComp_term in *| progress rewrite ?compComp'_term in *| progress rewrite ?instId_tele in *| progress rewrite ?compComp_tele in *| progress rewrite ?compComp'_tele in *| progress rewrite ?rinstId_term in *| progress rewrite ?compRen_term in *| progress rewrite ?compRen'_term in *| progress rewrite ?renComp_term in *| progress rewrite ?renComp'_term in *| progress rewrite ?renRen_term in *| progress rewrite ?renRen'_term in *| progress rewrite ?rinstId_tele in *| progress rewrite ?compRen_tele in *| progress rewrite ?compRen'_tele in *| progress rewrite ?renComp_tele in *| progress rewrite ?renComp'_tele in *| progress rewrite ?renRen_tele in *| progress rewrite ?renRen'_tele in *| progress rewrite ?varL_term in *| progress rewrite ?varLRen_term in *| progress (unfold up_ren, upRen_term_term, up_term_term in *)| progress (cbn [subst_term subst_tele ren_term ren_tele] in *)| fsimpl in *].

Ltac substify := auto_unfold; try repeat (erewrite rinstInst_term); try repeat (erewrite rinstInst_tele).

Ltac renamify := auto_unfold; try repeat (erewrite <- rinstInst_term); try repeat (erewrite <- rinstInst_tele).
