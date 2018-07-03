\<comment> \<open>SPA: Students' Proof Assistant - Anders Schlichtkrull & Jørgen Villadsen, DTU Compute, Denmark\<close>

\<comment> \<open>Based on our Archive of Formal Proofs entry https://www.isa-afp.org/entries/FOL_Harrison.shtml\<close>

\<comment> \<open>Acknowledgement: Thanks to Alexander Birch Jensen for collaboration on the first formalization\<close>

theory SPA imports Main
begin

section \<open>Syntax of First-Order Logic\<close>

type_synonym id = String.literal

datatype tm = Var id | Fn id "tm list"

datatype fm = Truth | Falsity | Rel id "tm list" | Imp fm fm | Iff fm fm | And fm fm | Or fm fm |
    Not fm | Exists id fm | Forall id fm

section \<open>Definition of Rules and Axioms on Formulas\<close>

abbreviation (input) "fail \<equiv> Truth"

definition zip_eq :: "tm list \<Rightarrow> tm list \<Rightarrow> fm list"
where
  "zip_eq l l' \<equiv> map (\<lambda>(t, t'). Rel (STR ''='') [t, t']) (zip l l')"

primrec occurs_in :: "id \<Rightarrow> tm \<Rightarrow> bool" and occurs_in_list :: "id \<Rightarrow> tm list \<Rightarrow> bool"
where
  "occurs_in i (Var x) = (i = x)" |
  "occurs_in i (Fn _ l) = occurs_in_list i l" |
  "occurs_in_list _ [] = False" |
  "occurs_in_list i (h # t) = (occurs_in i h \<or> occurs_in_list i t)"

primrec free_in :: "id \<Rightarrow> fm \<Rightarrow> bool"
where
  "free_in _ Truth = False" |
  "free_in _ Falsity = False" |
  "free_in i (Rel _ l) = occurs_in_list i l" |
  "free_in i (Imp p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Iff p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (And p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Or p q) = (free_in i p \<or> free_in i q)" |
  "free_in i (Not p) = free_in i p" |
  "free_in i (Exists x p) = (i \<noteq> x \<and> free_in i p)" |
  "free_in i (Forall x p) = (i \<noteq> x \<and> free_in i p)"

primrec equal_length :: "tm list \<Rightarrow> tm list \<Rightarrow> bool"
where
  "equal_length l [] = (case l of [] \<Rightarrow> True | _ # _ \<Rightarrow> False)" |
  "equal_length l (_ # r') = (case l of [] \<Rightarrow> False | _ # l' \<Rightarrow> equal_length l' r')"

abbreviation (input) "chain l l' p \<equiv> if equal_length l l' then foldr Imp (zip_eq l l') p else fail"

definition modusponens' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "modusponens' s s' \<equiv> case s of Imp p q \<Rightarrow> let p' = s' in if p = p' then q else fail | _ \<Rightarrow> fail"

definition gen' :: "id \<Rightarrow> fm \<Rightarrow> fm"
where
  "gen' x s \<equiv> Forall x s"

definition axiom_addimp' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_addimp' p q \<equiv> Imp p (Imp q p)"

definition axiom_distribimp' :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_distribimp' p q r \<equiv> Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))"

definition axiom_doubleneg' :: "fm \<Rightarrow> fm"
where
  "axiom_doubleneg' p \<equiv> Imp (Imp (Imp p Falsity) Falsity) p"

definition axiom_allimp' :: "id \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_allimp' x p q \<equiv> Imp (Forall x (Imp p q)) (Imp (Forall x p) (Forall x q))"

definition axiom_impall' :: "id \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_impall' x p \<equiv> if \<not> free_in x p then (Imp p (Forall x p)) else fail"

definition axiom_existseq' :: "id \<Rightarrow> tm \<Rightarrow> fm"
where
  "axiom_existseq' x t \<equiv> if \<not> occurs_in x t then Exists x (Rel (STR ''='') [Var x, t]) else fail"

definition axiom_eqrefl' :: "tm \<Rightarrow> fm"
where
  "axiom_eqrefl' t \<equiv> Rel (STR ''='') [t, t]"

definition axiom_funcong' :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fm"
where
  "axiom_funcong' i l l' \<equiv> chain l l' (Rel (STR ''='') [Fn i l, Fn i l'])"

definition axiom_predcong' :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fm"
where
  "axiom_predcong' i l l' \<equiv> chain l l' (Imp (Rel i l) (Rel i l'))"

definition axiom_iffimp1' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_iffimp1' p q \<equiv> Imp (Iff p q) (Imp p q)"

definition axiom_iffimp2' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_iffimp2' p q \<equiv> Imp (Iff p q) (Imp q p)"

definition axiom_impiff' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_impiff' p q \<equiv> Imp (Imp p q) (Imp (Imp q p) (Iff p q))"

definition axiom_true' :: fm
where
  "axiom_true' \<equiv> Iff Truth (Imp Falsity Falsity)"

definition axiom_not' :: "fm \<Rightarrow> fm"
where
  "axiom_not' p \<equiv> Iff (Not p) (Imp p Falsity)"

definition axiom_and' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_and' p q \<equiv> Iff (And p q) (Imp (Imp p (Imp q Falsity)) Falsity)"

definition axiom_or' :: "fm \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_or' p q \<equiv> Iff (Or p q) (Not (And (Not p) (Not q)))"

definition axiom_exists' :: "id \<Rightarrow> fm \<Rightarrow> fm"
where
  "axiom_exists' x p \<equiv> Iff (Exists x p) (Not (Forall x (Not p)))"

section \<open>Semantics of First-Order Logic\<close>

definition length2 :: "tm list \<Rightarrow> bool"
where
  "length2 l \<equiv> case l of [_,_] \<Rightarrow> True | _ \<Rightarrow> False"

primrec \<comment> \<open>Semantics of terms\<close>
  semantics_term :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a" and
  semantics_list :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list"
where
  "semantics_term e _ (Var x) = e x" |
  "semantics_term e f (Fn i l) = f i (semantics_list e f l)" |
  "semantics_list _ _ [] = []" |
  "semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l"

primrec \<comment> \<open>Semantics of formulas\<close>
  semantics :: "(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool"
where
  "semantics _ _ _ Truth = True" |
  "semantics _ _ _ Falsity = False" |
  "semantics e f g (Rel i l) = (if i = STR ''='' \<and> length2 l
      then (semantics_term e f (hd l) = semantics_term e f (hd (tl l)))
      else g i (semantics_list e f l))" |
  "semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)" |
  "semantics e f g (Iff p q) = (semantics e f g p \<longleftrightarrow> semantics e f g q)" |
  "semantics e f g (And p q) = (semantics e f g p \<and> semantics e f g q)" |
  "semantics e f g (Or p q) = (semantics e f g p \<or> semantics e f g q)" |
  "semantics e f g (Not p) = (\<not> semantics e f g p)" |
  "semantics e f g (Exists x p) = (\<exists>v. semantics (e(x := v)) f g p)" |
  "semantics e f g (Forall x p) = (\<forall>v. semantics (e(x := v)) f g p)"

section \<open>Definition of Proof System\<close>

inductive OK :: "fm \<Rightarrow> bool" ("\<turnstile> _" 0)
where
  "\<turnstile> s \<Longrightarrow> \<turnstile> s' \<Longrightarrow> \<turnstile> modusponens' s s'" |
  "\<turnstile> s \<Longrightarrow> \<turnstile> gen' _ s" |
  "\<turnstile> axiom_addimp' _ _" |
  "\<turnstile> axiom_distribimp' _ _ _" |
  "\<turnstile> axiom_doubleneg' _" |
  "\<turnstile> axiom_allimp' _ _ _" |
  "\<turnstile> axiom_impall' _ _" |
  "\<turnstile> axiom_existseq' _ _" |
  "\<turnstile> axiom_eqrefl' _" |
  "\<turnstile> axiom_funcong' _ _ _" |
  "\<turnstile> axiom_predcong' _ _ _" |
  "\<turnstile> axiom_iffimp1' _ _" |
  "\<turnstile> axiom_iffimp2' _ _" |
  "\<turnstile> axiom_impiff' _ _" |
  "\<turnstile> axiom_true'" |
  "\<turnstile> axiom_not' _" |
  "\<turnstile> axiom_and' _ _" |
  "\<turnstile> axiom_or' _ _" |
  "\<turnstile> axiom_exists' _ _"

proposition "\<turnstile> Imp p p"
proof -
  have 1: "\<turnstile> Imp (Imp p (Imp (Imp p p) p)) (Imp (Imp p (Imp p p)) (Imp p p))"
  using OK.intros
  unfolding axiom_distribimp'_def
  by simp

  have 2: "\<turnstile> Imp p (Imp (Imp p p) p)"
  using OK.intros
  unfolding axiom_addimp'_def
  by simp

  have 3: "\<turnstile> Imp (Imp p (Imp p p)) (Imp p p)"
  using 1 2 OK.intros(1)
  unfolding modusponens'_def
  by fastforce

  have 4: "\<turnstile> Imp p (Imp p p)"
  using OK.intros
  unfolding axiom_addimp'_def
  by simp

  have 5: "\<turnstile> Imp p p"
  using 3 4 OK.intros(1)
  unfolding modusponens'_def
  by fastforce

  show ?thesis
  using 5
  by simp
qed

section \<open>Soundness of Proof System\<close>

lemma map':
  "\<not> occurs_in x t \<Longrightarrow> semantics_term e f t = semantics_term (e(x := v)) f t"
  "\<not> occurs_in_list x l \<Longrightarrow> semantics_list e f l = semantics_list (e(x := v)) f l"
by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma map:
  "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p"
proof (induct p arbitrary: e)
  fix e
  show "\<not> free_in x Truth \<Longrightarrow> semantics e f g Truth \<longleftrightarrow> semantics (e(x := v)) f g Truth"
  by simp
next
  fix e
  show "\<not> free_in x Falsity \<Longrightarrow> semantics e f g Falsity \<longleftrightarrow> semantics (e(x := v)) f g Falsity"
  by simp
next
  fix e i l
  show "\<not> free_in x (Rel i l) \<Longrightarrow> semantics e f g (Rel i l) \<longleftrightarrow> semantics (e(x := v)) f g (Rel i l)"
  proof -
    assume assm: "\<not> free_in x (Rel i l)"
    then have fresh: "\<not> occurs_in_list x l"
    by simp
    show "semantics e f g (Rel i l) \<longleftrightarrow> semantics (e(x := v)) f g (Rel i l)"
    proof cases
      assume eq: "i = STR ''='' \<and> length2 l"
      then have "semantics e f g (Rel i l) \<longleftrightarrow>
          semantics_term e f (hd l) = semantics_term e f (hd (tl l))"
      by simp
      also have "... \<longleftrightarrow>
          semantics_term (e(x := v)) f (hd l) = semantics_term (e(x := v)) f (hd (tl l))"
      using map'(1) fresh occurs_in_list.simps(2) eq list.case_eq_if list.collapse
      unfolding length2_def
      by metis
      finally show ?thesis
      using eq
      by simp
    next
      assume not_eq: "\<not> (i = STR ''='' \<and> length2 l)"
      then have "semantics e f g (Rel i l) \<longleftrightarrow> g i (semantics_list e f l)"
      by simp iprover
      also have "... \<longleftrightarrow> g i (semantics_list (e(x := v)) f l)"
      using map'(2) fresh
      by metis
      finally show ?thesis
      using not_eq
      by simp iprover
    qed
  qed
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Imp p1 p2) \<Longrightarrow>
      semantics e f g (Imp p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Imp p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Iff p1 p2) \<Longrightarrow>
      semantics e f g (Iff p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Iff p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (And p1 p2) \<Longrightarrow>
      semantics e f g (And p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (And p1 p2)"
  using assm1 assm2
  by simp
next
  fix p1 p2 e
  assume assm1: "\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1" for e
  assume assm2: "\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2" for e
  show "\<not> free_in x (Or p1 p2) \<Longrightarrow>
      semantics e f g (Or p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Or p1 p2)"
  using assm1 assm2
  by simp
next
  fix p e
  assume "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p" for e
  then show "\<not> free_in x (Not p) \<Longrightarrow> semantics e f g (Not p) \<longleftrightarrow> semantics (e(x := v)) f g (Not p)"
  by simp
next
  fix x1 p e
  assume "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p" for e
  then show "\<not> free_in x (Exists x1 p) \<Longrightarrow>
      semantics e f g (Exists x1 p) \<longleftrightarrow> semantics (e(x := v)) f g (Exists x1 p)"
  by simp (metis fun_upd_twist fun_upd_upd)
next
  fix x1 p e
  assume "\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p" for e
  then show "\<not> free_in x (Forall x1 p) \<Longrightarrow>
      semantics e f g (Forall x1 p) \<longleftrightarrow> semantics (e(x := v)) f g (Forall x1 p)"
  by simp (metis fun_upd_twist fun_upd_upd)
qed

lemma length2_equiv:
  "length2 l \<longleftrightarrow> [hd l, hd (tl l)] = l"
proof -
  have "length2 l \<Longrightarrow> [hd l, hd (tl l)] = l"
  unfolding length2_def
  using list.case_eq_if list.exhaust_sel
  by metis
  then show ?thesis
  unfolding length2_def
  using list.case list.case_eq_if
  by metis
qed

lemma equal_length_sym:
  "equal_length l l' \<Longrightarrow> equal_length l' l"
proof (induct l' arbitrary: l)
  fix l
  assume "equal_length l []"
  then show "equal_length [] l"
  using equal_length.simps list.case_eq_if
  by metis
next
  fix l l' a
  assume sym: "equal_length l l' \<Longrightarrow> equal_length l' l" for l
  assume "equal_length l (a # l')"
  then show "equal_length (a # l') l"
  using equal_length.simps list.case_eq_if list.collapse list.inject sym
  by metis
qed

lemma equal_length2:
  "equal_length l l' \<Longrightarrow> length2 l \<longleftrightarrow> length2 l'"
proof -
  assume assm: "equal_length l l'"
  have "equal_length l [t, t'] \<Longrightarrow> length2 l" for t t'
  unfolding length2_def
  using equal_length.simps list.case_eq_if
  by metis
  moreover have "equal_length [t, t'] l' \<Longrightarrow> length2 l'" for t t'
  unfolding length2_def
  using equal_length.simps list.case_eq_if equal_length_sym
  by metis
  ultimately show ?thesis
  using assm length2_equiv
  by metis
qed

lemma imp_chain_equiv:
  "semantics e f g (foldr Imp l p) \<longleftrightarrow> (\<forall>q \<in> set l. semantics e f g q) \<longrightarrow> semantics e f g p"
using imp_conjL
by (induct l) simp_all

lemma imp_chain_zip_eq:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') p) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l' \<longrightarrow> semantics e f g p"
proof -
  assume "equal_length l l'"
  then have "(\<forall>q \<in> set (zip_eq l l'). semantics e f g q) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l'"
  unfolding zip_eq_def
  using length2_def
  by (induct l l' rule: list_induct2') simp_all
  then show ?thesis
  using imp_chain_equiv
  by iprover
qed

lemma funcong:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Rel (STR ''='') [Fn i l, Fn i l']))"
proof -
  assume assm: "equal_length l l'"
  show ?thesis
  proof cases
    assume "semantics_list e f l = semantics_list e f l'"
    then have "semantics e f g (Rel (STR ''='') [Fn i l, Fn i l'])"
    using length2_def
    by simp
    then show ?thesis
    using imp_chain_equiv
    by iprover
  next
    assume "semantics_list e f l \<noteq> semantics_list e f l'"
    then show ?thesis
    using assm imp_chain_zip_eq
    by iprover
  qed
qed

lemma predcong:
  "equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Imp (Rel i l) (Rel i l')))"
proof -
  assume assm: "equal_length l l'"
  show ?thesis
  proof cases
    assume eq: "i = STR ''='' \<and> length2 l \<and> length2 l'"
    show ?thesis
    proof cases
      assume "semantics_list e f l = semantics_list e f l'"
      then have "semantics_list e f [hd l, hd (tl l)] = semantics_list e f [hd l', hd (tl l')]"
      using eq length2_equiv
      by simp
      then have "semantics e f g (Imp (Rel (STR ''='') l) (Rel (STR ''='') l'))"
      using eq
      by simp
      then show ?thesis
      using eq imp_chain_equiv
      by iprover
    next
      assume "semantics_list e f l \<noteq> semantics_list e f l'"
      then show ?thesis
      using assm imp_chain_zip_eq
      by iprover
    qed
  next
    assume not_eq: "\<not> (i = STR ''='' \<and> length2 l \<and> length2 l')"
    show ?thesis
    proof cases
      assume "semantics_list e f l = semantics_list e f l'"
      then have "semantics e f g (Imp (Rel i l) (Rel i l'))"
      using assm not_eq equal_length2
      by simp iprover
      then show ?thesis
      using imp_chain_equiv
      by iprover
    next
      assume "semantics_list e f l \<noteq> semantics_list e f l'"
      then show ?thesis
      using assm imp_chain_zip_eq
      by iprover
    qed
  qed
qed

theorem soundness':
  "\<turnstile> p \<Longrightarrow> semantics e f g p"
proof (induct arbitrary: e rule: OK.induct)
  fix e s s'
  assume "semantics e f g s" "semantics e f g s'" for e
  then show "semantics e f g (modusponens' s s')"
  unfolding modusponens'_def
  by (cases s) simp_all
next
  fix e x s
  assume "semantics e f g s" for e
  then show "semantics e f g (gen' x s)"
  unfolding gen'_def
  by simp
next
  fix e p q
  show "semantics e f g (axiom_addimp' p q)"
  unfolding axiom_addimp'_def
  by simp
next
  fix e p q r
  show "semantics e f g (axiom_distribimp' p q r)"
  unfolding axiom_distribimp'_def
  by simp
next
  fix e g p
  show "semantics e f g (axiom_doubleneg' p)"
  unfolding axiom_doubleneg'_def
  by simp
next
  fix e x p q
  show "semantics e f g (axiom_allimp' x p q)"
  unfolding axiom_allimp'_def
  by simp
next
  fix e x p
  show "semantics e f g (axiom_impall' x p)"
  unfolding axiom_impall'_def
  using map
  by simp iprover
next
  fix e x t
  show "semantics e f g (axiom_existseq' x t)"
  unfolding axiom_existseq'_def
  using map'(1) length2_def
  by simp iprover
next
  fix e t
  show "semantics e f g (axiom_eqrefl' t)"
  unfolding axiom_eqrefl'_def
  using length2_def
  by simp
next
  fix e i l l'
  show "semantics e f g (axiom_funcong' i l l')"
  unfolding axiom_funcong'_def
  using funcong
  by simp standard
next
  fix e i l l'
  show "semantics e f g (axiom_predcong' i l l')"
  unfolding axiom_predcong'_def
  using predcong
  by simp standard
next
  fix e p q
  show "semantics e f g (axiom_iffimp1' p q)"
  unfolding axiom_iffimp1'_def
  by simp
next
  fix e p q
  show "semantics e f g (axiom_iffimp2' p q)"
  unfolding axiom_iffimp2'_def
  by simp
next
  fix e p q
  show "semantics e f g (axiom_impiff' p q)"
  unfolding axiom_impiff'_def
  by simp (rule impI, rule impI, rule iffI, erule mp, assumption, erule mp, assumption)
next
  fix e
  show "semantics e f g (axiom_true')"
  unfolding axiom_true'_def
  by simp
next
  fix e p
  show "semantics e f g (axiom_not' p)"
  unfolding axiom_not'_def
  by simp
next
  fix e p q
  show "semantics e f g (axiom_and' p q)"
  unfolding axiom_and'_def
  by simp
next
  fix e p q
  show "semantics e f g (axiom_or' p q)"
  unfolding axiom_or'_def
  by simp
next
  fix e x p
  show "semantics e f g (axiom_exists' x p)"
  unfolding axiom_exists'_def
  by simp
qed

corollary consistency': "\<not> (\<turnstile> Falsity)"
using soundness'
by fastforce

section \<open>Definition of Theorems as a Type\<close>

typedef "thm" = "{p :: fm. \<turnstile> p}"
proof -
  have "\<turnstile> axiom_addimp' Truth Truth"
    using OK.intros by auto
  then show ?thesis by blast
qed

definition "concl \<equiv> Rep_thm"
declare concl_def[simp]

setup_lifting type_definition_thm

section \<open>Soundness of Proof System as a Type\<close>

theorem soundness: "semantics e f g (concl p)"
  using soundness' Rep_thm
  by fastforce

theorem consistency: "concl p \<noteq> Falsity"
  using consistency' Rep_thm concl_def mem_Collect_eq
  by metis

section \<open>Definition of Rules and Axioms on Theorems\<close>

lift_definition modusponens :: "thm \<Rightarrow> thm \<Rightarrow> thm" is modusponens'
  using OK.intros(1) .

lift_definition gen :: "id \<Rightarrow> thm \<Rightarrow> thm" is gen'
  using OK.intros(2) .

lift_definition axiom_addimp :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_addimp'
  using OK.intros(3) .

lift_definition axiom_distribimp :: "fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_distribimp'
  using OK.intros(4) .

lift_definition axiom_doubleneg :: "fm \<Rightarrow> thm" is axiom_doubleneg'
  using OK.intros(5) .

lift_definition axiom_allimp :: "id \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_allimp'
  using OK.intros(6) .

lift_definition axiom_impall :: "id \<Rightarrow> fm \<Rightarrow> thm" is axiom_impall'
  using OK.intros(7) .

lift_definition axiom_existseq :: "id \<Rightarrow> tm \<Rightarrow> thm" is axiom_existseq'
  using OK.intros(8) .

lift_definition axiom_eqrefl :: "tm \<Rightarrow> thm" is axiom_eqrefl'
  using OK.intros(9) .

lift_definition axiom_funcong :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> thm" is axiom_funcong'
  using OK.intros(10) .

lift_definition axiom_predcong :: "id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> thm" is axiom_predcong'
  using OK.intros(11) .

lift_definition axiom_iffimp1 :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_iffimp1'
  using OK.intros(12) .

lift_definition axiom_iffimp2 :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_iffimp2'
  using OK.intros(13) .

lift_definition axiom_impiff :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_impiff'
  using OK.intros(14) .

lift_definition axiom_true :: "thm" is axiom_true'
  using OK.intros(15) .

lift_definition axiom_not :: "fm \<Rightarrow> thm" is axiom_not'
  using OK.intros(16) .

lift_definition axiom_and :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_and'
  using OK.intros(17) .

lift_definition axiom_or :: "fm \<Rightarrow> fm \<Rightarrow> thm" is axiom_or'
  using OK.intros(18) .

lift_definition axiom_exists :: "id \<Rightarrow> fm \<Rightarrow> thm" is axiom_exists'
  using OK.intros(19) .

section \<open>ML Code Reflection\<close>

code_reflect
  Proven
datatypes
  tm = Var | Fn
and
  fm = Truth | Falsity | Rel | Imp | Iff | And | Or | Not | Exists | Forall
functions
  modusponens gen axiom_addimp axiom_distribimp axiom_doubleneg axiom_allimp axiom_impall
  axiom_existseq axiom_eqrefl axiom_funcong axiom_predcong axiom_iffimp1 axiom_iffimp2
  axiom_impiff axiom_true axiom_not axiom_and axiom_or axiom_exists concl

ML_file \<open>SPA.ML\<close>

ML_val {* auto "A ==> A" *}

ML_val {* auto "exists x. D(x) ==> forall x. D(x)" *}

ML_val {* auto "(forall x. ~R(x) ==> R(f(x))) ==> exists x. R(x) /\\ R(f(f(x)))" *}

end
