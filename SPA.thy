\<comment> \<open>SPA: Students' Proof Assistant - Anders Schlichtkrull & Jørgen Villadsen, DTU Compute, Denmark\<close>

\<comment> \<open>Based on our Archive of Formal Proofs entry https://www.isa-afp.org/entries/FOL_Harrison.shtml\<close>

\<comment> \<open>Acknowledgement: Thanks to Alexander Birch Jensen for collaboration on the first formalization\<close>

theory SPA imports Main
begin

section \<open>Syntax of First-Order Logic\<close>

type_synonym id = String.literal

datatype tm = Var id | Fun id \<open>tm list\<close>

datatype fm = Truth | Falsity | Pre id \<open>tm list\<close> | Imp fm fm | Iff fm fm | Con fm fm | Dis fm fm |
  Neg fm | Exi id fm | Uni id fm

section \<open>Definition of Rules and Axioms on Formulas\<close>

abbreviation (input) \<open>fail \<equiv> Truth\<close>

definition zip_eq :: \<open>tm list \<Rightarrow> tm list \<Rightarrow> fm list\<close>
  where
    \<open>zip_eq l l' \<equiv> map (\<lambda>(t, t'). Pre (STR ''='') [t, t']) (zip l l')\<close>

primrec occurs_in :: \<open>id \<Rightarrow> tm \<Rightarrow> bool\<close> and occurs_in_list :: \<open>id \<Rightarrow> tm list \<Rightarrow> bool\<close>
  where
    \<open>occurs_in i (Var x) = (i = x)\<close> |
    \<open>occurs_in i (Fun _ l) = occurs_in_list i l\<close> |
    \<open>occurs_in_list _ [] = False\<close> |
    \<open>occurs_in_list i (h # t) = (occurs_in i h \<or> occurs_in_list i t)\<close>

primrec free_in :: \<open>id \<Rightarrow> fm \<Rightarrow> bool\<close>
  where
    \<open>free_in _ Truth = False\<close> |
    \<open>free_in _ Falsity = False\<close> |
    \<open>free_in i (Pre _ l) = occurs_in_list i l\<close> |
    \<open>free_in i (Imp p q) = (free_in i p \<or> free_in i q)\<close> |
    \<open>free_in i (Iff p q) = (free_in i p \<or> free_in i q)\<close> |
    \<open>free_in i (Con p q) = (free_in i p \<or> free_in i q)\<close> |
    \<open>free_in i (Dis p q) = (free_in i p \<or> free_in i q)\<close> |
    \<open>free_in i (Neg p) = free_in i p\<close> |
    \<open>free_in i (Exi x p) = (i \<noteq> x \<and> free_in i p)\<close> |
    \<open>free_in i (Uni x p) = (i \<noteq> x \<and> free_in i p)\<close>

primrec equal_length :: \<open>tm list \<Rightarrow> tm list \<Rightarrow> bool\<close>
  where
    \<open>equal_length l [] = (case l of [] \<Rightarrow> True | _ # _ \<Rightarrow> False)\<close> |
    \<open>equal_length l (_ # r') = (case l of [] \<Rightarrow> False | _ # l' \<Rightarrow> equal_length l' r')\<close>

abbreviation (input) \<open>chain l l' p \<equiv> if equal_length l l' then foldr Imp (zip_eq l l') p else fail\<close>

definition modusponens' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>modusponens' s s' \<equiv> case s of Imp p q \<Rightarrow> let p' = s' in if p = p' then q else fail | _ \<Rightarrow> fail\<close>

definition gen' :: \<open>id \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>gen' x s \<equiv> Uni x s\<close>

definition axiom_addimp' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_addimp' p q \<equiv> Imp p (Imp q p)\<close>

definition axiom_distribimp' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_distribimp' p q r \<equiv> Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r))\<close>

definition axiom_doubleneg' :: \<open>fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_doubleneg' p \<equiv> Imp (Imp (Imp p Falsity) Falsity) p\<close>

definition axiom_allimp' :: \<open>id \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_allimp' x p q \<equiv> Imp (Uni x (Imp p q)) (Imp (Uni x p) (Uni x q))\<close>

definition axiom_impall' :: \<open>id \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_impall' x p \<equiv> if \<not> free_in x p then (Imp p (Uni x p)) else fail\<close>

definition axiom_existseq' :: \<open>id \<Rightarrow> tm \<Rightarrow> fm\<close>
  where
    \<open>axiom_existseq' x t \<equiv> if \<not> occurs_in x t then Exi x (Pre (STR ''='') [Var x, t]) else fail\<close>

definition axiom_eqrefl' :: \<open>tm \<Rightarrow> fm\<close>
  where
    \<open>axiom_eqrefl' t \<equiv> Pre (STR ''='') [t, t]\<close>

definition axiom_funcong' :: \<open>id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fm\<close>
  where
    \<open>axiom_funcong' i l l' \<equiv> chain l l' (Pre (STR ''='') [Fun i l, Fun i l'])\<close>

definition axiom_predcong' :: \<open>id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> fm\<close>
  where
    \<open>axiom_predcong' i l l' \<equiv> chain l l' (Imp (Pre i l) (Pre i l'))\<close>

definition axiom_iffimp1' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_iffimp1' p q \<equiv> Imp (Iff p q) (Imp p q)\<close>

definition axiom_iffimp2' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_iffimp2' p q \<equiv> Imp (Iff p q) (Imp q p)\<close>

definition axiom_impiff' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_impiff' p q \<equiv> Imp (Imp p q) (Imp (Imp q p) (Iff p q))\<close>

definition axiom_true' :: fm
  where
    \<open>axiom_true' \<equiv> Iff Truth (Imp Falsity Falsity)\<close>

definition axiom_not' :: \<open>fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_not' p \<equiv> Iff (Neg p) (Imp p Falsity)\<close>

definition axiom_and' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_and' p q \<equiv> Iff (Con p q) (Imp (Imp p (Imp q Falsity)) Falsity)\<close>

definition axiom_or' :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_or' p q \<equiv> Iff (Dis p q) (Neg (Con (Neg p) (Neg q)))\<close>

definition axiom_exists' :: \<open>id \<Rightarrow> fm \<Rightarrow> fm\<close>
  where
    \<open>axiom_exists' x p \<equiv> Iff (Exi x p) (Neg (Uni x (Neg p)))\<close>

section \<open>Semantics of First-Order Logic\<close>

definition length2 :: \<open>tm list \<Rightarrow> bool\<close>
  where
    \<open>length2 l \<equiv> case l of [_,_] \<Rightarrow> True | _ \<Rightarrow> False\<close>

primrec \<comment> \<open>Semantics of terms\<close>
  semantics_term :: \<open>(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm \<Rightarrow> 'a\<close> and
  semantics_list :: \<open>(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> tm list \<Rightarrow> 'a list\<close>
  where
    \<open>semantics_term e _ (Var x) = e x\<close> |
    \<open>semantics_term e f (Fun i l) = f i (semantics_list e f l)\<close> |
    \<open>semantics_list _ _ [] = []\<close> |
    \<open>semantics_list e f (t # l) = semantics_term e f t # semantics_list e f l\<close>

primrec \<comment> \<open>Semantics of formulas\<close>
  semantics :: \<open>(id \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> 'a) \<Rightarrow> (id \<Rightarrow> 'a list \<Rightarrow> bool) \<Rightarrow> fm \<Rightarrow> bool\<close>
  where
    \<open>semantics _ _ _ Truth = True\<close> |
    \<open>semantics _ _ _ Falsity = False\<close> |
    \<open>semantics e f g (Pre i l) = (if i = STR ''='' \<and> length2 l
      then (semantics_term e f (hd l) = semantics_term e f (hd (tl l)))
      else g i (semantics_list e f l))\<close> |
    \<open>semantics e f g (Imp p q) = (semantics e f g p \<longrightarrow> semantics e f g q)\<close> |
    \<open>semantics e f g (Iff p q) = (semantics e f g p \<longleftrightarrow> semantics e f g q)\<close> |
    \<open>semantics e f g (Con p q) = (semantics e f g p \<and> semantics e f g q)\<close> |
    \<open>semantics e f g (Dis p q) = (semantics e f g p \<or> semantics e f g q)\<close> |
    \<open>semantics e f g (Neg p) = (\<not> semantics e f g p)\<close> |
    \<open>semantics e f g (Exi x p) = (\<exists>v. semantics (e(x := v)) f g p)\<close> |
    \<open>semantics e f g (Uni x p) = (\<forall>v. semantics (e(x := v)) f g p)\<close>

section \<open>Definition of Proof System\<close>

inductive OK :: \<open>fm \<Rightarrow> bool\<close> ("\<turnstile> _" 0)
  where
    \<open>\<turnstile> s \<Longrightarrow> \<turnstile> s' \<Longrightarrow> \<turnstile> modusponens' s s'\<close> |
    \<open>\<turnstile> s \<Longrightarrow> \<turnstile> gen' _ s\<close> |
    \<open>\<turnstile> axiom_addimp' _ _\<close> |
    \<open>\<turnstile> axiom_distribimp' _ _ _\<close> |
    \<open>\<turnstile> axiom_doubleneg' _\<close> |
    \<open>\<turnstile> axiom_allimp' _ _ _\<close> |
    \<open>\<turnstile> axiom_impall' _ _\<close> |
    \<open>\<turnstile> axiom_existseq' _ _\<close> |
    \<open>\<turnstile> axiom_eqrefl' _\<close> |
    \<open>\<turnstile> axiom_funcong' _ _ _\<close> |
    \<open>\<turnstile> axiom_predcong' _ _ _\<close> |
    \<open>\<turnstile> axiom_iffimp1' _ _\<close> |
    \<open>\<turnstile> axiom_iffimp2' _ _\<close> |
    \<open>\<turnstile> axiom_impiff' _ _\<close> |
    \<open>\<turnstile> axiom_true'\<close> |
    \<open>\<turnstile> axiom_not' _\<close> |
    \<open>\<turnstile> axiom_and' _ _\<close> |
    \<open>\<turnstile> axiom_or' _ _\<close> |
    \<open>\<turnstile> axiom_exists' _ _\<close>

proposition \<open>\<turnstile> Imp p p\<close>
proof -
  have 1: \<open>\<turnstile> Imp (Imp p (Imp (Imp p p) p)) (Imp (Imp p (Imp p p)) (Imp p p))\<close>
    using OK.intros
    unfolding axiom_distribimp'_def
    by simp

  have 2: \<open>\<turnstile> Imp p (Imp (Imp p p) p)\<close>
    using OK.intros
    unfolding axiom_addimp'_def
    by simp

  have 3: \<open>\<turnstile> Imp (Imp p (Imp p p)) (Imp p p)\<close>
    using 1 2 OK.intros(1)
    unfolding modusponens'_def
    by fastforce

  have 4: \<open>\<turnstile> Imp p (Imp p p)\<close>
    using OK.intros
    unfolding axiom_addimp'_def
    by simp

  have 5: \<open>\<turnstile> Imp p p\<close>
    using 3 4 OK.intros(1)
    unfolding modusponens'_def
    by fastforce

  show ?thesis
    using 5
    by simp
qed

section \<open>Soundness of Proof System\<close>

lemma map':
  \<open>\<not> occurs_in x t \<Longrightarrow> semantics_term e f t = semantics_term (e(x := v)) f t\<close>
  \<open>\<not> occurs_in_list x l \<Longrightarrow> semantics_list e f l = semantics_list (e(x := v)) f l\<close>
  by (induct t and l rule: semantics_term.induct semantics_list.induct) simp_all

lemma map:
  \<open>\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p\<close>
proof (induct p arbitrary: e)
  fix e
  show \<open>\<not> free_in x Truth \<Longrightarrow> semantics e f g Truth \<longleftrightarrow> semantics (e(x := v)) f g Truth\<close>
    by simp
next
  fix e
  show \<open>\<not> free_in x Falsity \<Longrightarrow> semantics e f g Falsity \<longleftrightarrow> semantics (e(x := v)) f g Falsity\<close>
    by simp
next
  fix e i l
  show \<open>\<not> free_in x (Pre i l) \<Longrightarrow> semantics e f g (Pre i l) \<longleftrightarrow> semantics (e(x := v)) f g (Pre i l)\<close>
  proof -
    assume assm: \<open>\<not> free_in x (Pre i l)\<close>
    then have fresh: \<open>\<not> occurs_in_list x l\<close>
      by simp
    show \<open>semantics e f g (Pre i l) \<longleftrightarrow> semantics (e(x := v)) f g (Pre i l)\<close>
    proof cases
      assume eq: \<open>i = STR ''='' \<and> length2 l\<close>
      then have \<open>semantics e f g (Pre i l) \<longleftrightarrow>
          semantics_term e f (hd l) = semantics_term e f (hd (tl l))\<close>
        by simp
      also have \<open>\<dots> \<longleftrightarrow>
          semantics_term (e(x := v)) f (hd l) = semantics_term (e(x := v)) f (hd (tl l))\<close>
        using map'(1) fresh occurs_in_list.simps(2) eq list.case_eq_if list.collapse
        unfolding length2_def
        by metis
      finally show ?thesis
        using eq
        by simp
    next
      assume not_eq: \<open>\<not> (i = STR ''='' \<and> length2 l)\<close>
      then have \<open>semantics e f g (Pre i l) \<longleftrightarrow> g i (semantics_list e f l)\<close>
        by simp iprover
      also have \<open>\<dots> \<longleftrightarrow> g i (semantics_list (e(x := v)) f l)\<close>
        using map'(2) fresh
        by metis
      finally show ?thesis
        using not_eq
        by simp iprover
    qed
  qed
next
  fix p1 p2 e
  assume assm1: \<open>\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1\<close> for e
  assume assm2: \<open>\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2\<close> for e
  show \<open>\<not> free_in x (Imp p1 p2) \<Longrightarrow>
      semantics e f g (Imp p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Imp p1 p2)\<close>
    using assm1 assm2
    by simp
next
  fix p1 p2 e
  assume assm1: \<open>\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1\<close> for e
  assume assm2: \<open>\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2\<close> for e
  show \<open>\<not> free_in x (Iff p1 p2) \<Longrightarrow>
      semantics e f g (Iff p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Iff p1 p2)\<close>
    using assm1 assm2
    by simp
next
  fix p1 p2 e
  assume assm1: \<open>\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1\<close> for e
  assume assm2: \<open>\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2\<close> for e
  show \<open>\<not> free_in x (Con p1 p2) \<Longrightarrow>
      semantics e f g (Con p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Con p1 p2)\<close>
    using assm1 assm2
    by simp
next
  fix p1 p2 e
  assume assm1: \<open>\<not> free_in x p1 \<Longrightarrow> semantics e f g p1 \<longleftrightarrow> semantics (e(x := v)) f g p1\<close> for e
  assume assm2: \<open>\<not> free_in x p2 \<Longrightarrow> semantics e f g p2 \<longleftrightarrow> semantics (e(x := v)) f g p2\<close> for e
  show \<open>\<not> free_in x (Dis p1 p2) \<Longrightarrow>
      semantics e f g (Dis p1 p2) \<longleftrightarrow> semantics (e(x := v)) f g (Dis p1 p2)\<close>
    using assm1 assm2
    by simp
next
  fix p e
  assume \<open>\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p\<close> for e
  then show \<open>\<not> free_in x (Neg p) \<Longrightarrow> semantics e f g (Neg p) \<longleftrightarrow> semantics (e(x := v)) f g (Neg p)\<close>
    by simp
next
  fix x1 p e
  assume \<open>\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p\<close> for e
  then show \<open>\<not> free_in x (Exi x1 p) \<Longrightarrow>
      semantics e f g (Exi x1 p) \<longleftrightarrow> semantics (e(x := v)) f g (Exi x1 p)\<close>
    by simp (metis fun_upd_twist fun_upd_upd)
next
  fix x1 p e
  assume \<open>\<not> free_in x p \<Longrightarrow> semantics e f g p \<longleftrightarrow> semantics (e(x := v)) f g p\<close> for e
  then show \<open>\<not> free_in x (Uni x1 p) \<Longrightarrow>
      semantics e f g (Uni x1 p) \<longleftrightarrow> semantics (e(x := v)) f g (Uni x1 p)\<close>
    by simp (metis fun_upd_twist fun_upd_upd)
qed

lemma length2_equiv:
  \<open>length2 l \<longleftrightarrow> [hd l, hd (tl l)] = l\<close>
proof -
  have \<open>length2 l \<Longrightarrow> [hd l, hd (tl l)] = l\<close>
    unfolding length2_def
    using list.case_eq_if list.exhaust_sel
    by metis
  then show ?thesis
    unfolding length2_def
    using list.case list.case_eq_if
    by metis
qed

lemma equal_length_sym:
  \<open>equal_length l l' \<Longrightarrow> equal_length l' l\<close>
proof (induct l' arbitrary: l)
  fix l
  assume \<open>equal_length l []\<close>
  then show \<open>equal_length [] l\<close>
    using equal_length.simps list.case_eq_if
    by metis
next
  fix l l' a
  assume sym: \<open>equal_length l l' \<Longrightarrow> equal_length l' l\<close> for l
  assume \<open>equal_length l (a # l')\<close>
  then show \<open>equal_length (a # l') l\<close>
    using equal_length.simps list.case_eq_if list.collapse list.inject sym
    by metis
qed

lemma equal_length2:
  \<open>equal_length l l' \<Longrightarrow> length2 l \<longleftrightarrow> length2 l'\<close>
proof -
  assume assm: \<open>equal_length l l'\<close>
  have \<open>equal_length l [t, t'] \<Longrightarrow> length2 l\<close> for t t'
    unfolding length2_def
    using equal_length.simps list.case_eq_if
    by metis
  moreover have \<open>equal_length [t, t'] l' \<Longrightarrow> length2 l'\<close> for t t'
    unfolding length2_def
    using equal_length.simps list.case_eq_if equal_length_sym
    by metis
  ultimately show ?thesis
    using assm length2_equiv
    by metis
qed

lemma imp_chain_equiv:
  \<open>semantics e f g (foldr Imp l p) \<longleftrightarrow> (\<forall>q \<in> set l. semantics e f g q) \<longrightarrow> semantics e f g p\<close>
  using imp_conjL
  by (induct l) simp_all

lemma imp_chain_zip_eq:
  \<open>equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') p) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l' \<longrightarrow> semantics e f g p\<close>
proof -
  assume \<open>equal_length l l'\<close>
  then have \<open>(\<forall>q \<in> set (zip_eq l l'). semantics e f g q) \<longleftrightarrow>
      semantics_list e f l = semantics_list e f l'\<close>
    unfolding zip_eq_def
    using length2_def
    by (induct l l' rule: list_induct2') simp_all
  then show ?thesis
    using imp_chain_equiv
    by iprover
qed

lemma funcong:
  \<open>equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Pre (STR ''='') [Fun i l, Fun i l']))\<close>
proof -
  assume assm: \<open>equal_length l l'\<close>
  show ?thesis
  proof cases
    assume \<open>semantics_list e f l = semantics_list e f l'\<close>
    then have \<open>semantics e f g (Pre (STR ''='') [Fun i l, Fun i l'])\<close>
      using length2_def
      by simp
    then show ?thesis
      using imp_chain_equiv
      by iprover
  next
    assume \<open>semantics_list e f l \<noteq> semantics_list e f l'\<close>
    then show ?thesis
      using assm imp_chain_zip_eq
      by iprover
  qed
qed

lemma predcong:
  \<open>equal_length l l' \<Longrightarrow>
      semantics e f g (foldr Imp (zip_eq l l') (Imp (Pre i l) (Pre i l')))\<close>
proof -
  assume assm: \<open>equal_length l l'\<close>
  show ?thesis
  proof cases
    assume eq: \<open>i = STR ''='' \<and> length2 l \<and> length2 l'\<close>
    show ?thesis
    proof cases
      assume \<open>semantics_list e f l = semantics_list e f l'\<close>
      then have \<open>semantics_list e f [hd l, hd (tl l)] = semantics_list e f [hd l', hd (tl l')]\<close>
        using eq length2_equiv
        by simp
      then have \<open>semantics e f g (Imp (Pre (STR ''='') l) (Pre (STR ''='') l'))\<close>
        using eq
        by simp
      then show ?thesis
        using eq imp_chain_equiv
        by iprover
    next
      assume \<open>semantics_list e f l \<noteq> semantics_list e f l'\<close>
      then show ?thesis
        using assm imp_chain_zip_eq
        by iprover
    qed
  next
    assume not_eq: \<open>\<not> (i = STR ''='' \<and> length2 l \<and> length2 l')\<close>
    show ?thesis
    proof cases
      assume \<open>semantics_list e f l = semantics_list e f l'\<close>
      then have \<open>semantics e f g (Imp (Pre i l) (Pre i l'))\<close>
        using assm not_eq equal_length2
        by simp iprover
      then show ?thesis
        using imp_chain_equiv
        by iprover
    next
      assume \<open>semantics_list e f l \<noteq> semantics_list e f l'\<close>
      then show ?thesis
        using assm imp_chain_zip_eq
        by iprover
    qed
  qed
qed

theorem soundness':
  \<open>\<turnstile> p \<Longrightarrow> semantics e f g p\<close>
proof (induct arbitrary: e rule: OK.induct)
  fix e s s'
  assume \<open>semantics e f g s\<close> \<open>semantics e f g s'\<close> for e
  then show \<open>semantics e f g (modusponens' s s')\<close>
    unfolding modusponens'_def
    by (cases s) simp_all
next
  fix e x s
  assume \<open>semantics e f g s\<close> for e
  then show \<open>semantics e f g (gen' x s)\<close>
    unfolding gen'_def
    by simp
next
  fix e p q
  show \<open>semantics e f g (axiom_addimp' p q)\<close>
    unfolding axiom_addimp'_def
    by simp
next
  fix e p q r
  show \<open>semantics e f g (axiom_distribimp' p q r)\<close>
    unfolding axiom_distribimp'_def
    by simp
next
  fix e g p
  show \<open>semantics e f g (axiom_doubleneg' p)\<close>
    unfolding axiom_doubleneg'_def
    by simp
next
  fix e x p q
  show \<open>semantics e f g (axiom_allimp' x p q)\<close>
    unfolding axiom_allimp'_def
    by simp
next
  fix e x p
  show \<open>semantics e f g (axiom_impall' x p)\<close>
    unfolding axiom_impall'_def
    using map
    by simp iprover
next
  fix e x t
  show \<open>semantics e f g (axiom_existseq' x t)\<close>
    unfolding axiom_existseq'_def
    using map'(1) length2_def
    by simp iprover
next
  fix e t
  show \<open>semantics e f g (axiom_eqrefl' t)\<close>
    unfolding axiom_eqrefl'_def
    using length2_def
    by simp
next
  fix e i l l'
  show \<open>semantics e f g (axiom_funcong' i l l')\<close>
    unfolding axiom_funcong'_def
    using funcong
    by simp standard
next
  fix e i l l'
  show \<open>semantics e f g (axiom_predcong' i l l')\<close>
    unfolding axiom_predcong'_def
    using predcong
    by simp standard
next
  fix e p q
  show \<open>semantics e f g (axiom_iffimp1' p q)\<close>
    unfolding axiom_iffimp1'_def
    by simp
next
  fix e p q
  show \<open>semantics e f g (axiom_iffimp2' p q)\<close>
    unfolding axiom_iffimp2'_def
    by simp
next
  fix e p q
  show \<open>semantics e f g (axiom_impiff' p q)\<close>
    unfolding axiom_impiff'_def
    by simp (rule impI, rule impI, rule iffI, erule mp, assumption, erule mp, assumption)
next
  fix e
  show \<open>semantics e f g (axiom_true')\<close>
    unfolding axiom_true'_def
    by simp
next
  fix e p
  show \<open>semantics e f g (axiom_not' p)\<close>
    unfolding axiom_not'_def
    by simp
next
  fix e p q
  show \<open>semantics e f g (axiom_and' p q)\<close>
    unfolding axiom_and'_def
    by simp
next
  fix e p q
  show \<open>semantics e f g (axiom_or' p q)\<close>
    unfolding axiom_or'_def
    by simp
next
  fix e x p
  show \<open>semantics e f g (axiom_exists' x p)\<close>
    unfolding axiom_exists'_def
    by simp
qed

corollary consistency': \<open>\<not> (\<turnstile> Falsity)\<close>
  using soundness'
  by fastforce

section \<open>Definition of Theorems as a Type\<close>

typedef "thm" = \<open>{p :: fm. \<turnstile> p}\<close>
proof -
  have \<open>\<turnstile> axiom_addimp' Truth Truth\<close>
    using OK.intros by auto
  then show ?thesis by blast
qed

definition \<open>concl \<equiv> Rep_thm\<close>
declare concl_def[simp]

setup_lifting type_definition_thm

section \<open>Soundness of Proof System as a Type\<close>

theorem soundness: \<open>semantics e f g (concl p)\<close>
  using soundness' Rep_thm
  by fastforce

theorem consistency: \<open>concl p \<noteq> Falsity\<close>
  using consistency' Rep_thm concl_def mem_Collect_eq
  by metis

section \<open>Definition of Rules and Axioms on Theorems\<close>

lift_definition modusponens :: \<open>thm \<Rightarrow> thm \<Rightarrow> thm\<close> is modusponens'
  using OK.intros(1) .

lift_definition gen :: \<open>id \<Rightarrow> thm \<Rightarrow> thm\<close> is gen'
  using OK.intros(2) .

lift_definition axiom_addimp :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_addimp'
  using OK.intros(3) .

lift_definition axiom_distribimp :: \<open>fm \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_distribimp'
  using OK.intros(4) .

lift_definition axiom_doubleneg :: \<open>fm \<Rightarrow> thm\<close> is axiom_doubleneg'
  using OK.intros(5) .

lift_definition axiom_allimp :: \<open>id \<Rightarrow> fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_allimp'
  using OK.intros(6) .

lift_definition axiom_impall :: \<open>id \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_impall'
  using OK.intros(7) .

lift_definition axiom_existseq :: \<open>id \<Rightarrow> tm \<Rightarrow> thm\<close> is axiom_existseq'
  using OK.intros(8) .

lift_definition axiom_eqrefl :: \<open>tm \<Rightarrow> thm\<close> is axiom_eqrefl'
  using OK.intros(9) .

lift_definition axiom_funcong :: \<open>id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> thm\<close> is axiom_funcong'
  using OK.intros(10) .

lift_definition axiom_predcong :: \<open>id \<Rightarrow> tm list \<Rightarrow> tm list \<Rightarrow> thm\<close> is axiom_predcong'
  using OK.intros(11) .

lift_definition axiom_iffimp1 :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_iffimp1'
  using OK.intros(12) .

lift_definition axiom_iffimp2 :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_iffimp2'
  using OK.intros(13) .

lift_definition axiom_impiff :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_impiff'
  using OK.intros(14) .

lift_definition axiom_true :: \<open>thm\<close> is axiom_true'
  using OK.intros(15) .

lift_definition axiom_not :: \<open>fm \<Rightarrow> thm\<close> is axiom_not'
  using OK.intros(16) .

lift_definition axiom_and :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_and'
  using OK.intros(17) .

lift_definition axiom_or :: \<open>fm \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_or'
  using OK.intros(18) .

lift_definition axiom_exists :: \<open>id \<Rightarrow> fm \<Rightarrow> thm\<close> is axiom_exists'
  using OK.intros(19) .

section \<open>ML Code Reflection\<close>

code_reflect
  Proven
  datatypes
    tm = Var | Fun
    and
    fm = Truth | Falsity | Pre | Imp | Iff | Con | Dis | Neg | Exi | Uni
  functions
    modusponens gen axiom_addimp axiom_distribimp axiom_doubleneg axiom_allimp axiom_impall
    axiom_existseq axiom_eqrefl axiom_funcong axiom_predcong axiom_iffimp1 axiom_iffimp2
    axiom_impiff axiom_true axiom_not axiom_and axiom_or axiom_exists concl

ML_file \<open>SPA.ML\<close>

ML_val \<open> auto "A ==> A" \<close>

ML_val \<open> auto "exists x. D(x) ==> forall x. D(x)" \<close>

ML_val \<open> auto "(forall x. ~R(x) ==> R(f(x))) ==> exists x. R(x) /\\ R(f(f(x)))" \<close>

end
