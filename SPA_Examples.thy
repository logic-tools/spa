\<comment> \<open>SPA: Students' Proof Assistant - Anders Schlichtkrull & Jørgen Villadsen, DTU Compute, Denmark\<close>

\<comment> \<open>Based on our Archive of Formal Proofs entry https://www.isa-afp.org/entries/FOL_Harrison.shtml\<close>

\<comment> \<open>Acknowledgement: Thanks to Alexander Birch Jensen for collaboration on the first formalization\<close>

theory SPA_Examples imports SPA
begin

section \<open>Pelletier's Problem 1\<close>

ML_val {*

auto "p ==> q <=> ~q ==> ~p"

*}

section \<open>Pelletier's Problem 2\<close>

ML_val {*

auto "~ ~p <=> p"

*}

section \<open>Pelletier's Problem 3\<close>

ML_val {*

auto "~(p ==> q) ==> q ==> p"

*}

section \<open>Pelletier's Problem 4\<close>

ML_val {*

auto "~p ==> q <=> ~q ==> p"

*}

section \<open>Pelletier's Problem 5\<close>

ML_val {*

auto "(p \\/ q ==> p \\/ r) ==> p \\/ (q ==> r)"

*}

section \<open>Pelletier's Problem 6\<close>

ML_val {*

auto "p \\/ ~p"

*}

section \<open>Pelletier's Problem 7\<close>

ML_val {*

auto "p \\/ ~ ~ ~p"

*}

section \<open>Pelletier's Problem 8\<close>

ML_val {*

auto "((p ==> q) ==> p) ==> p"

*}

section \<open>Pelletier's Problem 9\<close>

ML_val {*

auto "(p \\/ q) /\\ (~p \\/ q) /\\ (p \\/ ~q) ==> ~(~q \\/ ~q)"

*}

section \<open>Pelletier's Problem 10\<close>

ML_val {*

auto "(q ==> r) /\\ (r ==> p /\\ q) /\\ (p ==> q /\\ r) ==> (p <=> q)"

*}

section \<open>Pelletier's Problem 11\<close>

ML_val {*

auto "p <=> p"

*}

section \<open>Pelletier's Problem 12\<close>

ML_val {*

auto "((p <=> q) <=> r) <=> (p <=> (q <=> r))"

*}

section \<open>Pelletier's Problem 13\<close>

ML_val {*

auto "p \\/ q /\\ r <=> (p \\/ q) /\\ (p \\/ r)"

*}

section \<open>Pelletier's Problem 14\<close>

ML_val {*

auto "(p <=> q) <=> (q \\/ ~p) /\\ (~q \\/ p)"

*}

section \<open>Pelletier's Problem 15\<close>

ML_val {*

auto "p ==> q <=> ~p \\/ q"

*}

section \<open>Pelletier's Problem 16\<close>

ML_val {*

auto "(p ==> q) \\/ (q ==> p)"

*}

section \<open>Pelletier's Problem 17\<close>

ML_val {*

auto "p /\\ (q ==> r) ==> s <=> (~p \\/ q \\/ s) /\\ (~p \\/ ~r \\/ s)"

*}

section \<open>Pelletier's Problem 18\<close>

ML_val {*

auto "exists y. forall x. P(y) ==> P(x)"

*}

section \<open>Pelletier's Problem 19\<close>

ML_val {*

auto "exists x. forall y z. (P(y) ==> Q(z)) ==> P(x) ==> Q(x)"

*}

section \<open>Pelletier's Problem 20\<close>

ML_val {*

auto ("(forall x y. exists z. forall w. P(x) /\\ Q(y) ==> R(z) /\\ U(w)) " ^
      "==> (exists x y. P(x) /\\ Q(y)) ==> (exists z. R(z))")

*}

section \<open>Pelletier's Problem 21\<close>

ML_val {*

auto "(exists x. P ==> Q(x)) /\\ (exists x. Q(x) ==> P) ==> (exists x. P <=> Q(x))"

*}

section \<open>Pelletier's Problem 22\<close>

ML_val {*

auto "(forall x. P <=> Q(x)) ==> (P <=> (forall x. Q(x)))"

*}

section \<open>Pelletier's Problem 23\<close>

ML_val {*

auto "(forall x. P \\/ Q(x)) <=> P \\/ (forall x. Q(x))"

*}

section \<open>Pelletier's Problem 24\<close>

ML_val {*

auto ("~(exists x. U(x) /\\ Q(x)) /\\ " ^
      "(forall x. P(x) ==> Q(x) \\/ R(x)) /\\ " ^
      "~(exists x. P(x) ==> (exists x. Q(x))) /\\ " ^
      "(forall x. Q(x) /\\ R(x) ==> U(x)) " ^
      "==> (exists x. P(x) /\\ R(x))")

*}

section \<open>Pelletier's Problem 25\<close>

ML_val {*

auto ("(exists x. P(x)) /\\ " ^
      "(forall x. U(x) ==> ~G(x) /\\ R(x)) /\\ " ^
      "(forall x. P(x) ==> G(x) /\\ U(x)) /\\ " ^
      "((forall x. P(x) ==> Q(x)) \\/ (exists x. Q(x) /\\ P(x))) " ^
      "==> (exists x. Q(x) /\\ P(x))")

*}

section \<open>Pelletier's Problem 26\<close>

ML_val {*

auto ("((exists x. P(x)) <=> (exists x. Q(x))) /\\ " ^
      "(forall x y. P(x) /\\ Q(y) ==> (R(x) <=> U(y))) " ^
      "==> ((forall x. P(x) ==> R(x)) <=> (forall x. Q(x) ==> U(x)))")

*}

section \<open>Pelletier's Problem 27\<close>

ML_val {*

auto ("(exists x. P(x) /\\ ~Q(x)) /\\ " ^
      "(forall x. P(x) ==> R(x)) /\\ " ^
      "(forall x. U(x) /\\ V(x) ==> P(x)) /\\ " ^
      "(exists x. R(x) /\\ ~Q(x)) " ^
      "==> (forall x. V(x) ==> ~R(x)) ==> (forall x. U(x) ==> ~V(x))")

*}

section \<open>Pelletier's Problem 28\<close>

ML_val {*

auto ("(forall x. P(x) ==> (forall x. Q(x))) /\\ " ^
      "((forall x. Q(x) \\/ R(x)) ==> (exists x. Q(x) /\\ R(x))) /\\ " ^
      "((exists x. R(x)) ==> (forall x. L(x) ==> M(x))) " ^
      "==> (forall x. P(x) /\\ L(x) ==> M(x))")

*}

section \<open>Pelletier's Problem 29\<close>

ML_val {*

auto ("(exists x. P(x)) /\\ (exists x. G(x)) ==> " ^
      "((forall x. P(x) ==> H(x)) /\\ (forall x. G(x) ==> J(x)) " ^
      "<=> (forall x y. P(x) /\\ G(y) ==> H(x) /\\ J(y)))")

*}

section \<open>Pelletier's Problem 30\<close>

ML_val {*

auto ("(forall x. P(x) \\/ G(x) ==> ~H(x)) /\\ " ^
      "(forall x. (G(x) ==> ~U(x)) ==> P(x) /\\ H(x)) " ^
      "==> (forall x. U(x))")

*}

section \<open>Pelletier's Problem 31\<close>

ML_val {*

auto ("~(exists x. P(x) /\\ (G(x) \\/ H(x))) /\\ " ^
      "(exists x. Q(x) /\\ P(x)) /\\ " ^
      "(forall x. ~H(x) ==> J(x)) " ^
      "==> (exists x. Q(x) /\\ J(x))")

*}

section \<open>Pelletier's Problem 32\<close>

ML_val {*

auto ("(forall x. P(x) /\\ (G(x) \\/ H(x)) ==> Q(x)) /\\ " ^
      "(forall x. Q(x) /\\ H(x) ==> J(x)) /\\ " ^
      "(forall x. R(x) ==> H(x)) " ^
      "==> (forall x. P(x) /\\ R(x) ==> J(x))")

*}

section \<open>Pelletier's Problem 33\<close>

ML_val {*

auto ("(forall x. P(a) /\\ (P(x) ==> P(b)) ==> P(c)) " ^
      "<=> (forall x. P(a) ==> P(x) \\/ P(c)) /\\ (P(a) ==> P(b) ==> P(c))")

*}

section \<open>Pelletier's Problem 34\<close>

ML_val {*

prove
(<!("((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>"
^   "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))")!>)
[

  note ("directions",
  <!("(((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) ==>"
^    "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))) /\\"
^    "(((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))) ==>"
^    "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))))")!>)
  proof
  [
    conclude
    (<!("((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) ==>"
^       "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))")!>)
    proof
    [
      assume [("A",
      <!"(exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))"!>)],

      note ("ant",
      <!("((exists x. forall y. Q(x) <=> Q(y)) ==> ((exists x. P(x)) <=> (forall y. P(y)))) /\\"
^        "(((exists x. P(x)) <=> (forall y. P(y))) ==> ((exists x. forall y. Q(x) <=> Q(y))))")!>)
      proof
      [

        conclude
        (<!"(exists x. forall y. Q(x) <=> Q(y)) ==> ((exists x. P(x)) <=> (forall y. P(y)))"!>)
        proof
        [
          assume [("", <!"exists x. forall y. Q(x) <=> Q(y)"!>)],
          so have (<!"(exists x. Q(x)) <=> (forall y. Q(y))"!>) at once,
          so have (<!"exists x. forall y. P(x) <=> P(y)"!>) by ["A"],
          so our thesis at once,
          qed
        ],

        conclude
        (<!"((exists x. P(x)) <=> (forall y. P(y))) ==> (exists x. forall y. Q(x) <=> Q(y))"!>)
        proof
        [
          note ("imp",
          <!("((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) ==>"
^            "((exists x. forall y. P(x) <=> P(y)) ==> ((exists x. Q(x)) <=> (forall y. Q(y))))")!>)
          using [axiom_iffimp1
            (<!"exists x. forall y. P(x) <=> P(y)"!>)
            (<!"(exists x. Q(x)) <=> (forall y. Q(y))"!>)],
          note ("A1",
           <!"(exists x. forall y. P(x) <=> P(y)) ==> ((exists x. Q(x)) <=> (forall y. Q(y)))"!>)
          by_mp ("imp", "A"),

          assume [("", <!"((exists x. P(x)) <=> (forall y. P(y)))"!>)],
          so have (<!"(exists x. forall y. P(x) <=> P(y))"!>) at once,
          so have (<!"((exists x. Q(x)) <=> (forall y. Q(y)))"!>) by ["A1"],
          so our thesis at once,
          qed
        ],
        qed
      ],

      note ("imp",
      <!("((exists x. forall y. Q(x) <=> Q(y)) ==> ((exists x. P(x)) <=> (forall y. P(y)))) /\\"
^        "(((exists x. P(x)) <=> (forall y. P(y))) ==> ((exists x. forall y. Q(x) <=> Q(y)))) ==>"
^        "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))")!>)
      using [unshunt (axiom_impiff
        (<!"exists x. forall y. Q(x) <=> Q(y)"!>)
        (<!"(exists x. P(x)) <=> (forall y. P(y))"!>))],

      our thesis by_mp ("imp", "ant"),
      qed
    ],

    conclude
    (<!("((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))) ==>"
^       "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y))))")!>)
    proof
    [
      assume [("A",
       <!"(exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))"!>)],

      note ("ant",
      <!("((exists x. forall y. P(x) <=> P(y)) ==> ((exists x. Q(x)) <=> (forall y. Q(y)))) /\\"
^        "(((exists x. Q(x)) <=> (forall y. Q(y))) ==> (exists x. forall y. P(x) <=> P(y)))")!>)
      proof
      [

        conclude
        (<!"(exists x. forall y. P(x) <=> P(y)) ==> ((exists x. Q(x)) <=> (forall y. Q(y)))"!>)
        proof
        [
          assume [("", <!"exists x. forall y. P(x) <=> P(y)"!>)],
          so have (<!"(exists x. P(x)) <=> (forall y. P(y))"!>) at once,
          so have (<!"exists x. forall y. Q(x) <=> Q(y)"!>) by ["A"],
          so our thesis at once,
          qed
        ],

        conclude
        (<!"((exists x. Q(x)) <=> (forall y. Q(y))) ==> (exists x. forall y. P(x) <=> P(y))"!>)
        proof
        [
          note ("imp",
          <!("((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))) ==>"
^            "((exists x. forall y. Q(x) <=> Q(y)) ==> ((exists x. P(x)) <=> (forall y. P(y))))")!>)
          using [axiom_iffimp1
            (<!"exists x. forall y. Q(x) <=> Q(y)"!>)
            (<!"(exists x. P(x)) <=> (forall y. P(y))"!>)],
          note ("A1",
          <!"(exists x. forall y. Q(x) <=> Q(y)) ==> ((exists x. P(x)) <=> (forall y. P(y)))"!>)
          by_mp ("imp", "A"),

          assume [("", <!"(exists x. Q(x)) <=> (forall y. Q(y))"!>)],
          so have (<!"(exists x. forall y. Q(x) <=> Q(y))"!>) at once,
          so have (<!"((exists x. P(x)) <=> (forall y. P(y)))"!>) by ["A1"],
          so our thesis at once,
          qed
        ],
        qed
      ],

      note ("imp",
      <!("((exists x. forall y. P(x) <=> P(y)) ==> ((exists x. Q(x)) <=> (forall y. Q(y)))) /\\"
^        "(((exists x. Q(x)) <=> (forall y. Q(y))) ==> (exists x. forall y. P(x) <=> P(y))) ==>"
^        "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y))))")!>)
      using [unshunt (axiom_impiff
        (<!"exists x. forall y. P(x) <=> P(y)"!>)
        (<!"(exists x. Q(x)) <=> (forall y. Q(y))"!>))],

      our thesis by_mp ("imp", "ant"),
      qed
    ],
    qed
  ],

  note ("impiff",
  <!(("(((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) ==>"
^     "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y))))) /\\"
^     "(((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))) ==>"
^     "((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y))))) ==>"
^     "(((exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))) <=>"
^     "((exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))))"))!>)
  using [unshunt (axiom_impiff
    (<!("(exists x. forall y. P(x) <=> P(y)) <=> ((exists x. Q(x)) <=> (forall y. Q(y)))")!>)
    (<!("(exists x. forall y. Q(x) <=> Q(y)) <=> ((exists x. P(x)) <=> (forall y. P(y)))")!>))],

  our thesis by_mp ("impiff", "directions"),
  qed
]

*}

section \<open>Pelletier's Problem 35\<close>

ML_val {*

auto "exists x y. P(x,y) ==> (forall x y. P(x,y))"

*}

section \<open>Pelletier's Problem 36\<close>

ML_val {*

auto ("(forall x. exists y. P(x,y)) /\\ " ^
      "(forall x. exists y. G(x,y)) /\\ " ^
      "(forall x y. P(x,y) \\/ G(x,y) ==> (forall z. P(y,z) \\/ G(y,z) ==> H(x,z))) " ^
      "==> (forall x. exists y. H(x,y))")

*}

section \<open>Pelletier's Problem 37\<close>

ML_val {*

auto ("(forall z. " ^
        "exists w. forall x. exists y. (P(x,z) ==> P(y,w)) /\\ P(y,z) /\\ " ^
        "(P(y,w) ==> (exists u. Q(u,w)))) /\\ " ^
      "(forall x z. ~P(x,z) ==> (exists y. Q(y,z))) /\\ " ^
      "((exists x y. Q(x,y)) ==> (forall x. R(x,x))) " ^
      "==> (forall x. exists y. R(x,y))")

*}

section \<open>Pelletier's Problem 38\<close>

ML_val {*

auto ("(forall x. " ^
        "P(a) /\\ (P(x) ==> (exists y. P(y) /\\ R(x,y))) ==> " ^
        "(exists z w. P(z) /\\ R(x,w) /\\ R(w,z))) <=> " ^
      "(forall x. " ^
        "(~P(a) \\/ P(x) \\/ (exists z w. P(z) /\\ R(x,w) /\\ R(w,z))) /\\ " ^
        "(~P(a) \\/ ~(exists y. P(y) /\\ R(x,y)) \\/ " ^
        "(exists z w. P(z) /\\ R(x,w) /\\ R(w,z))))")

*}

section \<open>Pelletier's Problem 39\<close>

ML_val {*

auto "~(exists x. forall y. P(y,x) <=> ~P(y,y))"

*}

section \<open>Pelletier's Problem 40\<close>

ML_val {*

auto ("(exists y. forall x. P(x,y) <=> P(x,x)) " ^
      "==> ~(forall x. exists y. forall z. P(z,y) <=> ~P(z,x))")

*}

section \<open>Pelletier's Problem 41\<close>

ML_val {*

auto ("(forall z. exists y. forall x. P(x,y) <=> P(x,z) /\\ ~P(x,x)) " ^
      "==> ~(exists z. forall x. P(x,z))")

*}

section \<open>Pelletier's Problem 42\<close>

ML_val {*

auto "~(exists y. forall x. P(x,y) <=> ~(exists z. P(x,z) /\\ P(z,x)))"

*}

section \<open>Pelletier's Problem 43\<close>

ML_val {*

prove
  (<!"(forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)) ==> forall x y. Q(x,y) <=> Q(y,x)"!>)
  [
    assume [("A", <!"forall x y. Q(x,y) <=> forall z. P(z,x) <=> P(z,y)"!>)],
    conclude (<!"forall x y. Q(x,y) <=> Q(y,x)"!>) proof
    [
      fix "x", fix "y",
      conclude (<!"Q(x,y) <=> Q(y,x)"!>) proof
      [
        have (<!"(Q(x,y) ==> Q(y,x)) /\\ (Q(y,x) ==> Q(x,y))"!>) proof
        [
          conclude (<!"Q(x,y) ==> Q(y,x)"!>) proof
          [
            assume [("", <!"Q(x,y)"!>)],
            so have (<!"forall z. P(z,x) <=> P(z,y)"!>) by ["A"],
            so have (<!"forall z. P(z,y) <=> P(z,x)"!>) at once,
            so conclude (<!"Q(y,x)"!>) by ["A"],
            qed
          ],
          conclude (<!"Q(y,x) ==> Q(x,y)"!>) proof
          [
            assume [("", <!"Q(y,x)"!>)],
            so have (<!"forall z. P(z,y) <=> P(z,x)"!>) by ["A"],
            so have (<!"forall z. P(z,x) <=> P(z,y)"!>) at once,
            so conclude (<!"Q(x,y)"!>) by ["A"],
            qed
          ],
          qed
        ],
        so our thesis at once,
        qed
      ],
      qed
    ],
    qed
  ]

*}

section \<open>Pelletier's Problem 44\<close>

ML_val {*

auto ("(forall x. P(x) ==> (exists y. G(y) /\\ H(x,y)) /\\ " ^
      "(exists y. G(y) /\\ ~H(x,y))) /\\ " ^
      "(exists x. J(x) /\\ (forall y. G(y) ==> H(x,y))) ==> " ^
      "(exists x. J(x) /\\ ~P(x))")

*}

section \<open>Pelletier's Problem 45\<close>

ML_val {*

auto ("(forall x. " ^
        "P(x) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y)) ==> " ^
             "(forall y. G(y) /\\ H(x,y) ==> R(y))) /\\ " ^
      "~(exists y. L(y) /\\ R(y)) /\\ " ^
      "(exists x. P(x) /\\ (forall y. H(x,y) ==> " ^
        "L(y)) /\\ (forall y. G(y) /\\ H(x,y) ==> J(x,y))) ==> " ^
      "(exists x. P(x) /\\ ~(exists y. G(y) /\\ H(x,y)))")

*}

section \<open>Pelletier's Problem 46\<close>

ML_val {*

  prove
    (<!("(forall x. P(x) /\\ (forall y. P(y) /\\ H(y,x) ==> G(y)) ==> G(x)) /\\ " ^
          "((exists x. P(x) /\\ ~G(x)) ==> " ^
            "(exists x. P(x) /\\ ~G(x) /\\ (forall y. P(y) /\\ ~G(y) ==> J(x,y)))) /\\ " ^
          "(forall x y. P(x) /\\ P(y) /\\ H(x,y) ==> ~J(y,x)) ==> " ^
          "(forall x. P(x) ==> G(x))")!>)
    [
      assume [("A", <!("(forall x. P(x) /\\ (forall y. P(y) /\\ H(y,x) ==> G(y)) ==> G(x)) /\\ " ^
          "((exists x. P(x) /\\ ~G(x)) ==> " ^
            "(exists x. P(x) /\\ ~G(x) /\\ (forall y. P(y) /\\ ~G(y) ==> J(x,y)))) /\\ " ^
          "(forall x y. P(x) /\\ P(y) /\\ H(x,y) ==> ~J(y,x))")!>)],
      conclude (<!"(forall x. P(x) ==> G(x))"!>) proof
      [
        fix "x",
        conclude (<!"P(x) ==> G(x)"!>) proof
        [
          assume [("B", <!"P(x)"!>)],
          conclude (<!"G(x)"!>) by ["B","A"], qed
        ], qed
      ], qed
    ]

*}

section \<open>Pelletier's Problem 55\<close>

ML_val {*

auto ("lives(agatha) /\\ lives(butler) /\\ lives(charles) /\\ " ^
      "(killed(agatha,agatha) \\/ killed(butler,agatha) \\/ " ^
       "killed(charles,agatha)) /\\ " ^
      "(forall x y. killed(x,y) ==> hates(x,y) /\\ ~richer(x,y)) /\\ " ^
      "(forall x. hates(agatha,x) ==> ~hates(charles,x)) /\\ " ^
      "(hates(agatha,agatha) /\\ hates(agatha,charles)) /\\ " ^
      "(forall x. lives(x) /\\ ~richer(x,agatha) ==> hates(butler,x)) /\\ " ^
      "(forall x. hates(agatha,x) ==> hates(butler,x)) /\\ " ^
      "(forall x. ~hates(x,agatha) \\/ ~hates(x,butler) \\/ ~hates(x,charles)) " ^
      "==> killed(agatha,agatha) /\\ " ^
             "~killed(butler,agatha) /\\ " ^
             "~killed(charles,agatha)")

*}

section \<open>Pelletier's Problem 57\<close>

ML_val {*

auto ("P(f(a,b),f(b,c)) /\\ " ^
      "P(f(b,c),f(a,c)) /\\ " ^
      "(forall x y z. P(x,y) /\\ P(y,z) ==> P(x,z)) " ^
      "==> P(f(a,b),f(a,c))")

*}

section \<open>Pelletier's Problem 59\<close>

ML_val {*

auto "(forall x. P(x) <=> ~P(f(x))) ==> (exists x. P(x) /\\ ~P(f(x)))"

*}

section \<open>Pelletier's Problem 60\<close>

ML_val {*

auto "forall x. P(x,f(x)) <=> exists y. (forall z. P(z,y) ==> P(z,f(x))) /\\ P(x,y)"

*}

section \<open>Appendix\<close>

ML_val {* \<comment> \<open>Test gilmore_3\<close>

auto ("exists x. forall y z. " ^
              "((F(y,z) ==> (G(y) ==> H(x))) ==> F(x,x)) /\\ " ^
              "((F(z,x) ==> G(x)) ==> H(z)) /\\ " ^
              "F(x,y) " ^
              "==> F(z,z)")

*}

ML_val {* \<comment> \<open>Test gilmore_4\<close>

auto ("exists x y. forall z. " ^
              "(F(x,y) ==> F(y,z) /\\ F(z,z)) /\\ " ^
              "(F(x,y) /\\ G(x,y) ==> G(x,z) /\\ G(z,z))")

*}

ML_val {* \<comment> \<open>Test gilmore_5\<close>

auto ("(forall x. exists y. F(x,y) \\/ F(y,x)) /\\ " ^
      "(forall x y. F(y,x) ==> F(y,y)) " ^
      "==> exists z. F(z,z)")

*}

ML_val {* \<comment> \<open>Test gilmore_6\<close>

auto ("forall x. exists y. " ^
              "(exists u. forall v. F(u,x) ==> G(v,u) /\\ G(u,x)) " ^
              "==> (exists u. forall v. F(u,y) ==> G(v,u) /\\ G(u,y)) \\/ " ^
                        "(forall u v. exists w. G(v,u) \\/ H(w,y,u) ==> G(u,w))")

*}

ML_val {* \<comment> \<open>Test gilmore_7\<close>

auto ("(forall x. K(x) ==> exists y. L(y) /\\ (F(x,y) ==> G(x,y))) /\\ " ^
      "(exists z. K(z) /\\ forall u. L(u) ==> F(z,u)) " ^
      "==> exists v w. K(v) /\\ L(w) /\\ G(v,w)")

*}

ML_val {* \<comment> \<open>Test gilmore_8\<close>

auto ("exists x. forall y z. " ^
              "((F(y,z) ==> (G(y) ==> (forall u. exists v. H(u,v,x)))) ==> F(x,x)) /\\ " ^
              "((F(z,x) ==> G(x)) ==> (forall u. exists v. H(u,v,z))) /\\ " ^
              "F(x,y) " ^
              "==> F(z,z)")

*}

ML_val {* \<comment> \<open>Test gilmore_9\<close>

auto ("forall x. exists y. forall z. " ^
              "((forall u. exists v. F(y,u,v) /\\ G(y,u) /\\ ~H(y,x)) " ^
                   "==> (forall u. exists v. F(x,u,v) /\\ G(z,u) /\\ ~H(x,z)) " ^
                   "==> (forall u. exists v. F(x,u,v) /\\ G(y,u) /\\ ~H(x,y))) /\\ " ^
              "((forall u. exists v. F(x,u,v) /\\ G(y,u) /\\ ~H(x,y)) " ^
                  "==> ~(forall u. exists v. F(x,u,v) /\\ G(z,u) /\\ ~H(x,z)) " ^
                  "==> (forall u. exists v. F(y,u,v) /\\ G(y,u) /\\ ~H(y,x)) /\\ " ^
                         "(forall u. exists v. F(z,u,v) /\\ G(y,u) /\\ ~H(z,y)))")

*}

ML_val {* \<comment> \<open>Test davis_putnam_example\<close>

auto ("exists x. exists y. forall z. " ^
      "(F(x,y) ==> (F(y,z) /\\ F(z,z))) /\\ " ^
      "((F(x,y) /\\ G(x,y)) ==> (G(x,z) /\\ G(z,z)))")

*}

ML_val {* \<comment> \<open>Hoare's Exercise ewd1062_1 & ewd1062_2\<close>

prove
  (<!("(forall x. x <= x) /\\ " ^
      "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
      "(forall x y. f(x) <= y <=> x <= g(y)) " ^
      "==> (forall x y. x <= y ==> f(x) <= f(y)) /\\ " ^
          "(forall x y. x <= y ==> g(x) <= g(y))")!>)
  [
    assume [("A", <!("(forall x. x <= x) /\\ " ^
             "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
             "(forall x y. f(x) <= y <=> x <= g(y))")!>)],
    conclude (<!("(forall x y. x <= y ==> f(x) <= f(y)) /\\ " ^
                 "(forall x y. x <= y ==> g(x) <= g(y))")!>) proof
    [
      conclude (<!"(forall x y. x <= y ==> f(x) <= f(y))"!>) by ["A"],
      conclude (<!"(forall x y. x <= y ==> g(x) <= g(y))"!>) by ["A"],
      qed
    ],
    qed
  ]

*}

ML_val {* \<comment> \<open>Hoare's Exercise ewd1062_1\<close>

auto ("(forall x. x <= x) /\\ " ^
      "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
      "(forall x y. f(x) <= y <=> x <= g(y)) " ^
      "==> (forall x y. x <= y ==> f(x) <= f(y))")

*}

ML_val {* \<comment> \<open>Hoare's Exercise ewd1062_2\<close>

auto ("(forall x. x <= x) /\\ " ^
      "(forall x y z. x <= y /\\ y <= z ==> x <= z) /\\ " ^
      "(forall x y. f(x) <= y <=> x <= g(y)) " ^
      "==> (forall x y. x <= y ==> g(x) <= g(y))")

*}

ML_val {* \<comment> \<open>A simple example\<close>

val ewd954 = prove
 (<!("(forall x y. x <= y <=> x * y = x) /\\ " ^
   "(forall x y. f(x * y) = f(x) * f(y)) " ^
   "==> forall x y. x <= y ==> f(x) <= f(y)")!>)
 [note("eq_sym",<!"forall x y. x = y ==> y = x"!>)
    using [eq_sym (<!|"x"|!>) (<!|"y"|!>)],
  note("eq_trans",<!"forall x y z. x = y /\\ y = z ==> x = z"!>)
    using [eq_trans (<!|"x"|!>) (<!|"y"|!>) (<!|"z"|!>)],
  note("eq_cong",<!"forall x y. x = y ==> f(x) = f(y)"!>)
    using [axiom_funcong "f" [(<!|"x"|!>)] [(<!|"y"|!>)]],
  assume [("le",<!"forall x y. x <= y <=> x * y = x"!>),
          ("hom",<!"forall x y. f(x * y) = f(x) * f(y)"!>)],
  fix "x", fix "y",
  assume [("xy",<!"x <= y"!>)],
  so have (<!"x * y = x"!>) by ["le"],
  so have (<!"f(x * y) = f(x)"!>) by ["eq_cong"],
  so have (<!"f(x) = f(x * y)"!>) by ["eq_sym"],
  so have (<!"f(x) = f(x) * f(y)"!>) by ["eq_trans", "hom"],
  so have (<!"f(x) * f(y) = f(x)"!>) by ["eq_sym"],
  so conclude (<!"f(x) <= f(y)"!>) by ["le"],
  qed];

*}

ML_val {* \<comment> \<open>Example not in the main text\<close>

prove
 (<!("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")!>)
  [assume [("A",<!"exists x. p(x)"!>)],
   assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
   note ("C",<!"forall x. p(x) ==> p(f(f(f(f(x)))))"!>)
   proof
    [have (<!"forall x. p(x) ==> p(f(f(x)))"!>) by ["B"],
     so conclude (<!"forall x. p(x) ==> p(f(f(f(f(x)))))"!>) at once,
     qed],
   consider ("a",<!"p(a)"!>) by ["A"],
   take (<!|"a"|!>),
   so conclude (<!"p(f(f(f(f(a)))))"!>) by ["C"],
   qed];

*}

ML_val {* \<comment> \<open>Alternative formulation with lemma construct\<close>

prove
 (<!("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")!>)
  [assume [("A",<!"exists x. p(x)"!>)],
   assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
   lemma ("C",<!"forall x. p(x) ==> p(f(f(f(f(x)))))"!>),
     have (<!"forall x. p(x) ==> p(f(f(x)))"!>) by ["B"],
     so conclude (<!"forall x. p(x) ==> p(f(f(f(f(x)))))"!>) at once,
     qed,
   consider ("a",<!"p(a)"!>) by ["A"],
   take (<!|"a"|!>),
   so conclude (<!"p(f(f(f(f(a)))))"!>) by ["C"],
   qed]

*}

ML_val {* \<comment> \<open>Yet another formulation\<close>

prove
 (<!("(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))")!>)
  [assume [("A",<!"exists x. p(x)"!>)],
   assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
   note ("C",<!"forall x. p(x) ==> p(f(f(f(f(x)))))"!>) proof
    [have (<!"forall x. p(x) ==> p(f(f(x)))"!>) by ["B"],
     so our thesis at once,
     qed],
   consider ("a",<!"p(a)"!>) by ["A"],
   take (<!|"a"|!>),
   so our thesis by ["C"],
   qed];

*}

ML_val {* \<comment> \<open>And finally automatic\<close>

auto "(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(f(f(f(y)))))"

*}

ML_val {* \<comment> \<open>Harrison\<close>

auto "forall x. exists v w. forall y z. P(x) /\\ Q(y) ==> (P(v) \\/ R(w)) /\\ (R(z) ==> Q(v))"

*}

ML_val {*

prove (<!("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\\ p(f(y))")!>)
      [fix "c",
       assume [("A",<!"p(c)"!>)],
       assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
       take (<!|"c"|!>),
       conclude (<!"p(c)"!>) by ["A"],
       note ("C",<!"p(c) ==> p(f(c))"!>) by ["B"],
       so our thesis by ["C", "A"],
       qed];

*}

ML_val {*

prove (<!("p(c) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\\ p(f(y))")!>)
      [assume [("A",<!"p(c)"!>)],
       assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
       take (<!|"c"|!>),
       conclude (<!"p(c)"!>) by ["A"],
       our thesis by ["A", "B"],
       qed];

*}

ML_val {*

prove (<!("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\\ p(f(y))")!>)
      [fix "c",
       assume [("A",<!"p(c)"!>)],
       assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
       take (<!|"c"|!>),
       conclude (<!"p(c)"!>) by ["A"],
       note ("C",<!"p(c) ==> p(f(c))"!>) by ["B"],
       our thesis by ["C", "A"],
       qed];

*}

ML_val {*

prove (<!("forall a. p(a) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(y) /\\ p(f(y))")!>)
      [fix "c",
       assume [("A",<!"p(c)"!>)],
       assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
       take (<!|"c"|!>),
       note ("D",<!"p(c)"!>) by ["A"],
       note ("C",<!"p(c) ==> p(f(c))"!>) by ["B"],
       our thesis by ["C", "A", "D"],
       qed];

*}

ML_val {*

prove (<!"(p(a) \\/ p(b)) ==> q ==> exists y. p(y)"!>)
  [assume [("A",<!"p(a) \\/ p(b)"!>)],
   assume [("",<!"q"!>)],
   cases (<!"p(a) \\/ p(b)"!>) by ["A"],
     take (<!|"a"|!>),
     so our thesis at once,
     qed,
     take (<!|"b"|!>),
     so our thesis at once,
     qed];

*}

ML_val {*

prove (<!"(p(a) \\/ p(b)) /\\ (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))"!>)
  [assume [("base",<!"p(a) \\/ p(b)"!>),
           ("Step",<!"forall x. p(x) ==> p(f(x))"!>)],
   cases (<!"p(a) \\/ p(b)"!>) by ["base"],
     so note("A",<!"p(a)"!>) at once,
     note ("X",<!"p(a) ==> p(f(a))"!>) by ["Step"],
     take (<!|"a"|!>),
     our thesis by ["A", "X"],
     qed,
     take (<!|"b"|!>),
     so our thesis by ["Step"],
     qed];

*}

ML_val {*

prove (<!"(exists x. p(x)) ==> (forall x. p(x) ==> p(f(x))) ==> exists y. p(f(y))"!>)
  [assume [("A",<!"exists x. p(x)"!>)],
   assume [("B",<!"forall x. p(x) ==> p(f(x))"!>)],
   consider ("a",<!"p(a)"!>) by ["A"],
   so note ("concl",<!"p(f(a))"!>) by ["B"],
   take (<!|"a"|!>),
   our thesis by ["concl"],
   qed];

*}

ML_val {*

prove (<!("(forall x. p(x) ==> q(x)) ==> (forall x. q(x) ==> p(x)) ==> (p(a) <=> q(a))")!>)
  [assume [("A",<!"forall x. p(x) ==> q(x)"!>)],
   assume [("B",<!"forall x. q(x) ==> p(x)"!>)],
   note ("von",<!"p(a) ==> q(a)"!>) by ["A"],
   note ("bis",<!"q(a) ==> p(a)"!>) by ["B"],
   our thesis by ["von", "bis"],
   qed];

*}

ML_val {*

auto "forall x. exists y. (P(x) \\/ P(y)) ==> exists x. P(x)"

*}

end
