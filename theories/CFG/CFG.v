Require Import List.
Require Import Nat.
Import ListNotations.

Require Import Setoid Morphisms List Arith Lia.

Definition stack (X : Type) := list (list X * list X).

(* ** Post Grammars *)

Notation sig := nat.
(* a rule maps a non-terminal symbol to a word *)
Definition rule : Type := sig * list sig.
(* a context-free grammar consist of a start symbol and a list of rules *)
Definition cfg : Type := sig * list rule.
Definition rules (G : cfg) := snd G.
Definition startsym (G : cfg) := fst G.

(* single step context-free derivation *)
Inductive rew_cfg : cfg -> list sig -> list sig -> Prop :=
  | rewR R x a y v : In (a, v) (rules R) -> rew_cfg R (x++[a]++y) (x++v++y).

(* reflexive, transitive closure of single step context-free derivation *)
Inductive rewt (S: cfg) (x: list sig) : list sig -> Prop :=
  | rewtRefl : rewt S x x
  | rewtRule y z : rewt S x y -> rew_cfg S y z -> rewt S x z.

(* a word is terminal if it contains no non-terminals *)
Definition terminal G x := ~ exists y, rew_cfg G x y.

Inductive rew_cfg_left : cfg -> list sig -> list sig -> Prop :=
  | rewR_left R x a y v : (In (a, v) (rules R) /\ terminal R x) -> rew_cfg_left R (x ++ [a] ++ y) (x ++ v ++ y).


Inductive rewt_left (S: cfg) (x: list sig) : list sig -> Prop :=
  | rewtRefl_left : rewt_left S x x
  | rewtRule_left y z : rewt_left S x y -> 
                        rew_cfg_left S y z ->
                        rewt_left S x z.

Inductive rewt_left' (S: cfg) (x: list sig) : list sig -> Prop :=
  | rewtRefl_left' : rewt_left' S x x
  | rewtRule_left' y z : rew_cfg_left S x y ->
                        rewt_left' S y z -> 
                        rewt_left' S x z.

Lemma cant_be (x y : list sig) (a : sig) :
  x ++ a :: y = [] -> False.
Proof.
  intros.
  induction x; induction y; now simpl_list.
Qed.

Lemma empty_is_terminal (G: cfg) : terminal G [].
Proof.
  unfold terminal. unfold not. intros. destruct H as [x']. inversion H. apply (cant_be x y a H0).
Qed.

Global Instance rewt_leftTrans R :
  PreOrder (rewt_left R).
Proof.
  split.
  - hnf. econstructor.
  - induction 2; eauto. exact (rewtRule_left R x y0 z IHrewt_left H1).
Qed.

Global Instance rewt_leftTrans' R :
  PreOrder (rewt_left' R).
Proof.
  split.
  - hnf. econstructor.
  - induction 1.
    +  eauto. 
    + intros. remember (IHrewt_left' H1) as H2.
    exact (rewtRule_left' R x y z H H2).
Qed.

Lemma left'_iff_left (S : cfg) (x : list sig) (y : list sig) : rewt_left' S x y <-> rewt_left S x y.
Proof.
  split.
  + intros. induction H as [| x' y' z'].
    - constructor.
    - remember (rewtRule_left S x' x' y' (rewtRefl_left S x') H) as H2.
    apply ((PreOrder_Transitive _ y')); trivial.
  + intros. induction H as [| x' y' z'].
    - constructor.
    - remember (rewtRule_left' S x' y' y' H(rewtRefl_left' S y')) as H2.
    apply ((PreOrder_Transitive _ x')); trivial.
Qed.

(* the language of a grammar consists of all derivable terminal words *)
Definition L (G : cfg) x := rewt G [startsym G] x /\ terminal G x.

Lemma left_rew_to_rew_cfg (G: cfg) (x: list sig) : forall y,
  rew_cfg_left G x y -> rew_cfg G x y.
Proof.
  intros. repeat (destruct H). apply (rewR _ _ _ _ _). exact H.
Qed.

Lemma left_rewt_to_rewt (G: cfg) (x: list sig) (y : list sig) : rewt_left G x y -> rewt G x y.
Proof.
  intros. induction H.
  + constructor.
  + apply (rewtRule G x y z IHrewt_left (left_rew_to_rew_cfg G y z H0)).
Qed.

(* The Context-free Ambiguity Problem is
  given a context-free grammar to determine whether
  there exists a word that can have more than one 
  leftmost derivation.
*)
Definition CFA : cfg -> Prop :=
  fun G => exists (x: list sig) (ld1 ld2: rewt_left G [(startsym G)] x),
      L G x
      /\ ld1 <> ld2.  

(* The Context-free Palindrome Problem is
  given a context-free grammar to determine whether
  its language contains a palindrome. *)
Definition CFP : cfg -> Prop :=
  fun G => exists x, L G x /\ x = List.rev x.

(* The Context-free Intersection Problem is
  given two context-free grammars to determine whether 
  their intersection is not empty. *)
Definition CFI : cfg * cfg -> Prop :=
  fun '(G1, G2) => exists x, L G1 x /\ L G2 x.
