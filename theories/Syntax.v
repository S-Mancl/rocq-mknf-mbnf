From Stdlib Require Import Bool List String Arith.PeanoNat Vectors.Fin.
From MKNF Require Import Finite.
Import ListNotations.

Set Implicit Arguments.

(** * Chapter 1: Syntax

    The first step when formalising a logic is specifying its syntax. We will do it first for MKNF and, later on, for MBNF too.

    In the propositional language, we will use indexed propositions, in order to prevent malformed formulas: if we have [n] atoms, it shouldn't be possible to refer to any proposition whose index is [>= n].

    Throughout the following, feel free to ignore [n], as it only serves that purpose. Each atom, due to this construction, will have type [Fin.t n].

    Now, onwards to propositional MKNF grammar. 
    The following EBNF is the surface notation represented by [formula].
    Constructors appear at the right in order to simplify the translation between EBNF and Rocq syntax.

<<
    atom       ::= p_0 | ... | p_(n-1)                       FAtom
    formula    ::= atom                                      FAtom
                 | bottom                                    FBot
                 | "(" formula "and" formula ")"              FAnd
                 | "(" formula "or" formula ")"               FOr
                 | "(" formula "->" formula ")"               FImp
                 | "classical-not" formula                   FNeg
                 | "K" formula                               FK
                 | "not" formula                             FNot
    theory     ::= "[" formula { "," formula } "]"             list formula
>>

    Parentheses are used to specify precedences.
    It hasn't probably gone unnoticed to the keen reader how there are two negation operators.
    The FNeg one is the classical negation, while the FNot is negation-as-a-failure, a concept which will be detailed more extensively later on.
*)

(** The following is the syntax tree for MKNF formulas. *)
Inductive formula (n : nat) : Type :=
| FAtom : Fin.t n -> formula n
| FBot : formula n
| FAnd : formula n -> formula n -> formula n
| FOr : formula n -> formula n -> formula n
| FImp : formula n -> formula n -> formula n
| FNeg : formula n -> formula n
| FK : formula n -> formula n
| FNot : formula n -> formula n.

Arguments FAtom {n} _.
Arguments FBot {n}.
Arguments FAnd {n} _ _.
Arguments FOr {n} _ _.
Arguments FImp {n} _ _.
Arguments FNeg {n} _.
Arguments FK {n} _.
Arguments FNot {n} _.

(** A theory is a list of formulas to be satisfied together. *)
Definition theory n := list (formula n).

(** **
    For readability reasons, we define a high-level notation, more similar to the one used in the papers.
<<
    atom(p)   atom p
    bot       falsity
    ~ F       classical negation
    F and G   conjunction
    F or G    disjunction
    F implies G
    K F       knowledge
    not F     negation as failure
>>
*)
Declare Scope mknf_scope.
Delimit Scope mknf_scope with mknf.

Notation "'atom' '(' a ')'" := (FAtom a)
  (at level 0, a at level 99, format "'atom' '(' a ')'") : mknf_scope.
Notation "'bot'" := FBot : mknf_scope.
Notation "~ p" := (FNeg p)
  (at level 75, right associativity) : mknf_scope.
Notation "'K' p" := (FK p)
  (at level 75, right associativity) : mknf_scope.
Notation "'not' p" := (FNot p)
  (at level 75, right associativity) : mknf_scope.
Notation "p 'and' q" := (FAnd p q)
  (at level 80, right associativity) : mknf_scope.
Notation "p 'or' q" := (FOr p q)
  (at level 85, right associativity) : mknf_scope.
Notation "p 'implies' q" := (FImp p q)
  (at level 90, right associativity) : mknf_scope.

(** This is a useful function that counts the size of the formula, in which each atom and each operator contributes 1. *)
Fixpoint size {n} (f : formula n) : nat :=
  match f with
  | FAtom _ | FBot => 1
  | FAnd p q | FOr p q | FImp p q => S (size p + size q)
  | FNeg p | FK p | FNot p => S (size p)
  end.

(** This is yet another useful function which counts the modal depth, i.e. the maximum number of nested usages of modal operators [K] and [not].*)
Fixpoint modal_depth {n} (f : formula n) : nat :=
  match f with
  | FAtom _ | FBot => 0
  | FAnd p q | FOr p q | FImp p q => Nat.max (modal_depth p) (modal_depth q)
  | FNeg p => modal_depth p
  | FK p | FNot p => S (modal_depth p)
  end.

(** A formula is objective when it doesn't contain any modal operator at all: its truth depends only on the atom values in one world. *)
Fixpoint objectiveb {n} (f : formula n) : bool :=
  match f with
  | FAtom _ | FBot => true
  | FAnd p q | FOr p q | FImp p q => objectiveb p && objectiveb q
  | FNeg p => objectiveb p
  | FK _ | FNot _ => false
  end.

(** A formula is positive when there are no occurrences of the [not] modal operator.*)
Fixpoint positiveb {n} (f : formula n) : bool :=
  match f with
  | FAtom _ | FBot => true
  | FAnd p q | FOr p q | FImp p q => positiveb p && positiveb q
  | FNeg p | FK p => positiveb p
  | FNot _ => false
  end.

(** Transforming the boolean checks into propositions. *)
Definition Objective {n} (f : formula n) : Prop := objectiveb f = true.

Definition Positive {n} (f : formula n) : Prop := positiveb f = true.

(** An important theorem is the fact that objective formulas are exactly the ones in which the modal dept is 0. The two definitions are therefore consistent. *)
Lemma objective_no_modal {n} (f : formula n) :
  Objective f <-> modal_depth f = 0.
Proof.
  unfold Objective. induction f.
 - (* FAtom *) easy.
 - (* FBot *) easy.
 - (* FAnd *) simpl. rewrite andb_true_iff. rewrite IHf1, IHf2.
 destruct (modal_depth f1), (modal_depth f2); easy.
(*
 simpl. Search (?a&&?b=true <-> ?a=true /\ ?b=true). rewrite andb_true_iff.
              split; intros.
              -- destruct H. apply IHf1 in H. apply IHf2 in H0. rewrite H, H0. trivial.
              -- specialize (Nat.max_lub_iff (modal_depth f1) (modal_depth f2) 0); intro.
                Print le. specialize (le_n 0); intro. rewrite <- H in H1 at 1.
                apply H0 in H1. destruct H1. inversion H1; inversion H2. split.
                ---  apply IHf1. assumption.
                ---  apply IHf2. assumption.
*)
 - (* FOr *) simpl.  (* defined in the same way as and *) rewrite andb_true_iff. rewrite IHf1, IHf2.
 destruct (modal_depth f1), (modal_depth f2); easy.
 - (* FImp *) simpl.  (* defined in the same way as and *) rewrite andb_true_iff. rewrite IHf1, IHf2.
 destruct (modal_depth f1), (modal_depth f2); easy.
 - (* FNeg *) easy.
 - (* FK *) easy.
 - (* FNot *) easy.
Qed.

(** This will be useful later, trust me. *)
Definition positive_query {n} (f : formula n) : Prop := Positive f.

(** ** Named propositional front end

    The solver uses [Fin.t n] indices for atoms, but names are easier to write and read.  [named_formula] supplies that input syntax.  A symbol table translates names to indices, and missing names cause the translation to fail.
    Once translated, the formula can be passed to the verified solver.
*)

(** The grammar is the same.*)
Inductive named_formula : Type :=
| NAtom : string -> named_formula
| NBot : named_formula
| NAnd : named_formula -> named_formula -> named_formula
| NOr : named_formula -> named_formula -> named_formula
| NImp : named_formula -> named_formula -> named_formula
| NNeg : named_formula -> named_formula
| NK : named_formula -> named_formula
| NNot : named_formula -> named_formula.

(** A list mapping atom names to internal indices.*)
Definition symbol_table n := list (string * Fin.t n).

(** Resolve an atom's name in the symbol table. Return the index from the first
    matching entry, or [None] if the name is missing. *)
Fixpoint resolve_atom {n} (symbols : symbol_table n) (name : string)
    : option (Fin.t n) :=
  match symbols with
  | [] => None
  | (candidate, atom) :: tl =>
      if String.eqb name candidate then Some atom else resolve_atom tl name
  end.

(** Translate a named formula to the indexed syntax. *)
Fixpoint resolve_named_formula {n} (symbols : symbol_table n)
    (f : named_formula) : option (formula n) :=
  match f with
  | NAtom name =>
      match resolve_atom symbols name with
      | Some atom => Some (FAtom atom)
      | None => None
      end
  | NBot => Some FBot
  | NAnd p q =>
      match resolve_named_formula symbols p, resolve_named_formula symbols q with
      | Some p', Some q' => Some (FAnd p' q')
      | _, _ => None
      end
  | NOr p q =>
      match resolve_named_formula symbols p, resolve_named_formula symbols q with
      | Some p', Some q' => Some (FOr p' q')
      | _, _ => None
      end
  | NImp p q =>
      match resolve_named_formula symbols p, resolve_named_formula symbols q with
      | Some p', Some q' => Some (FImp p' q')
      | _, _ => None
      end
  | NNeg p =>
      match resolve_named_formula symbols p with
      | Some p' => Some (FNeg p') | None => None
      end
  | NK p =>
      match resolve_named_formula symbols p with
      | Some p' => Some (FK p') | None => None
      end
  | NNot p =>
      match resolve_named_formula symbols p with
      | Some p' => Some (FNot p') | None => None
      end
  end.

(** Translate every formula in a named theory. *)
Fixpoint resolve_named_theory {n} (symbols : symbol_table n)
    (t : list named_formula) : option (theory n) :=
  match t with
  | [] => Some []
  | f :: tl =>
      match resolve_named_formula symbols f, resolve_named_theory symbols tl with
      | Some f', Some tl' => Some (f' :: tl')
      | _, _ => None
      end
  end.

(** ** MBNF syntax

    This part is related to MBNF, the other logic studied in these chapters.

<<
    mbnf-formula ::= atom | bottom
                   | "(" mbnf-formula "and" mbnf-formula ")"
                   | "(" mbnf-formula "or" mbnf-formula ")"
                   | "(" mbnf-formula "->" mbnf-formula ")"
                   | "classical-not" mbnf-formula
                   | "B" mbnf-formula                         MBBelief
                   | "not" mbnf-formula                       MBNot
>>

*)

(** The syntax tree for MBNF *)
Inductive mbnf_formula (n : nat) : Type :=
| MBAtom : Fin.t n -> mbnf_formula n
| MBBot : mbnf_formula n
| MBAnd : mbnf_formula n -> mbnf_formula n -> mbnf_formula n
| MBOr : mbnf_formula n -> mbnf_formula n -> mbnf_formula n
| MBImp : mbnf_formula n -> mbnf_formula n -> mbnf_formula n
| MBNeg : mbnf_formula n -> mbnf_formula n
| MBBelief : mbnf_formula n -> mbnf_formula n
| MBNot : mbnf_formula n -> mbnf_formula n.

Arguments MBAtom {n} _.
Arguments MBBot {n}.
Arguments MBAnd {n} _ _.
Arguments MBOr {n} _ _.
Arguments MBImp {n} _ _.
Arguments MBNeg {n} _.
Arguments MBBelief {n} _.
Arguments MBNot {n} _.

(** A list of MBNF formulas to be satisfied together. *)
Definition mbnf_theory n := list (mbnf_formula n).

(** Notation *)
Declare Scope mbnf_scope.
Delimit Scope mbnf_scope with mbnf.

Notation "'atom' '(' a ')'" := (MBAtom a)
  (at level 0, a at level 99, format "'atom' '(' a ')'") : mbnf_scope.
Notation "'bot'" := MBBot : mbnf_scope.
Notation "~ p" := (MBNeg p)
  (at level 75, right associativity) : mbnf_scope.
Notation "'B' p" := (MBBelief p)
  (at level 75, right associativity) : mbnf_scope.
Notation "'not' p" := (MBNot p)
  (at level 75, right associativity) : mbnf_scope.
Notation "p 'and' q" := (MBAnd p q)
  (at level 80, right associativity) : mbnf_scope.
Notation "p 'or' q" := (MBOr p q)
  (at level 85, right associativity) : mbnf_scope.
Notation "p 'implies' q" := (MBImp p q)
  (at level 90, right associativity) : mbnf_scope.

(** Replace [K] with [B], leaving the remaining syntax unchanged. *)
Fixpoint mknf_to_mbnf {n} (f : formula n) : mbnf_formula n :=
  match f with
  | FAtom a => MBAtom a
  | FBot => MBBot
  | FAnd p q => MBAnd (mknf_to_mbnf p) (mknf_to_mbnf q)
  | FOr p q => MBOr (mknf_to_mbnf p) (mknf_to_mbnf q)
  | FImp p q => MBImp (mknf_to_mbnf p) (mknf_to_mbnf q)
  | FNeg p => MBNeg (mknf_to_mbnf p)
  | FK p => MBBelief (mknf_to_mbnf p)
  | FNot p => MBNot (mknf_to_mbnf p)
  end.

(** This one is the true translation: it places a B operator in front of the replacement did before. Its correctness will be proved... later on.*)
Definition subjectivize {n} (t : theory n) : mbnf_theory n :=
  map (fun f => MBBelief (mknf_to_mbnf f)) t.

(** The same operation must of course be applied to queries too. *)
Definition subjectivize_query {n} (q : formula n) : mbnf_formula n :=
  MBBelief (mknf_to_mbnf q).
