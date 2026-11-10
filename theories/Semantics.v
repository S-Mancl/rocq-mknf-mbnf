From Stdlib Require Import Bool List.
From MKNF Require Import Finite Syntax.
Import ListNotations.

Set Implicit Arguments.

(** * Chapter 2: MKNF semantics

    A [valuation] describes one possible world (assignment), while a [cluster] collects the worlds that remain possible. 
    In order to evaluate a formula, we select a current world and two clusters: [mk] for knowledge and [mn] for the assumptions used by [not].
    We can then define satisfaction of a whole theory and the preference conditions that make a satisfying structure a model.

    Clusters are canonical finite-set representatives drawn from [all_clusters]. The semantic ordering itself is the extensional [proper_subset] relation.

    With [I] the distinguished valuation, [M_K] the knowledge cluster, and [M_not] the assumption cluster, [satb] implements:

<<
    I,M_K,M_not |= p        iff p is true in I
    I,M_K,M_not |= bottom   never
    I,M_K,M_not |= ~ F           iff F does not hold
    I,M_K,M_not |= F and G       iff both conjuncts hold
    I,M_K,M_not |= F or G        iff at least one disjunct holds
    I,M_K,M_not |= F implies G   iff F fails or G holds
    I,M_K,M_not |= K F      iff every J in M_K satisfies F
    I,M_K,M_not |= not F    iff some J in M_not does not satisfy F
>>

*)

Fixpoint satb {n} (i : valuation) (mk mn : cluster) (f : formula n) : bool :=
  match f with
  | FAtom a => lookup i a
  | FBot => false
  | FAnd p q => satb i mk mn p && satb i mk mn q
  | FOr p q => satb i mk mn p || satb i mk mn q
  | FImp p q => implb (satb i mk mn p) (satb i mk mn q)
  | FNeg p => negb (satb i mk mn p)
  | FK p => forallb (fun j => satb j mk mn p) mk
  | FNot p => existsb (fun j => negb (satb j mk mn p)) mn
  end.

(** [Sat i mk mn f] is the relational version. *)
Definition Sat {n} i mk mn (f : formula n) : Prop :=
  satb i mk mn f = true.

(** The computed result and [Sat] express the same condition (trivial). *)
Theorem satb_spec {n} i mk mn (f : formula n) :
  satb i mk mn f = true <-> Sat i mk mn f.
Proof. reflexivity. Qed.

(** To know [F], every world in the knowledge cluster must satisfy it. *)
Lemma sat_K_iff {n} i mk mn (f : formula n) :
  Sat i mk mn (FK f) <-> forall j, In j mk -> Sat j mk mn f.
Proof.
  unfold Sat. simpl. rewrite forallb_forall. reflexivity.
Qed.

(** [not F] holds when some world in the assumption cluster fails to satisfy [F]. *)
Lemma sat_not_iff {n} i mk mn (f : formula n) :
  Sat i mk mn (FNot f) <-> exists j, In j mn /\ ~ Sat j mk mn f.
Proof.
  unfold Sat. simpl. rewrite existsb_exists.
  split.
  - (* -> *) intros. repeat destruct H. exists x.
    split.
    -- assumption.
    -- rewrite negb_true_iff in H0.
       intro contra. rewrite H0 in contra. discriminate contra.
  - (* <- *) intros. repeat destruct H. exists x.
    split.
    -- assumption.
    -- rewrite negb_true_iff.
       destruct (satb x mk mn f).
       --- destruct H0. trivial.
       --- reflexivity.
Qed.

(** Satisfiability of a theory (boolean). *)
Definition theory_satb {n} (mk mn : cluster) (t : theory n) : bool :=
  forallb (fun i => forallb (fun f => satb i mk mn f) t) mk.

(** Satisfiability of a theory (relational). *)
Definition TheorySat {n} mk mn (t : theory n) : Prop :=
  forall i, In i mk -> forall f, In f t -> Sat i mk mn f.

(** The two definitions are consistent. *)
Lemma theory_satb_spec {n} mk mn (t : theory n) :
  theory_satb mk mn t = true <-> TheorySat mk mn t.
Proof.
  unfold theory_satb, TheorySat.
  rewrite forallb_forall.
  split; intros.
  - specialize (H i).
    apply H in H0.
    apply forallb_forall with (x := f)  in H0.
    -- unfold Sat. assumption.
    -- assumption.
  - rewrite forallb_forall. intros.
    specialize (H x).
    apply H.
    -- assumption.
    -- assumption.
Qed.

(** ** [Gamma] and MKNF models

    We now define which clusters are models.

    Start with a theory [T] and fixed assumptions [S]. A cluster [M] belongs to [Gamma(T,S)] when:

    - Every axiom of [T] holds at every world in [M].
    - Every valid cluster containing all worlds of [M] and additional worlds fails to satisfy [T].

    In both checks, [S] supplies the assumptions used by [not]. When checking a larger cluster, the knowledge worlds change while these assumptions stay fixed.

    [TheorySat M S T] expresses the first condition.
    [GammaMember T S M] combines both conditions and requires [M] to use a standard representation from our finite enumeration.

    To obtain an MKNF model, use [M] itself as the assumptions:

<<
    M is an MKNF91 model of T
      iff M belongs to Gamma(T,M).
>>

    We use two model conventions. [MKNFModel91] allows an empty cluster, while [MKNFModelNonempty] additionally requires at least one world. The connection with MBNF uses this second convention.

    More possible worlds leave fewer facts true everywhere. Requiring that the cluster cannot be enlarged while satisfying the theory therefore keeps knowledge minimal. *)

(** With assumptions [s] fixed, [candidate] belongs to [Gamma(t,s)] if
    it is a valid cluster,
    it satisfies [t],
    and every valid strict enlargement fails to satisfy [t]. *)
Definition GammaMember {n} (t : theory n) (s candidate : cluster) : Prop :=
  canonical_cluster n candidate /\
  TheorySat candidate s t /\
  forall larger, canonical_cluster n larger ->
    proper_subset candidate larger -> ~ TheorySat larger s t.

(** An MKNF model is a cluster [m] that passes the [GammaMember] test using [m] itself as the assumption cluster. *)
Definition MKNFModel91 {n} (t : theory n) (m : cluster) : Prop :=
  GammaMember t m m.

(** An MKNF model with at least one world is non-empty. This is the convention needed for the connection with MBNF. *)
Definition MKNFModelNonempty {n} (t : theory n) (m : cluster) : Prop :=
  MKNFModel91 t m /\ exists i, In i m.

(** The model condition is [Gamma] membership with the candidate supplying its own assumptions. This lemma simply unfolds that definition. *)
Theorem model91_iff_gamma {n} (t : theory n) m :
  MKNFModel91 t m <-> GammaMember t m m.
Proof. reflexivity. Qed.

(** To use the nonempty convention, take an MKNF91 model and supply a world belonging to it. The other model conditions stay the same. *)
Theorem nonempty_model_bridge {n} (t : theory n) m :
  MKNFModelNonempty t m <->
  MKNFModel91 t m /\ exists i, In i m.
Proof. reflexivity. Qed.

(** The theory entails [q] when [q] holds at every world of every MKNF91 model.
    One counterexample world in one model is enough to refute entailment.
    An empty model has no worlds to check, and therefore any query holds trivially. *)
Definition Entails91 {n} (t : theory n) (q : formula n) : Prop :=
  forall m, MKNFModel91 t m ->
    forall i, In i m -> Sat i m m q.

(** Require [q] at every world of every non-empty MKNF model.
    A counterexample must therefore provide both a nonempty model cluster and a member world where [q] fails. *)
Definition EntailsNonempty {n} (t : theory n) (q : formula n) : Prop :=
  forall m, MKNFModelNonempty t m ->
    forall i, In i m -> Sat i m m q.

(** Require semantic entailment and the source's syntactic restriction on queries: [q] must contain no [not]. *)
Definition PaperEntails91 {n} (t : theory n) (q : formula n) : Prop :=
  positive_query q /\ Entails91 t q.

(** If every MKNF91 model of this theory is nonempty, the two entailment conventions agree. *)
Theorem entailment_bridge {n} (t : theory n) q :
  (forall m, MKNFModel91 t m -> exists i, In i m) ->
  (Entails91 t q <-> EntailsNonempty t q).
Proof.
  intros Hall. split.
  - intros H m [Hm Hne]. now apply H.
  - intros H m Hm. apply H. split; [assumption|now apply Hall].
Qed.

(** ** Semantic invariance lemmas

    These lemmas establish which parts of a structure each class of formula actually uses. *)

(** An objective formula has no modal operators, so changing either cluster cannot affect its truth value. Only the current valuation matters. *)
Lemma objective_satb_independent {n} (f : formula n) :
  Objective f -> forall i mk mn mk' mn',
    satb i mk mn f = satb i mk' mn' f.
Proof.
  intros.
  induction f;simpl; try easy.
  - (* && *) inversion H.
             Search ((?a && ?b = true) <-> (?a = true /\ ?b = true) ).
             rewrite andb_true_iff in H1. inversion H1.
             unfold Objective in *.
             apply IHf1 in H0.
             apply IHf2 in H2.
             rewrite H0, H2.
             trivial.
  - (* || *) inversion H.
             Search ((?a && ?b = true) <-> (?a = true /\ ?b = true) ).
             rewrite andb_true_iff in H1. inversion H1.
             unfold Objective in *.
             apply IHf1 in H0.
             apply IHf2 in H2.
             rewrite H0, H2.
             trivial.
  - (* -> *) inversion H.
             Search ((?a && ?b = true) <-> (?a = true /\ ?b = true) ).
             rewrite andb_true_iff in H1. inversion H1.
             unfold Objective in *.
             apply IHf1 in H0.
             apply IHf2 in H2.
             rewrite H0, H2.
             trivial.
  - (* ~~ *) inversion H.
             unfold Objective in IHf.
             apply IHf in H1.
             rewrite H1.
             trivial.
Qed.

(** The same independence stated using [Sat]. *)
Theorem objective_independent {n} (f : formula n) :
  Objective f -> forall i mk mn mk' mn',
    Sat i mk mn f <-> Sat i mk' mn' f.
Proof.
  intros H i mk mn mk' mn'. unfold Sat.
  now rewrite (objective_satb_independent H i mk mn mk' mn').
Qed.

(** A formula without [not] never consults the assumption cluster. *)
Lemma positive_satb_independent_not {n} (f : formula n) :
  Positive f -> forall i mk mn mn',
    satb i mk mn f = satb i mk mn' f.
Proof.
  induction f; intros; simpl; unfold Positive; simpl; try easy. (* needed a stronger induction hypothesis *)
  - (* && *) unfold Positive in *.
             inversion H.
             rewrite andb_true_iff in H1.
             destruct H1.
             specialize (IHf1 H0). specialize (IHf1 i mk mn mn').
             specialize (IHf2 H1). specialize (IHf2 i mk mn mn').
             rewrite IHf1, IHf2.
             trivial.
  - (* || *) unfold Positive in *.
             inversion H.
             rewrite andb_true_iff in H1.
             destruct H1.
             specialize (IHf1 H0). specialize (IHf1 i mk mn mn').
             specialize (IHf2 H1). specialize (IHf2 i mk mn mn').
             rewrite IHf1, IHf2.
             trivial.
  - (* -> *) unfold Positive in *.
             inversion H.
             rewrite andb_true_iff in H1.
             destruct H1.
             specialize (IHf1 H0). specialize (IHf1 i mk mn mn').
             specialize (IHf2 H1). specialize (IHf2 i mk mn mn').
             rewrite IHf1, IHf2.
             trivial.
  - (* ~~ *) unfold Positive in *.
             inversion H.
             specialize (IHf H1).
             specialize (IHf i mk mn mn').
             rewrite IHf.
             trivial.
  - (* fa *) inversion H.
             unfold Positive in *.
             apply forallb_ext_eq.
             intros.
             apply IHf.
             assumption.
Qed.

(** Same with [Sat]. *)
Theorem positive_independent_not {n} (f : formula n) :
  Positive f -> forall i mk mn mn',
    Sat i mk mn f <-> Sat i mk mn' f.
Proof.
  intros H i mk mn mn'. unfold Sat.
  now rewrite (positive_satb_independent_not H i mk mn mn').
Qed.

(** ** MBNF semantics and the subjectivization boundary

    This comparison replaces MKNF's [K] by MBNF's [B] and explains precisely when the two model notions agree after subjectivization.

    An MBNF model is pointed: [(initial,M,M)] satisfies the theory, [M] is nonempty, and no larger belief cluster can satisfy the theory at any possible initial world while the [not] cluster stays fixed at [M].

    Subjectivization wraps every MKNF axiom in [B].
    That outer modality makes truth independent of the chosen initial world and turns pointed MBNF satisfaction into the all-world satisfaction used by MKNF.
    In the maximality clause, a competing strict superset is rejected if the theory holds at any possible initial valuation; this explains the nested universal quantifiers in [MBNFModel].
    The proofs [subjectivization_model_bridge] and [subjectivization_entailment] state the required nonempty-model hypothesis explicitly. *)

(** Evaluate an MBNF formula. [B F] checks every world in the belief cluster [mb], and [not F] looks for a failure in the assumption cluster [mn]. These rules resemble MKNF's.
    The difference between the logics appears in their model definitions, including where the axioms must hold. *)
Fixpoint mbsatb {n} (i : valuation) (mb mn : cluster)
    (f : mbnf_formula n) : bool :=
  match f with
  | MBAtom a => lookup i a
  | MBBot => false
  | MBAnd p q => mbsatb i mb mn p && mbsatb i mb mn q
  | MBOr p q => mbsatb i mb mn p || mbsatb i mb mn q
  | MBImp p q => implb (mbsatb i mb mn p) (mbsatb i mb mn q)
  | MBNeg p => negb (mbsatb i mb mn p)
  | MBBelief p => forallb (fun j => mbsatb j mb mn p) mb
  | MBNot p => existsb (fun j => negb (mbsatb j mb mn p)) mn
  end.

(** [MBSat i mb mn f] means that the MBNF evaluator returns true for [f] at the supplied world and clusters. *)
Definition MBSat {n} i mb mn (f : mbnf_formula n) : Prop :=
  mbsatb i mb mn f = true.

(** Check all MBNF axioms at one initial world.
    An axiom [p] constrains the initial world, whereas [B p] constrains the belief worlds. *)
Definition MBTheorySatAt {n} i mb mn (t : mbnf_theory n) : Prop :=
  forall f, In f t -> MBSat i mb mn f.

(** An MBNF model has an initial world and a nonempty belief cluster [m].
    The theory holds at that world with both clusters set to [m].
    No strictly larger belief cluster may satisfy the theory at any initial world while assumptions stay fixed at [m].
    The initial world need not belong to [m], so a fact at that world and a belief across the cluster are separate requirements. *)
Definition MBNFModel {n} (t : mbnf_theory n)
    (initial : valuation) (m : cluster) : Prop :=
  In initial (all_valuations n) /\
  canonical_cluster n m /\
  (exists i, In i m) /\
  MBTheorySatAt initial m m t /\
  forall larger, canonical_cluster n larger -> proper_subset m larger ->
    forall j, In j (all_valuations n) ->
      ~ MBTheorySatAt j larger m t.

(** The query must hold at the initial world of every MBNF model. *)
Definition MBNFEntails {n} (t : mbnf_theory n) (q : mbnf_formula n) : Prop :=
  forall initial m, MBNFModel t initial m -> MBSat initial m m q.

(** Replacing [K] with [B] preserves local evaluation when the world and both clusters are unchanged. *)
Lemma mknf_to_mbnf_eval {n} (f : formula n) i mk mn :
  mbsatb i mk mn (mknf_to_mbnf f) = satb i mk mn f.
Proof.
  revert i mk mn. induction f; intros i mk mn; simpl; try reflexivity.
  - now rewrite IHf1, IHf2.
  - now rewrite IHf1, IHf2.
  - now rewrite IHf1, IHf2.
  - now rewrite IHf.
  - apply forallb_ext_eq. intros j Hj. apply IHf.
  - apply existsb_ext_eq. intros j Hj. now rewrite IHf.
Qed.

(** The wrapped MBNF theory holds at an initial world
    exactly when
    the original MKNF theory holds at every knowledge world. *)
Lemma subjectivize_sat_iff {n} (t : theory n) i m assumed :
  MBTheorySatAt i m assumed (subjectivize t) <-> TheorySat m assumed t.
Proof.
  unfold MBTheorySatAt, TheorySat.
  unfold subjectivize, MBSat.
  split.
  - (* -> *) intros.
    specialize (H (MBBelief (mknf_to_mbnf f))). (* this is the correct translation of f *)
    assert (Hin : In (MBBelief (mknf_to_mbnf f))
                     (map (fun x => MBBelief (mknf_to_mbnf x)) t)).
    -- apply in_map_iff.
       exists f.
       split; easy.
    -- specialize (H Hin).
       simpl in *.
       rewrite forallb_forall in H.
       specialize (H i0).
       specialize (H H0).
       unfold Sat.
       Check mknf_to_mbnf_eval.
       rewrite mknf_to_mbnf_eval in H.
       assumption.
  - (* <- *) intros.
    apply in_map_iff in H0.
    repeat destruct H0.
    simpl in *.
    apply forallb_forall.
    intros.
    unfold Sat in *.
    symmetry in H.
    rewrite H with (i:=x0) (f:=x); try assumption.
    rewrite mknf_to_mbnf_eval.
    trivial.
Qed.

(** A nonempty MKNF model cluster gives an MBNF model of the wrapped theory at every valid initial world, and conversely. *)
Theorem subjectivization_model_bridge {n} (t : theory n) m :
  MKNFModelNonempty t m <->
  forall initial, In initial (all_valuations n) ->
    MBNFModel (subjectivize t) initial m.
Proof.
  split.
  - (* -> *) intros.
    inversion H.
    inversion H1.
    repeat destruct H4.
    constructor; try assumption.
    repeat split; try easy.
    -- apply subjectivize_sat_iff. assumption.
    -- intros.
       specialize (H5 larger).
       intro contra.
       specialize (H5 H6).
       specialize (H5 H7).
       apply H5.
       apply subjectivize_sat_iff in contra.
       assumption.
  - (* <- *) intros.
    unfold MBNFModel in H.
    unfold MKNFModelNonempty.
    unfold MKNFModel91.
    unfold GammaMember.
    specialize (H (repeat false n)).
    assert (In (repeat false n) (all_valuations n)).
    -- apply all_valuations_complete.
       apply repeat_length.
    -- specialize (H H0).
       destruct H.
       destruct H1.
       destruct H2.
       destruct H3.
       repeat split; try assumption.
       --- apply subjectivize_sat_iff in H3. assumption.
       --- intros.
           intro contra.
           specialize (H4 larger).
           specialize (H4 H5 H6).
           specialize (H4 (repeat false n)).
           specialize (H4 H0).
           apply H4.
           apply subjectivize_sat_iff.
           assumption.
Qed.

(** An entailment under nonempty MKNF semantics remains valid after wrapping the translated theory and query in [B]. *)
Theorem subjectivization_entailment_forward {n} (t : theory n) q :
  EntailsNonempty t q ->
  MBNFEntails (subjectivize t) (subjectivize_query q).
Proof.
  intros.
  unfold MBNFEntails.
  intros.
  unfold subjectivize_query, MBSat.
  simpl.
  apply forallb_forall.
  intros.
  rewrite mknf_to_mbnf_eval.

  assert (MKNFModelNonempty t m).
  - unfold EntailsNonempty, MBNFModel, MKNFModelNonempty in *.
    unfold MKNFModel91.
    split.
    2: exists x; assumption.
    unfold GammaMember.
    repeat split.
    -- destruct H0.
       destruct H2.
       assumption.
    -- destruct H0.
       destruct H2.
       destruct H3.
       destruct H4.
       rewrite subjectivize_sat_iff in H4. assumption.
    -- intros.
       intro contra.
       destruct H0.
       destruct H4.
       destruct H5.
       destruct H6.
       specialize (H7 larger H2 H3 initial H0).
       apply H7.
       apply subjectivize_sat_iff.
       assumption.
  - unfold EntailsNonempty in H.
    specialize (H m H2 x H1).
    assumption.
Qed.

(** If the wrapped MBNF theory entails the wrapped query, the original MKNF entailment holds under the nonempty convention. *)
Theorem subjectivization_entailment_backward {n} (t : theory n) q :

  MBNFEntails (subjectivize t) (subjectivize_query q) ->
  EntailsNonempty t q.
Proof.
  unfold MBNFEntails.
  unfold EntailsNonempty.
  intros.
  specialize (H i m).
  unfold subjectivize_query, MBSat in H.
  simpl in *.
  unfold Sat.
  rewrite <- mknf_to_mbnf_eval.
  rewrite forallb_forall in H.
  apply H.
  2: exact H1.
  unfold MBNFModel.
  unfold MKNFModelNonempty in H0.
  unfold MKNFModel91 in H0.
  unfold GammaMember in H0.
  repeat destruct H0.
  destruct H3.
  repeat split.
  - apply all_valuations_complete.
    apply (canonical_valuation_length n m i).
    -- exact H0.
    -- exact H1.
  - exact H0.
  - exact H2.
  - apply subjectivization_model_bridge.
  -- unfold MKNFModelNonempty. unfold MKNFModel91. repeat split.
  --- exact H0.
  --- exact H3.
  --- exact H4.
  --- exact H2.
  -- apply all_valuations_complete. apply (canonical_valuation_length n m i).
  --- exact H0.
  --- exact H1.
  - intros. intro contra.
    specialize (H4 larger H5 H6). apply H4.
    apply subjectivize_sat_iff in contra.
    exact contra.
Qed.

(** The two directions give the equivalence used by the algorithms: solving the wrapped MBNF problem gives exactly the nonempty MKNF answer. *)
Theorem subjectivization_entailment {n} (t : theory n) q :
  EntailsNonempty t q <->
  MBNFEntails (subjectivize t) (subjectivize_query q).
Proof.
  split.
  - apply subjectivization_entailment_forward.
  - apply subjectivization_entailment_backward.
Qed.
