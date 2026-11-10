From Stdlib Require Import Bool List Vectors.Fin.
From MKNF Require Import Finite Syntax Semantics.
Import ListNotations.

Set Implicit Arguments.

(** * Chapter 3: Verified propositional reasoning algorithms

    We have defined the formulas and their meaning. We can now write procedures that answer queries, and prove that their answers agree with the semantics from Chapter 2.

    We will do it in two parts. First, we try every possible model, for MKNF and then for MBNF. Later, we use Rosati's partition algorithm to reduce the search. Throughout this chapter, the theories are finite and propositional. *)

(** #<a id="part-i"></a># *)
(** ** Part I: Direct exhaustive reasoning and correctness

    The first approach follows the definition of a model quite closely. We list every canonical cluster, check whether it belongs to [Gamma(T,M)], and look for a world where the query fails. Finding such a world gives us a counterexample. If the search finishes without finding one, the theory entails the query.

    Here is the idea in pseudocode:

<<
    COUNTERMODEL(T,q):
      for each cluster M in powerset(all valuations):
        if M is canonical and M is in Gamma(T,M):
          for each I in M:
            if I,M,M does not satisfy q: return (M,I)
      return none

    ENTAILS(T,q):
      return COUNTERMODEL(T,q) is none
>>

    For [n] atoms we have [2^n] worlds and [2^(2^n)] clusters. The search is therefore expensive, even with a small number of atoms. Its advantage is that we can follow each check back to the semantics.

    We will also write an exhaustive MBNF solver. Its correctness theorem will help us prove the partition algorithm correct in Part II. The partition algorithm itself runs without calling this exhaustive solver. *)

(** The following function checks whether [m] is an MKNF91 model. We check that it is canonical, that it satisfies the theory, and that every strict enlargement fails to satisfy the theory with the assumptions fixed at [m]. Recall that allowing as many worlds as possible keeps knowledge minimal. *)
Definition model91b {n} (t : theory n) (m : cluster) : bool :=
  mem_cluster m (all_clusters n) &&
  theory_satb m m t &&
  negb
    (existsb
       (fun larger => proper_subsetb m larger && theory_satb larger m t)
       (all_clusters n)).

(** A cluster is nonempty when it contains at least one world. The following function checks this. *)
Definition nonemptyb (m : cluster) : bool :=
  match m with [] => false | _ :: _ => true end.

(** To use the nonempty convention, we add the nonemptiness check to [model91b]. *)
Definition model_nonemptyb {n} (t : theory n) (m : cluster) : bool :=
  model91b t m && nonemptyb m.

(** The boolean check agrees with the usual meaning of nonemptiness: there is a world in the cluster. *)
Lemma nonemptyb_spec m :
  nonemptyb m = true <-> exists i, In i m.
Proof.
  induction m; simpl.
  - split;try easy. intro. destruct H. exfalso. assumption.
  - split; intros.
  -- exists a. left; trivial.
  -- trivial.
Qed.

(** We now prove that [model91b] returns true exactly for the MKNF91 models defined in Chapter 2. This includes the check against larger clusters. *)
Theorem model91b_spec {n} (t : theory n) m :
  model91b t m = true <-> MKNFModel91 t m.
Proof.
  unfold model91b, MKNFModel91, GammaMember.
  repeat rewrite andb_true_iff.
  rewrite mem_cluster_spec, theory_satb_spec, negb_true_iff.
  split.
  - intros [[in_all_clusters theorysat] boh].
    repeat split; try trivial.
    intros.
    intro contra.
    assert (notboh : existsb
    (fun larger : cluster => proper_subsetb m larger && theory_satb larger m t)
    (all_clusters n) = true
    ).
    -- apply existsb_exists.
       exists larger.
       split.
       --- unfold canonical_cluster in H. assumption.
       --- rewrite andb_true_iff. split.
       ---- rewrite proper_subsetb_spec. assumption.
       ---- rewrite theory_satb_spec. assumption.
    -- rewrite boh in notboh. discriminate notboh.
  - intros [can [sat boh]].
    repeat split.
    -- unfold canonical_cluster in can. apply can.
    -- exact sat.
    -- destruct (existsb
  (fun larger : cluster => proper_subsetb m larger && theory_satb larger m t)
  (all_clusters n)) eqn:maybecontra.
       --- (* if it were true *) rewrite existsb_exists in maybecontra.
       destruct maybecontra.
       destruct H.
       rewrite andb_true_iff in H0.
       destruct H0.
       specialize (boh x).
       unfold canonical_cluster in boh.
       rewrite proper_subsetb_spec in H0.
       specialize (boh H H0).
       rewrite theory_satb_spec in H1.
       apply boh in H1.
       exfalso; trivial.
       --- (* but there is none *) trivial.
Qed.

(** The same correspondence holds after adding the nonemptiness requirement. *)
Theorem model_nonemptyb_spec {n} (t : theory n) m :
  model_nonemptyb t m = true <-> MKNFModelNonempty t m.
Proof.
  unfold model_nonemptyb, MKNFModelNonempty.
  split; rewrite andb_true_iff, model91b_spec, nonemptyb_spec; trivial.
Qed.

(** We list every canonical cluster together with each world belonging to it. These pairs are the places where an MKNF query can fail. An empty cluster contributes no pairs. *)
Definition candidate_pairs n : list (cluster * valuation) :=
  flat_map
    (fun m => map (fun i => (m, i)) m)
    (all_clusters n).

(** A pair belongs to this list if and only if its cluster is canonical and its world belongs to that cluster. *)
Lemma candidate_pairs_spec n m i :
  In (m, i) (candidate_pairs n) <->
  canonical_cluster n m /\ In i m.
Proof.
  unfold candidate_pairs.
  rewrite in_flat_map.
  unfold canonical_cluster.
  split.
  - (* -> *) intros.
             repeat destruct H.
             apply in_map_iff in H0.
             destruct H0.
             destruct H0.
             inversion H0. subst.
             split; assumption.
  - (* <- *) intros.
             destruct H.
             exists m.
             split.
             -- assumption.
             -- apply in_map. assumption.
Qed.

(** A pair gives a counterexample when the cluster is a model and the query fails at the chosen world. Here we take pairs from [candidate_pairs], so we already know that the world belongs to the cluster. *)
Definition bad_pairb {n} (t : theory n) (q : formula n)
    (p : cluster * valuation) : bool :=
  let '(m, i) := p in
  model91b t m && negb (satb i m m q).

(** We can now answer the query. Search all candidate pairs for a counterexample, then negate the result. Returning true means that the query holds at every world of every MKNF91 model. *)
Definition entails91b {n} (t : theory n) (q : formula n) : bool :=
  negb (existsb (bad_pairb t q) (candidate_pairs n)).

(** For the nonempty convention, we use the same check with [model_nonemptyb]. World membership still comes from [candidate_pairs]. *)
Definition bad_nonempty_pairb {n} (t : theory n) (q : formula n)
    (p : cluster * valuation) : bool :=
  let '(m, i) := p in
  model_nonemptyb t m && negb (satb i m m q).

(** Once again, the theory entails the query if the search finds no counterexample. This version uses nonempty models. *)
Definition entails_nonemptyb {n} (t : theory n) (q : formula n) : bool :=
  negb (existsb (bad_nonempty_pairb t q) (candidate_pairs n)).

(** Sometimes we want to see why a query fails. The following function returns the first counterexample found, or [None] when there is none. *)
Definition countermodel91b {n} (t : theory n) (q : formula n) :
    option (cluster * valuation) :=
  find (bad_pairb t q) (candidate_pairs n).

(** We also want to check a counterexample supplied to us. Its cluster must be a model, its world must belong to that cluster, and the query must fail there. Since the pair may come from outside our search, we check membership explicitly. *)
Definition valid_counterexampleb {n} (t : theory n) (q : formula n)
    (p : cluster * valuation) : bool :=
  let '(m, i) := p in
  model91b t m && mem_valuation i m && negb (satb i m m q).


(** The validator returns true exactly when all three conditions of an MKNF91 counterexample hold. *)
Theorem valid_counterexampleb_spec {n} (t : theory n) q m i :
  valid_counterexampleb t q (m, i) = true <->
  MKNFModel91 t m /\ In i m /\ ~ Sat i m m q.
Proof.
  unfold valid_counterexampleb.
  repeat rewrite andb_true_iff.
  rewrite model91b_spec.
  rewrite mem_valuation_spec.
  split.
  - intros [[model inside] fls].
    split; try assumption.
    split; try assumption.
    intro contra.
    rewrite negb_true_iff in fls.
    unfold Sat in contra.
    rewrite fls in contra. discriminate contra.
  - intros [model [inside notsat]].
    split.
    -- split; assumption.
    -- destruct (satb i m m q) eqn:maybecontra.
    --- rewrite satb_spec in maybecontra. apply notsat in maybecontra. exfalso. trivial.
    --- trivial.
Qed.

(** *** Checking counterexamples

    We have a function that searches for counterexamples and another that checks a supplied pair. The search already knows that each world belongs to its cluster. The next theorem uses this fact to justify the shorter check in [bad_pairb]. *)

(** For a pair from [candidate_pairs], [bad_pairb] checks exactly the conditions needed for a counterexample. *)
Theorem bad_pairb_spec_on_candidates {n} (t : theory n) q m i :
  In (m, i) (candidate_pairs n) ->
  (bad_pairb t q (m, i) = true <->
   MKNFModel91 t m /\ In i m /\ ~ Sat i m m q).
Proof.
  intros.
  apply candidate_pairs_spec in H.
  destruct H.
  unfold bad_pairb. rewrite andb_true_iff. rewrite model91b_spec.
  split.
  - (* -> *) intros [model notsat].
             split.
             -- exact model.
             -- split.
             --- exact H0.
             --- intro contra.
                 rewrite <- satb_spec in contra.
                 rewrite negb_true_iff in notsat.
                 rewrite notsat in contra. discriminate contra.
  - (* <- *) intros [model [inside notsat]].
             split.
             -- exact model.
             -- rewrite negb_true_iff.
                destruct (satb i m m q) eqn:maybecontra.
                --- rewrite satb_spec in maybecontra. apply notsat in maybecontra. exfalso. assumption.
                --- trivial.
Qed.

(** Here is the correctness theorem for the first solver. A true answer means that the theory entails the query, and every query entailed by the theory receives a true answer. These are soundness and completeness, respectively. *)
Theorem entails91b_correct {n} (t : theory n) q :
  entails91b t q = true <-> Entails91 t q.
Proof.
  unfold entails91b, Entails91.
  rewrite negb_true_iff.
  split.
  - (* -> *) intros.
             rewrite <- satb_spec.
             destruct (satb i m m q) eqn:maybecontra; try trivial.
             assert (Hpair : In (m, i) (candidate_pairs n)).
             -- apply candidate_pairs_spec.
                split; try assumption.
                destruct H0. assumption.
             -- assert (Hex : existsb (bad_pairb t q) (candidate_pairs n) = true).
                --- apply existsb_exists. exists (m, i). split; try assumption.
                    unfold bad_pairb.
                    rewrite andb_true_iff. split.
                    ---- rewrite model91b_spec. exact H0.
                    ---- rewrite negb_true_iff. exact maybecontra.
                --- rewrite H in Hex. assumption.
  - (* <- *) intros.
             destruct (existsb (bad_pairb t q) (candidate_pairs n)) eqn:maybecontra; trivial.
             rewrite existsb_exists in maybecontra.
             destruct maybecontra.
             destruct H0.
             destruct x.
             rewrite bad_pairb_spec_on_candidates in H1.
             -- destruct H1. destruct H2.
                specialize (H c H1 v H2).
                exfalso.
                apply H3 in H.
                exact H.
             -- exact H0.
Qed.

(** We prove the same result for the nonempty solver. Once an application computes a true answer, this theorem turns it into a proof of entailment. *)
Theorem entails_nonemptyb_correct {n} (t : theory n) q :
  entails_nonemptyb t q = true <-> EntailsNonempty t q.
Proof.
  unfold entails_nonemptyb, EntailsNonempty.
  rewrite negb_true_iff.
  split.
  - (* -> *) intros.
             unfold Sat.
             destruct (satb i m m q) eqn:maybecontra; try trivial.
             assert (Hpair : In (m, i) (candidate_pairs n)).
             -- rewrite candidate_pairs_spec. unfold MKNFModelNonempty in H0. unfold MKNFModel91 in H0. unfold GammaMember in H0. destruct H0. destruct H0.
                split; assumption.
             -- assert (Hex : existsb (bad_nonempty_pairb t q) (candidate_pairs n) = true).
                --- rewrite existsb_exists.
                    exists (m, i).
                    split.
                    ---- assumption.
                    ---- unfold bad_nonempty_pairb.
                         rewrite andb_true_iff.
                         split.
                         ----- rewrite model_nonemptyb_spec. exact H0.
                         ----- rewrite negb_true_iff. exact maybecontra.
                --- rewrite H in Hex. discriminate Hex.
  - (* <- *) intros.
             destruct (existsb (bad_nonempty_pairb t q) (candidate_pairs n)) eqn:maybecontra; try trivial.
             rewrite existsb_exists in maybecontra.
             destruct maybecontra.
             destruct x, H0.
             unfold bad_nonempty_pairb in H1.
             rewrite andb_true_iff in H1.
             destruct H1.
             rewrite model_nonemptyb_spec in H1.
             rewrite negb_true_iff in H2.
             rewrite candidate_pairs_spec in H0.
             destruct H0.
             specialize (H c H1 v H3).
             rewrite <- satb_spec in H.
             rewrite H in H2.
             discriminate H2.
Qed.


(** If we ask several queries about the same theory, we can compute its nonempty models once and reuse the list. We must prove that the stored list contains exactly all the models in our enumeration. The following theorem then rewrites [entails_nonemptyb] to use that list, so its correctness theorem still applies. *)
Theorem entails_nonemptyb_from_model_catalogue {n} (t : theory n) models :
  filter (model_nonemptyb t) (all_clusters n) = models ->
  forall q, entails_nonemptyb t q =
    forallb (fun m => forallb (fun i => satb i m m q) m) models.
Proof.
  intros.
  apply eq_true_iff_eq.
  rewrite entails_nonemptyb_correct.
  rewrite <- H.
  rewrite forallb_forall.
  split.
  - (* -> *) intros.
             rewrite forallb_forall.
             intros.
             rewrite satb_spec.
             unfold EntailsNonempty in H0.
             apply filter_In in H1.
             destruct H1.
             rewrite model_nonemptyb_spec in H3.
             specialize (H0 x H3 x0 H2).
             assumption.
  - (* <- *) intros.
             unfold EntailsNonempty.
             intros.
             specialize (H0 m).
             rewrite filter_In in H0.
             rewrite model_nonemptyb_spec in H0.
             assert (In m (all_clusters n)).
             assert (forallb (fun i : valuation => satb i m m q) m = true).
             -- apply H0. split.
                --- unfold MKNFModelNonempty in H1. unfold MKNFModel91 in H1. unfold GammaMember in H1.
                    destruct H1.
                    destruct H1.
                    unfold canonical_cluster in H1.
                    exact H1.
                --- exact H1.
             -- unfold MKNFModelNonempty in H1. unfold MKNFModel91 in H1. unfold GammaMember in H1.
                destruct H1.
                destruct H1.
                unfold canonical_cluster in H1.
                exact H1.
             -- pose proof (conj H3 H1) as Hmerge.
                specialize (H0 Hmerge).
                rewrite forallb_forall in H0.
                specialize (H0 i H2).
                rewrite satb_spec in H0.
                exact H0.
Qed.

Arguments entails_nonemptyb_from_model_catalogue {n t models} _ q.


(** Every counterexample returned by our search is valid: its cluster is a model and contains a world where the query fails. *)
Theorem countermodel91b_sound {n} (t : theory n) q m i :
  countermodel91b t q = Some (m, i) ->
  MKNFModel91 t m /\ In i m /\ ~ Sat i m m q.
Proof.
  unfold countermodel91b.
  intros.
  apply find_some in H.
  destruct H.
  apply bad_pairb_spec_on_candidates; assumption.
Qed.

(** This is a useful fact about [find]. If some entry in a list passes the test, [find] returns a passing entry. It may find an earlier entry than the one we supplied. *)
Lemma find_complete {A} (f : A -> bool) xs x :
  In x xs -> f x = true -> exists y, find f xs = Some y.
Proof.
  intros.
  induction xs.
  - destruct H.
  - simpl in *.
    destruct H.
    -- subst. rewrite H0. exists x. trivial.
    -- destruct (f a) eqn:fa.
    --- exists a. trivial.
    ---  apply IHxs. exact H.
Qed.

(** We have shown that returned counterexamples are valid. We now prove the other direction: whenever entailment fails, the search returns a counterexample. *)
Theorem countermodel91b_complete {n} (t : theory n) q :
  ~ Entails91 t q ->
  exists m i, countermodel91b t q = Some (m, i).
Proof.
  intros.
  assert (entails91b t q = false).
  - destruct (entails91b t q ) eqn:maybecontra; try trivial.
    rewrite entails91b_correct in maybecontra.
    apply H in maybecontra.
    exfalso. assumption.
  - unfold entails91b in H0.
    rewrite negb_false_iff in H0.
    rewrite existsb_exists in H0.
    destruct H0.
    destruct x.
    unfold countermodel91b.
    destruct H0.
    destruct (find_complete (bad_pairb t q) (candidate_pairs n) (c,v)); try assumption.
    destruct x.
    exists c0, v0.
    exact H2.
Qed.


(** *** Exhaustive MBNF reasoning

    We now apply the same idea directly to the MBNF semantics. An MBNF candidate has an initial world and a belief cluster. The initial world can be outside the cluster.

    To reject a candidate on minimal-belief grounds, we need a strictly larger belief cluster and an initial world where the theory holds, keeping the original assumptions fixed. The two nested searches in [mbnf_modelb] look for such a pair.

    This solver will also be useful in the correctness proofs of Part II. Those proofs use it to obtain countermodels; the partition procedure runs its own search. *)

(** Check every axiom at the given initial world, using the supplied belief and assumption clusters. *)
Definition mb_theory_sat_atb {n} i mb mn (t : mbnf_theory n) : bool :=
  forallb (fun f => mbsatb i mb mn f) t.

(** The boolean theory check agrees with [MBTheorySatAt] from Chapter 2. *)
Lemma mb_theory_sat_atb_spec {n} i mb mn (t : mbnf_theory n) :
  mb_theory_sat_atb i mb mn t = true <-> MBTheorySatAt i mb mn t.
Proof.
  unfold mb_theory_sat_atb, MBTheorySatAt. rewrite forallb_forall. reflexivity.
Qed.

(** The following function checks the MBNF model conditions. We require a valid initial world, a canonical nonempty cluster, and truth of every axiom at that initial world. We then look for a strict enlargement satisfying the theory at some initial world with the original assumptions fixed. If we find one, the candidate fails the minimal-belief condition. *)
Definition mbnf_modelb {n} (t : mbnf_theory n)
    (initial : valuation) (m : cluster) : bool :=
  mem_valuation initial (all_valuations n) &&
  mem_cluster m (all_clusters n) &&
  nonemptyb m &&
  mb_theory_sat_atb initial m m t &&
  negb
    (existsb
       (fun larger =>
          proper_subsetb m larger &&
          existsb
            (fun j => mb_theory_sat_atb j larger m t)
            (all_valuations n))
       (all_clusters n)).

(** We prove that this check accepts exactly the MBNF models. In particular, the enlargement search covers every possible initial world. *)
Theorem mbnf_modelb_spec {n} (t : mbnf_theory n) initial m :
  mbnf_modelb t initial m = true <-> MBNFModel t initial m.
Proof.
  unfold mbnf_modelb, MBNFModel.
  repeat rewrite andb_true_iff.
  rewrite mem_valuation_spec, mem_cluster_spec,nonemptyb_spec, mb_theory_sat_atb_spec.
  rewrite negb_true_iff.
  split.
  - (* -> *) intros.
             repeat destruct H.
             repeat split; try assumption.
             intros.
             intro contra.
             assert (forall a, forall b, a = b -> ~(a = negb b)).
             -- intros.
                intro contrabis.
                rewrite H7 in contrabis. destruct b; discriminate contrabis.
             -- apply H7 in H0. simpl in H0.
                rewrite existsb_exists in H0.
                apply H0.
                exists larger.
                rewrite andb_true_iff.
                repeat split; try assumption.
                rewrite proper_subsetb_spec. assumption.
                rewrite existsb_exists.
                exists j.
                split; try assumption.
                rewrite mb_theory_sat_atb_spec.
                assumption.
  - (* <- *) intros.
             destruct H.
             destruct H0.
             destruct H1.
             destruct H2.
             repeat split; try assumption.
             destruct (existsb
  (fun larger : cluster =>
   proper_subsetb m larger &&
   existsb (fun j : valuation => mb_theory_sat_atb j larger m t) (all_valuations n))
  (all_clusters n)) eqn:boh; try trivial.
             rewrite existsb_exists in boh.
             destruct boh.
             destruct H4.
             rewrite andb_true_iff in H5.
             destruct H5.
             rewrite existsb_exists in H6.
             destruct H6.
             destruct H6.
             rewrite mb_theory_sat_atb_spec in H7.
             rewrite proper_subsetb_spec in H5.
             unfold canonical_cluster in H3.
             specialize (H3 x H4 H5 x0 H6 H7).
             exfalso. trivial.
Qed.

(** List all pairs of a valid initial world and a canonical cluster. The model check will decide which ones are models. Recall that the initial world need not belong to the cluster. *)
Definition mbnf_model_pairs n : list (valuation * cluster) :=
  flat_map
    (fun i => map (fun m => (i, m)) (all_clusters n))
    (all_valuations n).

(** The enumeration contains exactly the pairs whose initial world is valid and whose cluster is canonical. *)
Lemma mbnf_model_pairs_spec n i m :
  In (i, m) (mbnf_model_pairs n) <->
  In i (all_valuations n) /\ canonical_cluster n m.
Proof.
  unfold mbnf_model_pairs, canonical_cluster.
  rewrite in_flat_map.
  split.
  - (* -> *) intros.
             destruct H.
             destruct H.
             apply in_map_iff in H0.
             destruct H0.
             destruct H0.
             inversion H0.
             subst.
             split; assumption.
  - (* <- *) intros.
             destruct H.
             exists i.
             split; try assumption.
             apply in_map_iff.
             exists m.
             split; trivial.
Qed.

(** A pair gives an MBNF counterexample when it is a model of the theory and the query fails at its initial world. *)
Definition mbnf_bad_pairb {n} (t : mbnf_theory n) (q : mbnf_formula n)
    (p : valuation * cluster) : bool :=
  let '(i, m) := p in mbnf_modelb t i m && negb (mbsatb i m m q).

(** The exhaustive MBNF solver searches these pairs and returns true if none is a counterexample. As before, the search over all clusters makes this expensive. *)
Definition mbnf_exhaustive_entailsb {n}
    (t : mbnf_theory n) (q : mbnf_formula n) : bool :=
  negb (existsb (mbnf_bad_pairb t q) (mbnf_model_pairs n)).

(** The exhaustive solver returns true if and only if the theory entails the query in MBNF. We will use this result in the proofs of Part II. *)
Theorem mbnf_exhaustive_entailsb_correct {n}
    (t : mbnf_theory n) q :
  mbnf_exhaustive_entailsb t q = true <-> MBNFEntails t q.
Proof.
  unfold mbnf_exhaustive_entailsb, MBNFEntails.
  rewrite negb_true_iff.
  split.
  - (* -> *) intros.
             unfold MBSat.
             destruct (mbsatb initial m m q) eqn:boh; try trivial.
             assert (Hpair : In (initial, m) (mbnf_model_pairs n)).
             -- apply mbnf_model_pairs_spec.
                unfold MBNFModel in H0.
                destruct H0.
                destruct H1.
                pose (conj H0 H1). exact a.
             -- assert (Hex : existsb (mbnf_bad_pairb t q) (mbnf_model_pairs n) = true).
                --- rewrite existsb_exists.
                    exists (initial, m).
                    split; try assumption.
                    unfold mbnf_bad_pairb.
                    rewrite andb_true_iff.
                    rewrite mbnf_modelb_spec.
                    rewrite negb_true_iff.
                    split; assumption.
                ---  rewrite H in Hex. trivial.
  - (* <- *) intros.
             destruct (existsb (mbnf_bad_pairb t q) (mbnf_model_pairs n)) eqn:maybecontra; try trivial.
             rewrite existsb_exists in maybecontra.
             destruct maybecontra.
             destruct x.
             specialize (H v c).
             destruct H0.
             rewrite <- mbnf_modelb_spec in H.
             unfold MBSat in H.
             unfold mbnf_bad_pairb in H1.
             rewrite andb_true_iff in H1.
             destruct H1.
             apply H in H1.
             rewrite negb_true_iff in H2.
             rewrite H1 in H2.
             discriminate H2.
Qed.

(** The translation from Chapter 2 lets us answer a nonempty MKNF query with the MBNF solver. We translate the theory and the query, wrap them in [B], and use the subjectivization theorem to obtain correctness. *)
Theorem mknf_subjective_solver_correct {n} (t : theory n) q :
  mbnf_exhaustive_entailsb (subjectivize t) (subjectivize_query q) = true <->
  EntailsNonempty t q.
Proof.
  rewrite mbnf_exhaustive_entailsb_correct.
  rewrite subjectivization_entailment.
  easy.
Qed.

(** The direct nonempty MKNF solver and the translated exhaustive MBNF solver always give the same answer. Their searches may take different amounts of work. *)
Theorem direct_and_subjective_solvers_agree {n} (t : theory n) q :
  entails_nonemptyb t q =
  mbnf_exhaustive_entailsb (subjectivize t) (subjectivize_query q).
Proof.
  destruct (entails_nonemptyb t q) eqn:Hdirect;
    destruct (mbnf_exhaustive_entailsb (subjectivize t)
      (subjectivize_query q)) eqn:Hsubjective; try reflexivity.
  - apply entails_nonemptyb_correct in Hdirect.
    apply mknf_subjective_solver_correct in Hdirect.
    rewrite Hdirect in Hsubjective. discriminate Hsubjective.
  - apply mknf_subjective_solver_correct in Hsubjective.
    apply entails_nonemptyb_correct in Hsubjective.
    rewrite Hdirect in Hsubjective. discriminate Hsubjective.
Qed.

(** #<a id="part-ii"></a># *)
(** ** Part II: Rosati's general propositional procedure

    We now implement Figure 1 of {{https://doi.org/10.1613/jair.637}Rosati (1999), Reasoning about Minimal Belief and Negation as Failure}, Sections 4.1--4.2.

    The idea is to guess the truth values of modal formulas and use those values to build an objective formula. Its satisfying worlds give us a candidate cluster. We then check that the guess agrees with those worlds and that the candidate meets the model conditions.

    We will first define these constructions, then prove the three checks correct. If you want to see the algorithm before following its proofs, look at [objective_base], the three Figure 1 conditions, and [rosati_general_not_entailsb_correct].

    At the end, we extend the procedure to arbitrary queries and connect it to nonempty MKNF. Our propositional satisfiability checks try the finite list of valuations. *)

(** *** Modal occurrences and objective reducts

    We call a formula starting with [B] or [not] a modal atom. For each relevant modal atom, we guess a truth value. A partition stores the ones guessed true; the remaining ones are guessed false.

    Using these guesses, we can replace modal formulas with true or false. The result is called an objective reduct. *)

(** First, we need to decide whether two formulas have the same syntax tree. *)
Definition mbnf_formula_eq_dec {n} :
  forall x y : mbnf_formula n, {x = y} + {x <> y}.
Proof. decide equality; apply Fin.eq_dec. Defined.

(** The following function gives the same equality check as a boolean. We will use it to recognise repeated formulas in partitions. *)
Definition mbnf_formula_eqb {n} (x y : mbnf_formula n) : bool :=
  if mbnf_formula_eq_dec x y then true else false.

(** The boolean equality check returns true if and only if the formulas are equal. *)
Lemma mbnf_formula_eqb_spec {n} (x y : mbnf_formula n) :
  mbnf_formula_eqb x y = true <-> x = y.
Proof.
  unfold mbnf_formula_eqb.
  destruct (mbnf_formula_eq_dec x y) eqn:maybecontra; easy.
Qed.

(** Collect the subformulas starting with [B] or [not]. We also look inside modal operators: [B (not p)] contributes both [B (not p)] and [not p]. For now, we keep repeated occurrences. *)
Fixpoint formula_modal_occurrences {n} (f : mbnf_formula n) :
    list (mbnf_formula n) :=
  match f with
  | MBAtom _ | MBBot => []
  | MBAnd p q | MBOr p q | MBImp p q => formula_modal_occurrences p ++ formula_modal_occurrences q
  | MBNeg p => formula_modal_occurrences p
  | MBBelief p => MBBelief p :: formula_modal_occurrences p
  | MBNot p => MBNot p :: formula_modal_occurrences p
end.

(** A partition stores the modal formulas we guess true. Among the relevant formulas, those missing from the list are guessed false. We still have to check whether any structure agrees with this guess. *)
Definition modal_partition n := list (mbnf_formula n).

(** Look up a formula in the partition to read its guessed truth value. Equal formulas receive the same answer. *)
Definition modal_mem {n} (f : mbnf_formula n) (p : modal_partition n) : bool :=
  existsb (mbnf_formula_eqb f) p.

(** The lookup returns true if and only if the formula belongs to the partition list. *)
Lemma modal_mem_spec {n} (f : mbnf_formula n) p :
  modal_mem f p = true <-> In f p.
Proof.
  unfold modal_mem.
  rewrite existsb_exists.
  split; intros.
  - (* -> *) repeat destruct H.
             rewrite mbnf_formula_eqb_spec in H0. subst. assumption.
  - (* <- *) exists f. split; try trivial.
             rewrite mbnf_formula_eqb_spec. trivial.
Qed.

(** We can also obtain a partition from a structure whose worlds and clusters are already given. Keep the formulas in the supplied list that are true in that structure. *)
Definition induced_modal_partition {n} (occurrences : list (mbnf_formula n))
    (i : valuation) (mb mn : cluster) : modal_partition n :=
  filter (fun f => mbsatb i mb mn f) occurrences.

(** We write the constant true as [~ bot]. We will use it for an empty conjunction and for modal formulas guessed true. *)
Definition mb_true {n} : mbnf_formula n := MBNeg MBBot.

(** Replace [B F] and [not F] with the constants specified by the partition. Keep atoms and boolean connectives. For example, guessing [B p] true turns [(B p) implies q] into [true implies q]. The resulting formula has no modal operators. *)
Fixpoint mb_objective_reduct {n} (p : modal_partition n)
    (f : mbnf_formula n) : mbnf_formula n :=
  match f with
  | MBAtom a => MBAtom a
  | MBBot => MBBot
  | MBAnd x y => MBAnd (mb_objective_reduct p x) (mb_objective_reduct p y)
  | MBOr x y => MBOr (mb_objective_reduct p x) (mb_objective_reduct p y)
  | MBImp x y => MBImp (mb_objective_reduct p x) (mb_objective_reduct p y)
  | MBNeg x => MBNeg (mb_objective_reduct p x)
  | MBBelief x as modal => if modal_mem modal p then mb_true else MBBot
  | MBNot x as modal => if modal_mem modal p then mb_true else MBBot
  end.

(** For a formula in the supplied list, membership in the induced partition gives its actual truth value in the structure. We need the membership premise because formulas outside the supplied list were never recorded. *)
Lemma modal_mem_induced {n} (occurrences : list (mbnf_formula n))
    (i : valuation) (mb mn : cluster) (f : mbnf_formula n) :
  In f occurrences ->
  modal_mem f (induced_modal_partition occurrences i mb mn) =
  mbsatb i mb mn f.
Proof.
  intros.
  destruct (mbsatb i mb mn f) eqn:boh.
  - (* if true *) rewrite modal_mem_spec.
                  unfold induced_modal_partition.
                  apply filter_In.
                  split; assumption.
  - (* if false*) destruct (modal_mem f (induced_modal_partition occurrences i mb mn)) eqn:maybecontra; try trivial.
                  rewrite modal_mem_spec in maybecontra.
                  unfold induced_modal_partition in maybecontra.
                  apply filter_In in maybecontra.
                  destruct maybecontra.
                  rewrite boh in H1.
                  discriminate H1.
Qed.

(** Figure 1 accepts positive queries, meaning queries with no occurrence of [not]. The following function checks this, including inside nested operators. [B] and classical negation are allowed. *)
Fixpoint mbnf_positiveb {n} (f : mbnf_formula n) : bool :=
  match f with
  | MBAtom _ | MBBot => true
  | MBAnd p q | MBOr p q | MBImp p q => mbnf_positiveb p && mbnf_positiveb q
  | MBNeg p | MBBelief p => mbnf_positiveb p
  | MBNot _ => false
  end.

(** *** Objective bases and their meaning *)

(** Collect the modal occurrences from every axiom of the theory. We keep nested occurrences and repetitions. Modal formulas that appear only in the query will be handled by [query_reduct]. *)
Definition theory_modal_atoms {n} (t : mbnf_theory n) :=
  flat_map formula_modal_occurrences t.

(** We can now enumerate the guesses by taking every subset of the theory's modal list. Each subset records the formulas guessed true. Repeated occurrences can give repeated guesses; we will remove that extra work later. *)
Definition rosati_partitions {n} (t : mbnf_theory n) :=
  powerset (theory_modal_atoms t).

(** Compare two partitions on the supplied list of modal formulas. They agree when every formula in that list has the same guessed value. Their order and any extra entries outside the list do not affect the comparison. *)
Definition partition_equivb {n} (atoms p r : list (mbnf_formula n)) :=
  forallb (fun f => Bool.eqb (modal_mem f p) (modal_mem f r)) atoms.

(** The comparison returns true exactly when the two partitions give the same answer for each formula in the supplied list. *)
Lemma partition_equivb_spec {n} (atoms p r : list (mbnf_formula n)) :
  partition_equivb atoms p r = true <->
  forall f, In f atoms -> modal_mem f p = modal_mem f r.
Proof.
  unfold partition_equivb.
  rewrite forallb_forall.
  split; intros.
  - specialize (H f H0).
    rewrite eqb_true_iff in H.
    exact H.
  - rewrite eqb_true_iff.
    apply (H x H0).
Qed.


(** Keep the valuations where [f] is true with empty clusters. We will use this function with objective formulas, whose truth depends only on the valuation. In that case, it lists their propositional models. *)
Definition objective_worlds {n} (f : mbnf_formula n) : cluster :=
  filter (fun i => mbsatb i [] [] f) (all_valuations n).

(** A world belongs to the resulting list exactly when it is a valid valuation and [f] is true there with empty clusters. *)
Lemma objective_worlds_spec {n} (f : mbnf_formula n) i :
  In i (objective_worlds f) <->
  In i (all_valuations n) /\ mbsatb i [] [] f = true.
Proof. unfold objective_worlds. apply filter_In. Qed.

(** Filtering the list of all valuations gives a canonical cluster. We can therefore use the worlds satisfying an objective formula in our model checks. *)
Lemma objective_worlds_canonical {n} (f : mbnf_formula n) :
  canonical_cluster n (objective_worlds f).
Proof. apply filter_in_powerset. Qed.

(** Every world belonging to a canonical cluster is a valid valuation for our language. *)
Lemma canonical_world n m i :
  canonical_cluster n m -> In i m -> In i (all_valuations n).
Proof. intros Hm Hi. exact (powerset_member_is_subset _ _ Hm i Hi). Qed.

(** Changing the order of worlds or repeating them in a cluster leaves the truth of a formula unchanged. What matters is which worlds belong to each cluster. *)
Lemma mbsatb_extensional {n} (f : mbnf_formula n) i mb mn mb' mn' :
  same_set mb mb' -> same_set mn mn' ->
  mbsatb i mb mn f = mbsatb i mb' mn' f.
Proof.
  revert i.
  induction f; intros; try easy.
  - (* and *) simpl.
              specialize (IHf1 i H H0).
              specialize (IHf2 i H H0).
              rewrite IHf1, IHf2.
              trivial.
  - (* or *)  simpl.
              specialize (IHf1 i H H0).
              specialize (IHf2 i H H0).
              rewrite IHf1, IHf2.
              trivial.
  - (* imp *) simpl.
              specialize (IHf1 i H H0).
              specialize (IHf2 i H H0).
              rewrite IHf1, IHf2.
              trivial.
  - (* neg *) simpl.
              specialize (IHf i H H0).
              rewrite IHf.
              trivial.
  - (* bel *) simpl.
              assert (forall i : valuation, mbsatb i mb mn f = mbsatb i mb' mn' f).
              intro. specialize (IHf i0 H H0). assumption.
              destruct (forallb (fun j : valuation => mbsatb j mb' mn' f) mb') eqn:maybecontra.
              -- rewrite forallb_forall in *. intros.
                 specialize (H1 x).
                 specialize (maybecontra x).
                 rewrite H1.
                 apply maybecontra.
                 unfold same_set in H.
                 apply (proj1 H).
                 assumption.
              -- rewrite forallb_false_exists in *.
                 destruct maybecontra.
                 exists x.
                 split.
                 --- unfold same_set in H.
                     unfold subset in H.
                     apply (proj2 H).
                     exact (proj1 H2).
                 --- destruct H2.
                     specialize (H1 x).
                     rewrite H3 in H1.
                     assumption.
  - (* not *) simpl.
              apply Bool.eq_true_iff_eq.
              repeat rewrite existsb_exists.
              unfold same_set in H0.
              unfold subset in H0.
              split; intros.
              -- destruct H1.
                 exists x.
                 split.
                 --- apply ((proj1 H0) x (proj1 H1)).
                 --- specialize (IHf x H H0).
                     rewrite <- IHf.
                     exact (proj2 H1).
              -- destruct H1.
                 exists x.
                 split.
                 --- apply ((proj2 H0) x (proj1 H1)).
                 --- specialize (IHf x H H0).
                     rewrite IHf.
                     exact (proj2 H1).
Qed.

(** A cluster contains exactly the same worlds as itself. *)
Lemma same_set_refl m : same_set m m.
Proof. split; intros i Hi; exact Hi. Qed.

(** Once the two clusters are fixed, a formula starting with [B] or [not] has the same truth value at any initial world. Its outer modal operator supplies the worlds where its body is evaluated. *)
Lemma modal_initial_independent {n} (f : mbnf_formula n) i j mb mn :
  (exists g, f = MBBelief g \/ f = MBNot g) ->
  mbsatb i mb mn f = mbsatb j mb mn f.
Proof. intros. destruct H. destruct H;subst; trivial. Qed.

(** Every formula collected by [formula_modal_occurrences] starts with [B] or [not]. *)
Lemma occurrences_are_modal {n} (f a : mbnf_formula n) :
  In a (formula_modal_occurrences f) ->
  exists g, a = MBBelief g \/ a = MBNot g.
Proof.
  induction f; try easy; intros.
  - simpl in H.
    Search (In ?a (?b++?c)).
    apply in_app_iff in H.
    destruct H as [H|H].
    -- exact (IHf1 H).
    -- exact (IHf2 H).
  - simpl in H.
    Search (In ?a (?b++?c)).
    apply in_app_iff in H.
    destruct H as [H|H].
    -- exact (IHf1 H).
    -- exact (IHf2 H).
  - simpl in H.
    Search (In ?a (?b++?c)).
    apply in_app_iff in H.
    destruct H as [H|H].
    -- exact (IHf1 H).
    -- exact (IHf2 H).
  - simpl in H.
    destruct H as [H|H].
    -- exists f. left. symmetry. assumption.
    -- exact (IHf H).
  - simpl in H.
    destruct H as [H|H].
    -- exists f. right. symmetry. assumption.
    -- exact (IHf H).
Qed.

(** The same holds for the list collected from a whole theory. Its entries therefore have truth values independent of the initial world. *)
Lemma theory_atom_modal {n} (t : mbnf_theory n) a :
  In a (theory_modal_atoms t) -> exists g, a = MBBelief g \/ a = MBNot g.
Proof.
  intros.
  unfold theory_modal_atoms in H.
  rewrite in_flat_map in H.
  repeat destruct H.
  specialize (occurrences_are_modal x a H0). trivial.
Qed.

(** Read the theory's modal truth values from the given clusters. We use the empty list as a placeholder for the initial world, since the collected modal formulas ignore it. *)
Definition partition_induced {n} (t : mbnf_theory n) mb mn :=
  induced_modal_partition (theory_modal_atoms t) [] mb mn.

(** For every modal formula recorded by the theory, membership in the induced partition gives its actual truth value at any initial world. *)
Lemma induced_mem {n} (t : mbnf_theory n) a i mb mn :
  In a (theory_modal_atoms t) ->
  modal_mem a (partition_induced t mb mn) = mbsatb i mb mn a.
Proof.
  intros.
  unfold partition_induced.
  rewrite modal_mem_induced.
  2: exact H.
  apply modal_initial_independent.
  apply theory_atom_modal in H.
  exact H.
Qed.

(** Every partition obtained from a pair of clusters occurs in our enumeration. In particular, the search includes the modal truth values of every model. *)
Lemma induced_listed {n} (t : mbnf_theory n) mb mn :
  In (partition_induced t mb mn) (rosati_partitions t).
Proof. apply filter_in_powerset. Qed.

(** We call a partition accurate when each of its guesses agrees with the actual truth of the relevant formula, at every initial world, for the supplied clusters. *)
Definition accurate_partition {n} (atoms p : list (mbnf_formula n)) mb mn :=
  forall a, In a atoms -> forall i, modal_mem a p = mbsatb i mb mn a.

(** If a partition is accurate for all modal occurrences of a formula, reduction preserves that formula's truth value. This is the result that lets us replace modal evaluation with propositional evaluation after checking the guess. *)
Lemma reduct_accurate {n} (f : mbnf_formula n) p mb mn :
  accurate_partition (formula_modal_occurrences f) p mb mn -> forall i,
  mbsatb i [] [] (mb_objective_reduct p f) = mbsatb i mb mn f.
Proof.
  induction f; intros; try easy.
  - simpl.
    rewrite IHf1, IHf2; try trivial.
    1,2: unfold accurate_partition.
    1,2: intros.
    1,2: unfold accurate_partition in H; simpl in H.
    1,2: specialize (H a).
    1,2: rewrite in_app_iff in H.
    1,2: apply H.
    1: right.
    2: left.
    1,2: assumption.
  - simpl.
    rewrite IHf1, IHf2; try trivial.
    1,2: unfold accurate_partition.
    1,2: intros.
    1,2: unfold accurate_partition in H; simpl in H.
    1,2: specialize (H a).
    1,2: rewrite in_app_iff in H.
    1,2: apply H.
    1: right.
    2: left.
    1,2: assumption.
  - simpl.
    rewrite IHf1, IHf2; try trivial.
    1,2: unfold accurate_partition.
    1,2: intros.
    1,2: unfold accurate_partition in H; simpl in H.
    1,2: specialize (H a).
    1,2: rewrite in_app_iff in H.
    1,2: apply H.
    1: right.
    2: left.
    1,2: assumption.
  - simpl. rewrite <- IHf; trivial.
  - simpl in *.
    rewrite (H (MBBelief f) (or_introl eq_refl) i).
    cbn [mbsatb].
    destruct (forallb (fun j => mbsatb j mb mn f) mb); reflexivity.
  - simpl in *.
    rewrite (H (MBNot f) (or_introl eq_refl) i).
    cbn [mbsatb].
    destruct (existsb (fun j => negb (mbsatb j mb mn f)) mn); reflexivity.
Qed.

(** Suppose we guess [B F] true. Every belief world must then satisfy [F], so we add its reduct as a constraint on those worlds. Other entries contribute true here. False beliefs and [not] formulas will be dealt with by the accuracy check. *)
Definition base_component {n} p (a : mbnf_formula n) : mbnf_formula n :=
  match a with
  | MBBelief f => if modal_mem a p then mb_objective_reduct p f else mb_true
  | _ => mb_true
  end.

(** We call the conjunction of those constraints the objective base. It describes which worlds are compatible with the beliefs guessed true. We still need accuracy and minimal-belief checks before accepting its worlds as a model. *)
Definition objective_base {n} (t : mbnf_theory n) p : mbnf_formula n :=
  fold_right MBAnd mb_true (map (base_component p) (theory_modal_atoms t)).

(** Take every valuation satisfying the objective base. These are all the worlds compatible with its constraints. *)
Definition base_worlds {n} (t : mbnf_theory n) p :=
  objective_worlds (objective_base t p).

(** A world satisfies the base if and only if it satisfies the reduced body of every theory belief guessed true. *)
Lemma objective_base_spec {n} (t : mbnf_theory n) p i :
  mbsatb i [] [] (objective_base t p) = true <->
  forall f, In (MBBelief f) (theory_modal_atoms t) ->
    modal_mem (MBBelief f) p = true ->
    mbsatb i [] [] (mb_objective_reduct p f) = true.
Proof.
  unfold objective_base.
  generalize (theory_modal_atoms t). intros atoms.
  induction atoms as [|a atoms IH].
  - cbn [map fold_right mbsatb mb_true].
    split; [intros _ f []|intros _; reflexivity].
  - cbn [map fold_right mbsatb]. rewrite andb_true_iff, IH.
    split.
    + intros [Ha Htail] f [Heq|Hf] Hp.
      * subst a. unfold base_component in Ha. now rewrite Hp in Ha.
      * now apply Htail.
    + intros H. split.
      * destruct a; cbn [base_component mbsatb mb_true]; try reflexivity.
        destruct (modal_mem (MBBelief a) p) eqn:Ha; [|reflexivity].
        apply H; [now left|exact Ha].
      * intros f Hf. apply H. now right.
Qed.

(** Every modal occurrence of an axiom also belongs to the theory's modal list. *)
Lemma theory_occurs {n} (t : mbnf_theory n) f a :
  In f t -> In a (formula_modal_occurrences f) -> In a (theory_modal_atoms t).
Proof.
  intros Hf Ha. apply in_flat_map. exists f. now split.
Qed.

(** Our collection includes nested occurrences. If [a] is recorded inside [f], then every modal formula recorded inside [a] is also recorded inside [f]. *)
Lemma occurrences_transitive {n} (f a b : mbnf_formula n) :
  In a (formula_modal_occurrences f) ->
  In b (formula_modal_occurrences a) -> In b (formula_modal_occurrences f).
Proof.
  revert a b.
  induction f; intros. try easy.
  - simpl in *. assumption.
  - simpl in *. rewrite in_app_iff in *.
    destruct H as [H|H].
    -- left. exact (IHf1 a b H H0).
    -- right. exact (IHf2 a b H H0).
  - simpl in *. rewrite in_app_iff in *.
    destruct H as [H|H].
    -- left. exact (IHf1 a b H H0).
    -- right. exact (IHf2 a b H H0).
  - simpl in *. rewrite in_app_iff in *.
    destruct H as [H|H].
    -- left. exact (IHf1 a b H H0).
    -- right. exact (IHf2 a b H H0).
  - simpl in *.
    exact (IHf a b H H0).
  - simpl in *.
    destruct H as [H|H].
    -- subst. exact H0.
    -- right. exact (IHf a b H H0).
  - simpl in *.
    destruct H as [H|H].
    -- subst. exact H0.
    -- right. exact (IHf a b H H0).
Qed.

(** This also holds for the list collected from the whole theory: it contains the nested modal occurrences of each of its entries. *)
Lemma theory_atom_descendant {n} (t : mbnf_theory n) a b :
  In a (theory_modal_atoms t) -> In b (formula_modal_occurrences a) ->
  In b (theory_modal_atoms t).
Proof.
  intros Ha Hb. apply in_flat_map in Ha as [f [Hf Ha]].
  apply theory_occurs with (f:=f); [exact Hf|].
  now apply occurrences_transitive with (a:=a).
Qed.

(** In particular, when the list contains [B F], it also contains every modal occurrence inside [F]. *)
Lemma body_occurs {n} (t : mbnf_theory n) f a :
  In (MBBelief f) (theory_modal_atoms t) ->
  In a (formula_modal_occurrences f) -> In a (theory_modal_atoms t).
Proof.
  intros Hf Ha. apply theory_atom_descendant with (a:=MBBelief f);
    [exact Hf|now right].
Qed.

(** Start with a canonical belief cluster and read its modal values. Every world of that cluster satisfies the resulting base. Taking all worlds of the base can therefore only enlarge the original cluster. *)
Lemma base_contains_candidate {n} (t : mbnf_theory n) mb mn :
  canonical_cluster n mb ->
  subset mb (base_worlds t (partition_induced t mb mn)).
Proof.
  intros Hcan i Hi. apply objective_worlds_spec. split.
  - now apply canonical_world with (m:=mb).
  - apply objective_base_spec. intros f Hf Hp.
    rewrite (induced_mem t (MBBelief f) i mb mn Hf) in Hp.
    apply forallb_forall with (x:=i) in Hp; [|exact Hi].
    rewrite reduct_accurate with (mb:=mb) (mn:=mn); [exact Hp|].
    intros a Ha j. apply induced_mem. now apply body_occurs with (f:=f).
Qed.

(** We now prove that this enlargement preserves the truth of any formula whose modal occurrences are all recorded by the theory. Throughout the comparison, the assumption cluster stays fixed. This is the main step behind replacing a cluster with the worlds of its base. *)
Lemma expand_to_base {n} (t : mbnf_theory n) mb mn :
  canonical_cluster n mb ->
  forall f, (forall a, In a (formula_modal_occurrences f) ->
    In a (theory_modal_atoms t)) -> forall i,
  mbsatb i (base_worlds t (partition_induced t mb mn)) mn f =
  mbsatb i mb mn f.
Proof.
  intros Hcan f. induction f; intros Hocc i; cbn [mbsatb]; try reflexivity.
  - rewrite IHf1, IHf2; try reflexivity;
      intros a Ha; apply Hocc; apply in_app_iff; auto.
  - rewrite IHf1, IHf2; try reflexivity;
      intros a Ha; apply Hocc; apply in_app_iff; auto.
  - rewrite IHf1, IHf2; try reflexivity;
      intros a Ha; apply Hocc; apply in_app_iff; auto.
  - rewrite IHf; [reflexivity|exact Hocc].
  - specialize (IHf (fun a Ha => Hocc a (or_intror Ha))).
    destruct (forallb (fun j => mbsatb j mb mn f) mb) eqn:Hbelief.
    -- apply forallb_forall. intros j Hj. rewrite IHf.
      apply objective_worlds_spec in Hj as [_ Hj].
      apply objective_base_spec with (f:=f) in Hj.
      --- rewrite reduct_accurate with (mb:=mb) (mn:=mn) in Hj; [exact Hj|].
        intros a Ha k. apply induced_mem. apply Hocc. now right.
      --- apply Hocc. now left.
      --- rewrite (induced_mem t (MBBelief f) i mb mn (Hocc _ (or_introl eq_refl))).
        exact Hbelief.
    -- apply forallb_false_exists in Hbelief as [j [Hj Hfalse]].
      apply forallb_false_exists. exists j. split.
      --- now apply base_contains_candidate with (mb:=mb).
      --- now rewrite IHf.
  - apply existsb_ext_eq. intros j Hj.
    rewrite IHf; [reflexivity|]. intros a Ha. apply Hocc. now right.
Qed.

(** After enlarging the belief cluster to the worlds of its induced base, the original partition is still accurate on the theory's modal formulas. The assumptions remain fixed. *)
Lemma induced_base_accurate {n} (t : mbnf_theory n) mb mn :
  canonical_cluster n mb ->
  accurate_partition (theory_modal_atoms t) (partition_induced t mb mn)
    (base_worlds t (partition_induced t mb mn)) mn.
Proof.
  intros.
  unfold accurate_partition.
  intros.
  rewrite (induced_mem t a i mb mn H0).
  pose (expand_to_base t mb mn H a).
  symmetry. apply e.
  intros.
  apply (theory_atom_descendant t a a0 H0 H1).
Qed.

(** Check whether the partition agrees with the modal truth values induced by the supplied belief and assumption clusters. *)
Definition partition_atb {n} (t : mbnf_theory n) p mb mn :=
  partition_equivb (theory_modal_atoms t) p (partition_induced t mb mn).

(** The boolean agreement check returns true exactly when the partition is accurate for those clusters. *)
Lemma partition_atb_spec {n} (t : mbnf_theory n) p mb mn :
  partition_atb t p mb mn = true <->
  accurate_partition (theory_modal_atoms t) p mb mn.
Proof.
  unfold partition_atb.
  rewrite partition_equivb_spec.
  split; intros.
  - unfold accurate_partition. intros.
    specialize (H a H0).
    pose (induced_mem t a i mb mn H0) as Hnew.
    rewrite <- Hnew.
    exact H.
  - unfold accurate_partition in H.
    specialize (H f H0 ([]:valuation)).
    pose (induced_mem t f).
    specialize (e ([]:valuation) mb mn H0).
    rewrite <- H in e.
    symmetry. exact e.
Qed.

(** A partition read from a structure agrees with that structure. This follows directly from how we obtained it. *)
Lemma induced_accurate {n} (t : mbnf_theory n) mb mn :
  accurate_partition (theory_modal_atoms t) (partition_induced t mb mn) mb mn.
Proof.
  intros a Ha i. apply induced_mem. exact Ha.
Qed.

(** Evaluate every reduced axiom at the chosen initial world. These are propositional checks using the guessed modal values. To relate them to the original theory, we still need accuracy. *)
Definition reduct_theory_satb {n} i (t : mbnf_theory n) p :=
  forallb (fun f => mbsatb i [] [] (mb_objective_reduct p f)) t.

(** With an accurate partition, checking the reduced theory gives the same answer as checking the original theory in the supplied structure. *)
Lemma reduct_theory_accurate {n} i (t : mbnf_theory n) p mb mn :
  accurate_partition (theory_modal_atoms t) p mb mn ->
  reduct_theory_satb i t p = mb_theory_sat_atb i mb mn t.
Proof.
  intros.
  unfold reduct_theory_satb, mb_theory_sat_atb.
  apply forallb_ext_eq.
  intros.
  apply reduct_accurate.
  unfold accurate_partition in *.
  intros.
  apply H.
  exact (theory_occurs t x a H0 H1).
Qed.
Arguments reduct_theory_accurate {n} i t {p mb mn} _.

(** Here is why objective bases are useful. A model's belief cluster contains exactly the worlds satisfying its induced base. We already know that enlarging to the base preserves the theory. If that enlargement added worlds, it would contradict the model's minimal-belief condition. *)
Lemma model_is_its_base {n} (t : mbnf_theory n) i m :
  MBNFModel t i m -> same_set m (base_worlds t (partition_induced t m m)).
Proof.
  intros.
  unfold MBNFModel in H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  unfold same_set.
  split.
  - apply base_contains_candidate. exact H0.
  - unfold subset. intros.
    destruct (subsetb (base_worlds t (partition_induced t m m)) m) eqn:boh.
    -- apply subsetb_spec in boh.
       unfold subset in boh.
       exact (boh x H4).
    -- exfalso.
       destruct H1.
       apply H3 with (larger:=base_worlds t (partition_induced t m m)) (j:=i).
      --- apply objective_worlds_canonical.
      --- split; [now apply base_contains_candidate|].
        intros Hsub. apply subsetb_spec in Hsub. congruence.
      --- assumption.
      --- intros f Hf. unfold MBSat.
        rewrite expand_to_base; [now apply H2|exact H0|].
        intros a Ha. now apply theory_occurs with (f:=f).
Qed.
Arguments model_is_its_base {n} t {i m} _.

(** Replacing the smaller cluster with a list of the same worlds preserves strict containment in another cluster. *)
Lemma proper_subset_left_ext m r s :
  same_set m r -> (proper_subset m s <-> proper_subset r s).
Proof.
  unfold proper_subset, same_set, subset. firstorder.
Qed.
Arguments proper_subset_left_ext {m r s} _.

(** We can replace a model's belief cluster with a canonical list of the same worlds. The model conditions still hold: truth, nonemptiness, and the comparison with larger clusters all depend on the represented worlds. *)
Lemma model_cluster_ext {n} (t : mbnf_theory n) i m r :
  same_set m r -> canonical_cluster n r -> MBNFModel t i m -> MBNFModel t i r.
Proof.
  intros Heq Hr Hmodel.
  unfold MBNFModel in Hmodel.
  destruct Hmodel as [Hi Hmodel].
  destruct Hmodel as [Hm Hmodel].
  destruct Hmodel as [Hne Hmodel].
  destruct Hmodel as [Hsat Hmax].
  unfold MBNFModel.
  split.
  - exact Hi.
  - split.
    -- exact Hr.
    -- split.
       --- destruct Hne as [w Hw].
           exists w.
           unfold same_set in Heq.
           destruct Heq as [Hmr Hrm].
           apply Hmr. exact Hw.
       --- split.
           ---- unfold MBTheorySatAt in *.
                intros f Hf.
                unfold MBSat in *.
                rewrite <- (mbsatb_extensional f i Heq Heq).
                apply Hsat. exact Hf.
           ---- intros larger Hlarger Hproper j Hj Hjsat.
                apply Hmax with (larger:=larger) (j:=j).
                ----- exact Hlarger.
                ----- rewrite (proper_subset_left_ext Heq). exact Hproper.
                ----- exact Hj.
                ----- unfold MBTheorySatAt in *.
                      intros f Hf.
                      unfold MBSat in *.
                      rewrite (mbsatb_extensional f j (same_set_refl larger) Heq).
                      apply Hjsat. exact Hf.
Qed.

(** If two partitions agree on every modal occurrence of a formula, they produce the same reduct of that formula. *)
Lemma reduct_partition_ext {n} (f : mbnf_formula n) p r :
  (forall a, In a (formula_modal_occurrences f) -> modal_mem a p = modal_mem a r) ->
  mb_objective_reduct p f = mb_objective_reduct r f.
Proof.
  induction f; intros H; simpl in *; try reflexivity.
  - f_equal.
    -- apply IHf1. intros a Ha. apply H. rewrite in_app_iff. left. exact Ha.
    -- apply IHf2. intros a Ha. apply H. rewrite in_app_iff. right. exact Ha.
  - f_equal.
    -- apply IHf1. intros a Ha. apply H. rewrite in_app_iff. left. exact Ha.
    -- apply IHf2. intros a Ha. apply H. rewrite in_app_iff. right. exact Ha.
  - f_equal.
    -- apply IHf1. intros a Ha. apply H. rewrite in_app_iff. left. exact Ha.
    -- apply IHf2. intros a Ha. apply H. rewrite in_app_iff. right. exact Ha.
  - f_equal. apply IHf. exact H.
  - rewrite (H (MBBelief f)).
    -- reflexivity.
    -- left. reflexivity.
  - rewrite (H (MBNot f)).
    -- reflexivity.
    -- left. reflexivity.
Qed.

(** Likewise, partitions agreeing on the theory's modal formulas produce the same objective base. *)
Lemma base_partition_ext {n} (t : mbnf_theory n) p r :
  partition_equivb (theory_modal_atoms t) p r = true ->
  objective_base t p = objective_base t r.
Proof.
  intros H.
  rewrite partition_equivb_spec in H.
  unfold objective_base.
  f_equal.
  apply map_ext_in.
  intros a Ha.
  destruct a; simpl; try reflexivity.
  rewrite H.
  - destruct (modal_mem (MBBelief a) r) eqn:boh.
    -- apply reduct_partition_ext.
       intros b Hb. apply H.
       apply body_occurs with (f:=a); assumption.
    -- reflexivity.
  - exact Ha.
Qed.
Arguments base_partition_ext {n} t {p r} _.

(** To reduce a query, read its modal values from the candidate cluster, using that cluster for both beliefs and assumptions. We collect the query's own modal occurrences, including any that are absent from the theory. *)
Definition query_reduct {n} (q : mbnf_formula n) m :=
  mb_objective_reduct (induced_modal_partition (formula_modal_occurrences q) [] m m) q.

(** At every initial world, evaluating this reduced query gives the same answer as evaluating the original query with the candidate supplying both clusters. *)
Lemma query_reduct_correct {n} (q : mbnf_formula n) m i :
  mbsatb i [] [] (query_reduct q m) = mbsatb i m m q.
Proof.
  unfold query_reduct.
  apply reduct_accurate.
  unfold accurate_partition.
  intros a Ha j.
  rewrite modal_mem_induced.
  - apply modal_initial_independent.
    apply occurrences_are_modal with (f:=q). exact Ha.
  - exact Ha.
Qed.

(** *** Figure 1: general partition search

    We now have what we need to write the three checks in Figure 1.

    - Condition (a): does the partition agree with the worlds of its base?
    - Condition (b): is there an initial world satisfying the reduced theory and falsifying the reduced query?
    - Condition (c): does every competing partition fail to give a structure with less belief, while the candidate's assumptions stay fixed?

    The bases are objective formulas. We check implication between them by comparing their finite sets of satisfying worlds with [subsetb]. We also require a nonempty base cluster, as required by the MBNF semantics. *)

(** The first check combines conditions (a) and (b) with nonemptiness. The guess must agree with the base worlds, and some initial world must satisfy the reduced theory while falsifying the reduced query. Condition (c) will deal with minimal belief. *)
Definition rosati_condition_ab {n} (t : mbnf_theory n) (q : mbnf_formula n) p :=
  let w := base_worlds t p in
  nonemptyb w && partition_atb t p w w &&
  existsb (fun i => reduct_theory_satb i t p &&
    negb (mbsatb i [] [] (query_reduct q w))) (all_valuations n).

(** Try every initial world and check whether any of them satisfies the reduced theory. This establishes propositional satisfiability for the guess. Accuracy and minimal belief are checked separately. *)
Definition partition_theory_satb {n} (t : mbnf_theory n) p :=
  existsb (fun i => reduct_theory_satb i t p) (all_valuations n).

(** For condition (c), compare the candidate with every competing guess. A different guess defeats the candidate when its reduced theory is satisfiable, it is accurate with the candidate's assumptions fixed, and its base contains the candidate's base worlds. Reject the candidate if such a competitor exists. *)
Definition rosati_condition_c {n} (t : mbnf_theory n) p :=
  forallb (fun r =>
    partition_equivb (theory_modal_atoms t) p r ||
    negb (partition_theory_satb t r) ||
    negb (partition_atb t r (base_worlds t r) (base_worlds t p)) ||
    negb (subsetb (base_worlds t p) (base_worlds t r)))
    (rosati_partitions t).

(** For a query containing no [not], look for a partition passing all three checks. Returning true means that we found a counterexample. The function also returns false for a query outside this restriction, so we must either prove the query positive or use the wrapper defined later. *)
Definition rosati_general_not_entailsb {n} (t : mbnf_theory n) (q : mbnf_formula n) :=
  mbnf_positiveb q &&
  existsb (fun p => rosati_condition_ab t q p && rosati_condition_c t p)
    (rosati_partitions t).

(** Condition (c) holds exactly when every competitor passing the satisfiability, accuracy, and containment checks gives the same modal assignment as the candidate. *)
Lemma rosati_condition_c_spec {n} (t : mbnf_theory n) p :
  rosati_condition_c t p = true <->
  forall r, In r (rosati_partitions t) ->
    partition_atb t r (base_worlds t r) (base_worlds t p) = true ->
    partition_theory_satb t r = true ->
    subset (base_worlds t p) (base_worlds t r) ->
    partition_equivb (theory_modal_atoms t) p r = true.
Proof.
  unfold rosati_condition_c.
  rewrite forallb_forall.
  split.
  - intros H r Hr Ha Hsat Hsub.
    specialize (H r Hr).
    apply subsetb_spec in Hsub.
    rewrite Ha, Hsat, Hsub in H.
    simpl in H.
    rewrite !orb_false_r in H.
    exact H.
  - intros H r Hr.
    destruct (partition_equivb (theory_modal_atoms t) p r) eqn:Heq; try reflexivity.
    destruct (partition_theory_satb t r) eqn:Hsat; try reflexivity.
    destruct (partition_atb t r (base_worlds t r) (base_worlds t p)) eqn:Ha; try reflexivity.
    destruct (subsetb (base_worlds t p) (base_worlds t r)) eqn:Hsub; try reflexivity.
    apply subsetb_spec in Hsub.
    specialize (H r Hr Ha Hsat Hsub).
    rewrite H in Heq. discriminate Heq.
Qed.

(** We say the base is maximal when no canonical strict enlargement satisfies the theory at any initial world, with assumptions fixed at the base. This is the minimal-belief condition written for the candidate's world set. *)
Definition base_maximal {n} (t : mbnf_theory n) p :=
  forall larger, canonical_cluster n larger ->
    proper_subset (base_worlds t p) larger ->
    forall j, In j (all_valuations n) ->
      ~ MBTheorySatAt j larger (base_worlds t p) t.

(** Passing condition (c) rules out every strict enlargement that could satisfy the theory. Thus the comparison between partitions enforces the required minimal belief. *)
Lemma rosati_c_implies_maximal {n} (t : mbnf_theory n) p :
  rosati_condition_c t p = true -> base_maximal t p.
Proof.
  intros H.
  unfold base_maximal.
  intros larger Hcan Hproper j Hj Hsat.
  destruct Hproper as [Hsub Hstrict].
  apply Hstrict.
  unfold subset.
  intros w Hw.
  unfold base_worlds.
  rewrite (base_partition_ext t (p:=p)
    (r:=partition_induced t larger (base_worlds t p))).
  - apply base_contains_candidate with (mb:=larger); assumption.
  - rewrite rosati_condition_c_spec in H.
    apply H.
    -- apply induced_listed.
    -- apply partition_atb_spec.
       apply induced_base_accurate. exact Hcan.
    -- unfold partition_theory_satb.
       rewrite existsb_exists.
       exists j. split.
       --- exact Hj.
       --- rewrite (reduct_theory_accurate j t (induced_accurate t larger (base_worlds t p))).
           apply mb_theory_sat_atb_spec. exact Hsat.
    -- unfold subset. intros v Hv.
       apply base_contains_candidate with (mb:=larger).
       --- exact Hcan.
       --- apply Hsub. exact Hv.
Qed.

(** We also need the converse. If the candidate is accurate and no strict enlargement satisfies the theory with its assumptions fixed, then condition (c) passes. *)
Lemma maximal_implies_rosati_c {n} (t : mbnf_theory n) p :
  partition_atb t p (base_worlds t p) (base_worlds t p) = true ->
  base_maximal t p -> rosati_condition_c t p = true.
Proof.
  intros Hp Hmax.
  apply rosati_condition_c_spec.
  intros r Hr Ha Hsat Hsub.
  destruct (subsetb (base_worlds t r) (base_worlds t p)) eqn:Hback.
  - apply subsetb_spec in Hback.
    apply partition_atb_spec in Hp, Ha.
    apply partition_equivb_spec.
    intros a Hatom.
    unfold accurate_partition in Hp, Ha.
    specialize (Hp a Hatom ([]:valuation)).
    specialize (Ha a Hatom ([]:valuation)).
    rewrite Hp, Ha.
    apply mbsatb_extensional.
    -- split; assumption.
    -- apply same_set_refl.
  - exfalso.
    unfold partition_theory_satb in Hsat.
    rewrite existsb_exists in Hsat.
    destruct Hsat as [j [Hj Hsat]].
    unfold base_maximal in Hmax.
    apply Hmax with (larger:=base_worlds t r) (j:=j).
    -- apply objective_worlds_canonical.
    -- unfold proper_subset. split.
       --- exact Hsub.
       --- intro Hreverse.
           apply subsetb_spec in Hreverse.
           rewrite Hreverse in Hback. discriminate Hback.
    -- exact Hj.
    -- apply mb_theory_sat_atb_spec.
       apply partition_atb_spec in Ha.
       rewrite <- (reduct_theory_accurate j t Ha).
       exact Hsat.
Qed.

(** Conditions (a) and (b) pass exactly when the base is nonempty, the guess is accurate, and some initial world satisfies the original theory while falsifying the original query. This gives a possible counterexample; we still have to check minimal belief. *)
Lemma rosati_ab_spec {n} (t : mbnf_theory n) q p :
  rosati_condition_ab t q p = true <->
  (exists w, In w (base_worlds t p)) /\
  accurate_partition (theory_modal_atoms t) p (base_worlds t p) (base_worlds t p) /\
  exists i, In i (all_valuations n) /\
    MBTheorySatAt i (base_worlds t p) (base_worlds t p) t /\
    mbsatb i (base_worlds t p) (base_worlds t p) q = false.
Proof.
  unfold rosati_condition_ab.
  rewrite !andb_true_iff.
  rewrite nonemptyb_spec, partition_atb_spec, existsb_exists.
  split.
  - intros H.
    destruct H as [[Hne Ha] [i [Hi Htest]]].
    rewrite andb_true_iff in Htest.
    destruct Htest as [Ht Hq].
    rewrite (reduct_theory_accurate i t Ha) in Ht.
    apply mb_theory_sat_atb_spec in Ht.
    rewrite query_reduct_correct, negb_true_iff in Hq.
    split.
    -- exact Hne.
    -- split.
       --- exact Ha.
       --- exists i. repeat split; assumption.
  - intros H.
    destruct H as [Hne [Ha [i [Hi [Ht Hq]]]]].
    split.
    -- split; assumption.
    -- exists i. split.
       --- exact Hi.
       --- rewrite andb_true_iff.
           rewrite (reduct_theory_accurate i t Ha), mb_theory_sat_atb_spec.
           rewrite query_reduct_correct, negb_true_iff.
           split; assumption.
Qed.

(** We can now prove Figure 1 correct. For a query containing no [not], the procedure returns true if and only if the theory fails to entail the query. Thus every returned counterexample is valid, and every failure of entailment can be found. The theory itself may contain nested modal operators without this restriction. *)
Theorem rosati_general_not_entailsb_correct {n} (t : mbnf_theory n) q :
  mbnf_positiveb q = true ->
  (rosati_general_not_entailsb t q = true <-> ~ MBNFEntails t q).
Proof.
  intros Hpositive.
  unfold rosati_general_not_entailsb.
  rewrite Hpositive. simpl.
  rewrite existsb_exists.
  split.
  - intros H Hentails.
    destruct H as [p [Hp Hcheck]].
    rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [Hab Hc].
    apply rosati_ab_spec in Hab.
    destruct Hab as [Hne [Ha [i [Hi [Ht Hq]]]]].
    apply (eq_true_false_abs (mbsatb i (base_worlds t p) (base_worlds t p) q)).
    -- apply Hentails.
       unfold MBNFModel.
       repeat split; try assumption.
       --- apply objective_worlds_canonical.
       --- apply rosati_c_implies_maximal. exact Hc.
    -- exact Hq.
  - intros Hnot.
    destruct (mbnf_exhaustive_entailsb t q) eqn:Hdirect.
    -- rewrite mbnf_exhaustive_entailsb_correct in Hdirect.
       apply Hnot in Hdirect. contradiction.
    -- unfold mbnf_exhaustive_entailsb in Hdirect.
       rewrite negb_false_iff, existsb_exists in Hdirect.
       destruct Hdirect as [[i m] [Hpair Hbad]].
       unfold mbnf_bad_pairb in Hbad.
       rewrite andb_true_iff in Hbad.
       destruct Hbad as [Hm Hq].
       rewrite mbnf_modelb_spec in Hm.
       rewrite negb_true_iff in Hq.
       pose (model_is_its_base t Hm) as Heq.
       pose (@model_cluster_ext n t i m
         (base_worlds t (partition_induced t m m)) Heq
         (objective_worlds_canonical _) Hm) as Hbase.
       exists (partition_induced t m m).
       split.
       --- apply induced_listed.
       --- rewrite andb_true_iff. split.
           ---- apply rosati_ab_spec.
                destruct Hbase as [Hi [Hcan [Hne [Ht Hmax]]]].
                split.
                ----- exact Hne.
                ----- split.
                      + unfold accurate_partition. intros a Ha j.
                        rewrite (induced_mem t a j m m Ha).
                        apply mbsatb_extensional; exact Heq.
                      + exists i. split.
                        * exact Hi.
                        * split.
                          ++ exact Ht.
                          ++ rewrite <- (mbsatb_extensional q i Heq Heq). exact Hq.
           ---- apply maximal_implies_rosati_c.
                ----- apply partition_atb_spec.
                      unfold accurate_partition. intros a Ha j.
                      rewrite (induced_mem t a j m m Ha).
                      apply mbsatb_extensional; exact Heq.
                ----- unfold MBNFModel in Hbase.
                      destruct Hbase as [Hi [Hcan [Hne [Ht Hmax]]]].
                      exact Hmax.
Qed.

(** *** Public entailment interfaces

    Figure 1 requires a query without [not]. We can meet this requirement by rewriting [not F] as [~ B F] wherever it occurs in the query. The two expressions have the same truth value when the belief and assumption clusters coincide. Models use equal clusters for evaluating queries, so this rewrite will let us accept arbitrary queries. *)

(** The following function performs the rewrite throughout the query, including inside nested operators. The result contains no [not]. We will prove that it preserves truth when the two clusters coincide; that equality of clusters is needed here. *)
Fixpoint mbnf_positive_query {n} (f : mbnf_formula n) : mbnf_formula n :=
  match f with
  | MBAtom a => MBAtom a
  | MBBot => MBBot
  | MBAnd x y => MBAnd (mbnf_positive_query x) (mbnf_positive_query y)
  | MBOr x y => MBOr (mbnf_positive_query x) (mbnf_positive_query y)
  | MBImp x y => MBImp (mbnf_positive_query x) (mbnf_positive_query y)
  | MBNeg x => MBNeg (mbnf_positive_query x)
  | MBBelief x => MBBelief (mbnf_positive_query x)
  | MBNot x => MBNeg (MBBelief (mbnf_positive_query x))
  end.

(** The rewritten query satisfies Figure 1's restriction: it contains no occurrence of [not]. *)
Lemma mbnf_positive_query_is_positive {n} (f : mbnf_formula n) :
  mbnf_positiveb (mbnf_positive_query f) = true.
Proof.
  induction f; simpl; try reflexivity; try assumption.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
Qed.

(** A useful boolean identity: some entry fails a check if and only if the check fails to hold for every entry. The equality also holds for the empty list. *)
Lemma existsb_negb_forallb {A} (f : A -> bool) xs :
  existsb (fun x => negb (f x)) xs = negb (forallb f xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    rewrite IHxs.
    rewrite Bool.negb_andb.
    reflexivity.
Qed.

(** With equal belief and assumption clusters, the rewritten query and the original have the same truth value. A world falsifying [F] exists exactly when [F] fails to hold at every world, which explains the rewrite of [not]. *)
Lemma mbnf_positive_query_correct {n} (f : mbnf_formula n) :
  forall i m, mbsatb i m m (mbnf_positive_query f) = mbsatb i m m f.
Proof.
  induction f; intros i m; simpl; try reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf1, IHf2. reflexivity.
  - rewrite IHf. reflexivity.
  - apply forallb_ext_eq.
    intros j Hj. apply IHf.
  - rewrite existsb_negb_forallb.
    f_equal.
    apply forallb_ext_eq.
    intros j Hj. apply IHf.
Qed.

(** The theory entails the rewritten query if and only if it entails the original one. Every model uses equal clusters for the query evaluation, so the preceding result applies. *)
Lemma mbnf_positive_query_entailment {n} (t : mbnf_theory n) q :
  MBNFEntails t (mbnf_positive_query q) <-> MBNFEntails t q.
Proof.
  unfold MBNFEntails, MBSat.
  split; intros H i m Hmodel.
  - specialize (H i m Hmodel).
    rewrite mbnf_positive_query_correct in H.
    exact H.
  - rewrite mbnf_positive_query_correct.
    apply H. exact Hmodel.
Qed.

(** We can now accept any MBNF query. Rewrite it, run Figure 1, then negate the result so that true means entailment. *)
Definition rosati_general_entailsb {n} (t : mbnf_theory n) q :=
  negb (rosati_general_not_entailsb t (mbnf_positive_query q)).

(** This is the correctness theorem for the public MBNF solver. It returns true if and only if the theory entails the query. The function handles the positive-query requirement internally. *)
Theorem rosati_general_entailsb_correct {n} (t : mbnf_theory n) q :
  rosati_general_entailsb t q = true <-> MBNFEntails t q.
Proof.
  unfold rosati_general_entailsb.
  rewrite negb_true_iff.
  pose (rosati_general_not_entailsb_correct t (mbnf_positive_query q)
    (mbnf_positive_query_is_positive q)) as Hcorrect.
  rewrite mbnf_positive_query_entailment in Hcorrect.
  rewrite <- mbnf_exhaustive_entailsb_correct in Hcorrect.
  rewrite Bool.not_true_iff_false in Hcorrect.
  rewrite <- mbnf_exhaustive_entailsb_correct.
  rewrite <- Bool.not_true_iff_false.
  rewrite Hcorrect.
  apply Bool.not_false_iff_true.
Qed.


(** Both MBNF solvers always return the same answer for the same theory and query. This follows from their correctness theorems. The amount of work needed to reach that answer can differ. *)
Theorem rosati_general_agrees_with_exhaustive {n} (t : mbnf_theory n) q :
  rosati_general_entailsb t q = mbnf_exhaustive_entailsb t q.
Proof.
  apply Bool.eq_true_iff_eq.
  rewrite rosati_general_entailsb_correct.
  rewrite mbnf_exhaustive_entailsb_correct.
  reflexivity.
Qed.


(** To answer an MKNF query with this solver, translate the formulas to MBNF and wrap the theory and query in [B], as in Chapter 2. *)
Definition rosati_mknf_entailsb {n} (t : theory n) q :=
  rosati_general_entailsb (subjectivize t) (subjectivize_query q).

(** The translated solver is correct for nonempty MKNF entailment. We combine the MBNF correctness theorem with the subjectivization equivalence. *)
Theorem rosati_mknf_entailsb_correct {n} (t : theory n) q :
  rosati_mknf_entailsb t q = true <-> EntailsNonempty t q.
Proof.
  unfold rosati_mknf_entailsb.
  rewrite rosati_general_entailsb_correct.
  rewrite <- subjectivization_entailment.
  reflexivity.
Qed.

(** *** Reusing checked partition catalogues

    The preference checks depend on the theory. If we ask several queries about it, we can compute the accepted partitions once and reuse the list.

    The following lemmas show that this gives the same answers as Figure 1. We will also use conditional branches to stop checking a candidate as soon as one check fails. *)

(** We first write condition (c) with explicit branches. We can skip a competitor if it gives the same assignment, if its reduced theory is unsatisfiable, or if it is inaccurate with the candidate's assumptions. Only the remaining competitors need a containment check. *)
Definition rosati_minimal_partitionb {n} (t : mbnf_theory n) p :=
  let atoms := theory_modal_atoms t in
  let w := base_worlds t p in
  forallb (fun r =>
    if partition_equivb atoms p r then true
    else if partition_theory_satb t r then
      let wr := base_worlds t r in
      if partition_atb t r wr w then
        negb (subsetb w wr)
      else true
    else true) (rosati_partitions t).

(** Writing the checks with branches gives exactly the same answer as the original condition (c). *)
Lemma rosati_minimal_partitionb_eq {n} (t : mbnf_theory n) p :
  rosati_minimal_partitionb t p = rosati_condition_c t p.
Proof.
  unfold rosati_minimal_partitionb, rosati_condition_c.
  apply forallb_ext_eq.
  intros r Hr.
  destruct (partition_equivb (theory_modal_atoms t) p r),
    (partition_theory_satb t r),
    (partition_atb t r (base_worlds t r) (base_worlds t p)); reflexivity.
Qed.

(** Keep a partition when its base is nonempty, its reduced theory is satisfiable, it is accurate, and it passes condition (c). None of these checks uses the query, so we can store their results. *)
Definition rosati_preferred_partitionb {n} (t : mbnf_theory n) p :=
  let w := base_worlds t p in
  if nonemptyb w then
    if partition_theory_satb t p then
      if partition_atb t p w w then rosati_minimal_partitionb t p else false
    else false
  else false.

(** The function accepts a partition if and only if all four checks pass. *)
Lemma rosati_preferred_partitionb_spec {n} (t : mbnf_theory n) p :
  rosati_preferred_partitionb t p = true <->
  nonemptyb (base_worlds t p) = true /\
  partition_theory_satb t p = true /\
  partition_atb t p (base_worlds t p) (base_worlds t p) = true /\
  rosati_condition_c t p = true.
Proof.
  unfold rosati_preferred_partitionb.
  rewrite rosati_minimal_partitionb_eq.
  split.
  - intros H.
    destruct (nonemptyb (base_worlds t p)) eqn:Hne; try discriminate.
    destruct (partition_theory_satb t p) eqn:Hsat; try discriminate.
    destruct (partition_atb t p (base_worlds t p) (base_worlds t p)) eqn:Ha; try discriminate.
    repeat split; try reflexivity.
    exact H.
  - intros H.
    destruct H as [Hne [Hsat [Ha Hc]]].
    rewrite Hne, Hsat, Ha.
    exact Hc.
Qed.

(** Given the complete list of accepted partitions, answering a query only needs the search for an initial world falsifying it. We require an equation proving that the list is exactly the filtered enumeration. The following theorem then gives the same answer as the original solver. *)
Theorem rosati_general_entailsb_from_partition_catalogue {n} (t : mbnf_theory n) models :
  filter (rosati_preferred_partitionb t) (rosati_partitions t) = models ->
  forall q, rosati_general_entailsb t q =
    negb (existsb (fun p =>
      let reduced_query := query_reduct (mbnf_positive_query q) (base_worlds t p) in
      existsb (fun i => reduct_theory_satb i t p &&
        negb (mbsatb i [] [] reduced_query)) (all_valuations n)) models).
Proof.
  intros Hmodels q.
  unfold rosati_general_entailsb, rosati_general_not_entailsb.
  rewrite mbnf_positive_query_is_positive. simpl.
  f_equal.
  apply Bool.eq_true_iff_eq.
  rewrite <- Hmodels, !existsb_exists.
  split.
  - intros H.
    destruct H as [p [Hp Hcheck]].
    rewrite andb_true_iff in Hcheck.
    destruct Hcheck as [Hab Hc].
    unfold rosati_condition_ab in Hab.
    rewrite !andb_true_iff in Hab.
    destruct Hab as [[Hne Ha] Hquery].
    exists p. split.
    -- apply filter_In. split.
       --- exact Hp.
       --- apply rosati_preferred_partitionb_spec. split.
           ---- exact Hne.
           ---- split.
                ----- unfold partition_theory_satb.
                      rewrite existsb_exists in *.
                      destruct Hquery as [i [Hi Htest]].
                      rewrite andb_true_iff in Htest.
                      destruct Htest as [Hsat Hfalse].
                      exists i. split; assumption.
                ----- split; assumption.
    -- exact Hquery.
  - intros H.
    destruct H as [p [Hp Hquery]].
    rewrite filter_In in Hp.
    destruct Hp as [Hp Hpreferred].
    apply rosati_preferred_partitionb_spec in Hpreferred.
    destruct Hpreferred as [Hne [Hsat [Ha Hc]]].
    exists p. split.
    -- exact Hp.
    -- rewrite andb_true_iff. split.
       --- unfold rosati_condition_ab.
           rewrite Hne, Ha. exact Hquery.
       --- exact Hc.
Qed.

Arguments rosati_general_entailsb_from_partition_catalogue {n t models} _ q.

(** An accepted partition gives an MBNF model at any valid initial world satisfying its reduced theory. We can use this to prove that a theory has a model through a partition calculation. *)
Theorem rosati_preferred_partition_model {n} (t : mbnf_theory n) p i :
  rosati_preferred_partitionb t p = true -> In i (all_valuations n) ->
  reduct_theory_satb i t p = true -> MBNFModel t i (base_worlds t p).
Proof.
  intros Hpreferred Hi Hsat.
  apply rosati_preferred_partitionb_spec in Hpreferred.
  destruct Hpreferred as [Hne [Hsome [Ha Hc]]].
  rewrite nonemptyb_spec in Hne.
  apply partition_atb_spec in Ha.
  unfold MBNFModel.
  split.
  - exact Hi.
  - split.
    -- apply objective_worlds_canonical.
    -- split.
       --- exact Hne.
       --- split.
           ---- apply mb_theory_sat_atb_spec.
                rewrite <- (reduct_theory_accurate i t Ha). exact Hsat.
           ---- apply rosati_c_implies_maximal. exact Hc.
Qed.

(** *** Enumerating distinct modal choices

    The same modal formula can occur in several axioms. Equal occurrences must have the same truth value, so choosing that value once is enough. We will remove repeated formulas before listing partitions and prove that this preserves the answers. *)

(** Replacing either partition in a comparison with an equivalent one leaves the comparison unchanged. Here, equivalent means agreeing on the supplied modal formulas. *)
Lemma partition_equivb_ext {n} (atoms p p' r r' : modal_partition n) :
  partition_equivb atoms p p' = true ->
  partition_equivb atoms r r' = true ->
  partition_equivb atoms p r = partition_equivb atoms p' r'.
Proof.
  intros Hp Hr.
  rewrite partition_equivb_spec in Hp, Hr.
  unfold partition_equivb.
  apply forallb_ext_eq.
  intros a Ha.
  rewrite (Hp a Ha), (Hr a Ha).
  reflexivity.
Qed.
Arguments partition_equivb_ext {n atoms p p' r r'} _ _.

(** Suppose [pool] contains exactly the relevant modal formulas. For any guess, some subset of [pool] gives the same values on those formulas. The pool's order and repetitions do not prevent us from representing a guess. *)
Lemma partition_choices_cover {n} (atoms pool p : modal_partition n) :
  (forall a, In a pool <-> In a atoms) ->
  exists r, In r (powerset pool) /\ partition_equivb atoms p r = true.
Proof.
  intros Hpool.
  exists (filter (fun a => modal_mem a p) pool).
  split.
  - apply filter_in_powerset.
  - apply partition_equivb_spec.
    intros a Ha.
    apply Bool.eq_true_iff_eq.
    rewrite !modal_mem_spec, filter_In, modal_mem_spec, Hpool.
    split.
    -- intros Hp. split; assumption.
    -- intros H. destruct H as [Hin Hp]. exact Hp.
Qed.

(** Remove repeated modal formulas, then list every subset. We now make one choice for each distinct formula. *)
Definition rosati_distinct_partitions {n} (t : mbnf_theory n) :=
  powerset (nodup mbnf_formula_eq_dec (theory_modal_atoms t)).

(** Every guess has an equivalent representative in this smaller enumeration. Removing repetitions therefore keeps every possible assignment of modal truth values. *)
Lemma rosati_distinct_partitions_cover {n} (t : mbnf_theory n) p :
  exists r, In r (rosati_distinct_partitions t) /\
    partition_equivb (theory_modal_atoms t) p r = true.
Proof.
  unfold rosati_distinct_partitions.
  apply partition_choices_cover.
  intros a.
  apply nodup_In.
Qed.

(** The original enumeration also represents every guess on the theory's modal formulas. Extra entries in the supplied guess do not affect this result. *)
Lemma rosati_partitions_cover {n} (t : mbnf_theory n) p :
  exists r, In r (rosati_partitions t) /\
    partition_equivb (theory_modal_atoms t) p r = true.
Proof.
  unfold rosati_partitions.
  apply partition_choices_cover.
  intros a.
  reflexivity.
Qed.

(** Equivalent guesses give the same result when we check accuracy against fixed belief and assumption clusters. *)
Lemma partition_atb_ext {n} (t : mbnf_theory n) p r mb mn :
  partition_equivb (theory_modal_atoms t) p r = true ->
  partition_atb t p mb mn = partition_atb t r mb mn.
Proof.
  intros Heq.
  unfold partition_atb.
  apply partition_equivb_ext.
  - exact Heq.
  - apply partition_equivb_spec.
    intros a Ha. reflexivity.
Qed.
Arguments partition_atb_ext {n} t {p r} mb mn _.

(** Equivalent guesses give the same reduced-theory truth value at each initial world. *)
Lemma reduct_theory_satb_ext {n} (t : mbnf_theory n) p r i :
  partition_equivb (theory_modal_atoms t) p r = true ->
  reduct_theory_satb i t p = reduct_theory_satb i t r.
Proof.
  intros Heq.
  rewrite partition_equivb_spec in Heq.
  unfold reduct_theory_satb.
  apply forallb_ext_eq.
  intros f Hf.
  rewrite (reduct_partition_ext f p r).
  - reflexivity.
  - intros a Ha. apply Heq.
    apply theory_occurs with (f:=f); assumption.
Qed.
Arguments reduct_theory_satb_ext {n} t {p r} i _.

(** It follows that the reduced theories of equivalent guesses have the same satisfiability result. *)
Lemma partition_theory_satb_ext {n} (t : mbnf_theory n) p r :
  partition_equivb (theory_modal_atoms t) p r = true ->
  partition_theory_satb t p = partition_theory_satb t r.
Proof.
  intros Heq.
  unfold partition_theory_satb.
  apply existsb_ext_eq.
  intros i Hi.
  apply reduct_theory_satb_ext. exact Heq.
Qed.
Arguments partition_theory_satb_ext {n} t {p r} _.

(** This function checks whether we can dismiss a competitor in condition (c). We can do so if its guess is equivalent, its reduced theory is unsatisfiable, it is inaccurate with the candidate's assumptions, or its base fails to contain the candidate's base. Returning false means that the competitor defeats the candidate. *)
Definition rosati_competitionb {n} (t : mbnf_theory n) p r :=
  partition_equivb (theory_modal_atoms t) p r ||
  negb (partition_theory_satb t r) ||
  negb (partition_atb t r (base_worlds t r) (base_worlds t p)) ||
  negb (subsetb (base_worlds t p) (base_worlds t r)).

(** Replacing the candidate and its competitor with equivalent guesses preserves this comparison result. *)
Lemma rosati_competitionb_ext {n} (t : mbnf_theory n) p p' r r' :
  partition_equivb (theory_modal_atoms t) p p' = true ->
  partition_equivb (theory_modal_atoms t) r r' = true ->
  rosati_competitionb t p r = rosati_competitionb t p' r'.
Proof.
  intros Hp Hr.
  unfold rosati_competitionb.
  rewrite (partition_equivb_ext Hp Hr).
  rewrite (partition_theory_satb_ext t Hr).
  unfold base_worlds.
  rewrite (base_partition_ext t Hp), (base_partition_ext t Hr).
  rewrite (partition_atb_ext t _ _ Hr).
  reflexivity.
Qed.
Arguments rosati_competitionb_ext {n} t {p p' r r'} _ _.

(** Checking one representative of every competitor guess gives the same result as checking the original list. Repeated representatives only add work. *)
Lemma rosati_distinct_condition_c {n} (t : mbnf_theory n) p :
  forallb (rosati_competitionb t p) (rosati_distinct_partitions t) =
    rosati_condition_c t p.
Proof.
  change (forallb (rosati_competitionb t p) (rosati_distinct_partitions t) =
    forallb (rosati_competitionb t p) (rosati_partitions t)).
  apply Bool.eq_true_iff_eq.
  rewrite !forallb_forall.
  split.
  - intros H r Hr.
    destruct (rosati_distinct_partitions_cover t r) as [s [Hs Heq]].
    rewrite (rosati_competitionb_ext t (p:=p) (p':=p) (r:=r) (r':=s)).
    -- apply H. exact Hs.
    -- apply partition_equivb_spec. intros a Ha. reflexivity.
    -- exact Heq.
  - intros H r Hr.
    destruct (rosati_partitions_cover t r) as [s [Hs Heq]].
    rewrite (rosati_competitionb_ext t (p:=p) (p':=p) (r:=r) (r':=s)).
    -- apply H. exact Hs.
    -- apply partition_equivb_spec. intros a Ha. reflexivity.
    -- exact Heq.
Qed.

(** Equivalent guesses also give the same result for the full acceptance check. We may therefore store the representative supplied by our enumeration. *)
Lemma rosati_preferred_partitionb_ext {n} (t : mbnf_theory n) p r :
  partition_equivb (theory_modal_atoms t) p r = true ->
  rosati_preferred_partitionb t p = rosati_preferred_partitionb t r.
Proof.
  intros Heq.
  unfold rosati_preferred_partitionb.
  rewrite !rosati_minimal_partitionb_eq.
  rewrite (partition_theory_satb_ext t Heq), (partition_atb_ext t _ _ Heq).
  unfold base_worlds.
  rewrite (base_partition_ext t Heq).
  destruct (nonemptyb (objective_worlds (objective_base t r))),
    (partition_theory_satb t r),
    (partition_atb t r (objective_worlds (objective_base t r))
      (objective_worlds (objective_base t r))); try reflexivity.
  apply forallb_ext_eq.
  intros s Hs.
  apply rosati_competitionb_ext.
  - exact Heq.
  - apply partition_equivb_spec. intros a Ha. reflexivity.
Qed.
Arguments rosati_preferred_partitionb_ext {n} t {p r} _.

(** There is a quick check we can do before trying valuations. If a modal formula is itself an axiom, guessing it false makes the reduced theory unsatisfiable. We reject such guesses immediately and leave the other axioms to the usual checks. *)
Definition rosati_modal_factsb {n} (t : mbnf_theory n) p :=
  forallb (fun f => match f with
    | MBBelief _ | MBNot _ => modal_mem f p
    | _ => true
    end) t.

(** Every world satisfying the reduced theory passes this preliminary check. Consequently, when the check fails, there is no need to search for a satisfying valuation. *)
Lemma reduct_theory_modal_facts {n} (t : mbnf_theory n) p i :
  reduct_theory_satb i t p = true -> rosati_modal_factsb t p = true.
Proof.
  unfold reduct_theory_satb, rosati_modal_factsb.
  rewrite !forallb_forall.
  intros H f Hf.
  specialize (H f Hf).
  destruct f; try reflexivity.
  - simpl in H.
    destruct (modal_mem (MBBelief f) p) eqn:boh.
    -- reflexivity.
    -- discriminate H.
  - simpl in H.
    destruct (modal_mem (MBNot f) p) eqn:boh.
    -- reflexivity.
    -- discriminate H.
Qed.

(** Run the preliminary check first. If it fails, return false. Otherwise, run the existing satisfiability procedure. *)
Definition rosati_guarded_satb {n} (t : mbnf_theory n) p :=
  if rosati_modal_factsb t p then partition_theory_satb t p else false.

(** The preliminary check preserves every satisfiability answer. *)
Lemma rosati_guarded_satb_eq {n} (t : mbnf_theory n) p :
  rosati_guarded_satb t p = partition_theory_satb t p.
Proof.
  unfold rosati_guarded_satb.
  destruct (rosati_modal_factsb t p) eqn:Hfacts.
  - reflexivity.
  - destruct (partition_theory_satb t p) eqn:Hsat.
    -- unfold partition_theory_satb in Hsat.
       rewrite existsb_exists in Hsat.
       destruct Hsat as [i [Hi Hsat]].
       apply reduct_theory_modal_facts in Hsat.
       rewrite Hsat in Hfacts. discriminate Hfacts.
    -- reflexivity.
Qed.

(** We now combine these improvements. Enumerate distinct guesses and store each competitor's satisfiability result and, when satisfiable, its base worlds. Reuse those values when checking candidates, stopping at the first failed check. *)
Definition rosati_distinct_cached_partitions {n} (t : mbnf_theory n) :=
  let candidates := rosati_distinct_partitions t in
  let data := map (fun r =>
    let sat := rosati_guarded_satb t r in
    (r, if sat then base_worlds t r else [], sat)) candidates in
  filter (fun p =>
    if rosati_guarded_satb t p then
      let w := base_worlds t p in
      if nonemptyb w then
        if partition_atb t p w w then
          forallb (fun entry : modal_partition n * cluster * bool =>
            let '(r, wr, sat) := entry in
            if partition_equivb (theory_modal_atoms t) p r then true
            else if sat then
              if partition_atb t r wr w then negb (subsetb w wr) else true
            else true) data
        else false
      else false
    else false) candidates.

(** This implementation produces exactly the same accepted list as filtering the distinct enumeration with the original test. Storing intermediate results and stopping early preserve the catalogue. *)
Lemma rosati_distinct_cached_partitions_eq {n} (t : mbnf_theory n) :
  rosati_distinct_cached_partitions t =
    filter (rosati_preferred_partitionb t) (rosati_distinct_partitions t).
Proof.
  unfold rosati_distinct_cached_partitions.
  apply filter_ext.
  intros p.
  unfold rosati_preferred_partitionb.
  rewrite rosati_minimal_partitionb_eq, rosati_guarded_satb_eq.
  destruct (partition_theory_satb t p).
  - destruct (nonemptyb (base_worlds t p)); try reflexivity.
    destruct (partition_atb t p (base_worlds t p) (base_worlds t p)); try reflexivity.
    rewrite <- rosati_distinct_condition_c.
    induction (rosati_distinct_partitions t) as [|r rs IH].
    -- reflexivity.
    -- cbn [map forallb].
       rewrite IH.
       unfold rosati_competitionb.
       rewrite rosati_guarded_satb_eq.
       destruct (partition_equivb (theory_modal_atoms t) p r),
         (partition_theory_satb t r),
         (partition_atb t r (base_worlds t r) (base_worlds t p)),
         (subsetb (base_worlds t p) (base_worlds t r)); reflexivity.
  - destruct (nonemptyb (base_worlds t p)); reflexivity.
Qed.

(** A complete catalogue from the distinct enumeration gives the original solver's answer to every query. As before, we require an equation proving that the supplied list contains exactly the accepted partitions. Leaving out a different accepted guess could hide a counterexample. *)
Theorem rosati_general_entailsb_from_distinct_catalogue {n} (t : mbnf_theory n) models :
  filter (rosati_preferred_partitionb t) (rosati_distinct_partitions t) = models ->
  forall q, rosati_general_entailsb t q =
    negb (existsb (fun p =>
      let reduced_query := query_reduct (mbnf_positive_query q) (base_worlds t p) in
      existsb (fun i => reduct_theory_satb i t p &&
        negb (mbsatb i [] [] reduced_query)) (all_valuations n)) models).
Proof.
  intros Hmodels q.
  rewrite (rosati_general_entailsb_from_partition_catalogue eq_refl q).
  rewrite <- Hmodels.
  f_equal.
  apply Bool.eq_true_iff_eq.
  rewrite !existsb_exists.
  split.
  - intros H.
    destruct H as [p [Hp Hq]].
    rewrite filter_In in Hp.
    destruct Hp as [Hp Hpreferred].
    destruct (rosati_distinct_partitions_cover t p) as [r [Hr Heq]].
    exists r. split.
    -- apply filter_In. split.
       --- exact Hr.
       --- rewrite <- (rosati_preferred_partitionb_ext t Heq). exact Hpreferred.
    -- rewrite existsb_exists in Hq.
       destruct Hq as [i [Hi Hq]].
       rewrite existsb_exists.
       exists i. split.
       --- exact Hi.
       --- rewrite <- (reduct_theory_satb_ext t i Heq).
           unfold base_worlds in *.
           rewrite <- (base_partition_ext t Heq). exact Hq.
  - intros H.
    destruct H as [p [Hp Hq]].
    rewrite filter_In in Hp.
    destruct Hp as [Hp Hpreferred].
    destruct (rosati_partitions_cover t p) as [r [Hr Heq]].
    exists r. split.
    -- apply filter_In. split.
       --- exact Hr.
       --- rewrite <- (rosati_preferred_partitionb_ext t Heq). exact Hpreferred.
    -- rewrite existsb_exists in Hq.
       destruct Hq as [i [Hi Hq]].
       rewrite existsb_exists.
       exists i. split.
       --- exact Hi.
       --- rewrite <- (reduct_theory_satb_ext t i Heq).
           unfold base_worlds in *.
           rewrite <- (base_partition_ext t Heq). exact Hq.
Qed.
Arguments rosati_general_entailsb_from_distinct_catalogue {n t models} _ q.

(** If this complete catalogue contains a partition with a satisfiable reduced theory, then the theory has an MBNF model. It is useful to establish this when interpreting deductions, since a theory with no models entails every query. *)
Theorem rosati_distinct_catalogue_has_model {n} (t : mbnf_theory n) models :
  filter (rosati_preferred_partitionb t) (rosati_distinct_partitions t) = models ->
  existsb (partition_theory_satb t) models = true ->
  exists i m, MBNFModel t i m.
Proof.
  intros Hmodels Hsome.
  rewrite <- Hmodels in Hsome.
  rewrite existsb_exists in Hsome.
  destruct Hsome as [p [Hp Hsat]].
  rewrite filter_In in Hp.
  destruct Hp as [Hin Hpreferred].
  unfold partition_theory_satb in Hsat.
  rewrite existsb_exists in Hsat.
  destruct Hsat as [i [Hi Hsat]].
  exists i, (base_worlds t p).
  apply rosati_preferred_partition_model; assumption.
Qed.
