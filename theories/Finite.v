From Stdlib Require Import Bool List Arith.PeanoNat Vectors.Fin.
Import ListNotations.

Set Implicit Arguments.

(** If [f] and [g] agree on every entry of [xs], they give the same answer
    to the question: do all entries pass? *)
Lemma forallb_ext_eq {A} (f g : A -> bool) xs :
  (forall x, In x xs -> f x = g x) -> forallb f xs = forallb g xs.
Proof.
  intros H. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. now right.
Qed.

(** If [f] and [g] agree on every entry of [xs], either test can be used to
    check whether some entry passes. Their behaviour outside [xs] does not
    matter. *)
Lemma existsb_ext_eq {A} (f g : A -> bool) xs :
  (forall x, In x xs -> f x = g x) -> existsb f xs = existsb g xs.
Proof.
  intros H. induction xs as [|x xs IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)), IH; [reflexivity|].
  intros y Hy. apply H. now right.
Qed.

(** A list fails the all-entries check exactly when it contains a failing
    entry. The empty list passes: there is nothing in it that could fail. *)
Lemma forallb_false_exists {A} (f : A -> bool) xs :
  forallb f xs = false <-> exists x, In x xs /\ f x = false.
Proof.
  induction xs as [|x xs IH]; simpl.
  - split; [discriminate|intros [y [[] _]]].
  - destruct (f x) eqn:Hx; simpl.
    + rewrite IH. split.
      * intros [y [Hy Hfalse]]. exists y. auto.
      * intros [y [[<-|Hy] Hfalse]].
        -- congruence.
        -- now exists y.
    + split.
      * intros _. exists x. auto.
      * intros _. reflexivity.
Qed.

(** * Appendix A: Internal finite enumeration support

    This appendix collects the list and enumeration functions used by the
    algorithms.  First-time readers may skip it.  It appears last in the
    generated manual even though other files import it.

    A valuation for an [n]-atom language is a Boolean list of length [n].  Only
    valuations produced by [all_valuations n] enter canonical clusters, so
    the enumeration enforces the required length.

<<
    all_valuations(0)     = [[]]
    all_valuations(n + 1) = map (cons false) (all_valuations(n))
                              ++ map (cons true) (all_valuations(n))
    all_clusters(n)       = powerset(all_valuations(n))
>>

    Lists are only representatives.  [subset], [same_set], and
    [proper_subset] are extensional and ignore representation equality.  The
    powerset enumeration supplies duplicate-free, consistently ordered
    representatives to executable searches because [all_valuations] itself
    has no duplicates.  [lookup] uses [false] as an out-of-range default, but
    canonical valuations always have the required length, so that default is
    unreachable in semantic and algorithmic calls. *)


(** A valuation describes one possible world by assigning a Boolean value to
    each atom. With atoms [p] and [q], for example, [true; false] means that
    [p] is true and [q] is false. We store these assignments as lists;
    [all_valuations] below supplies lists of the right length. *)
Definition valuation := list bool.

(** Decide whether two valuations are equal. Besides the decision, Rocq
    returns a proof of equality or inequality. *)
Definition valuation_eq_dec : forall x y : valuation, {x = y} + {x <> y} :=
  list_eq_dec Bool.bool_dec.

(** Compare two valuations as Boolean lists. The result is true when every
    entry matches and the lists have the same length. *)
Definition valuation_eqb (x y : valuation) : bool :=
  if valuation_eq_dec x y then true else false.

(** The comparison returns true exactly when the two valuation lists are
    equal. *)
Lemma valuation_eqb_spec (x y : valuation) :
  valuation_eqb x y = true <-> x = y.
Proof.
  unfold valuation_eqb. destruct (valuation_eq_dec x y); split; congruence.
Qed.

(** Read an atom's value from the corresponding position in a valuation. A
    missing position returns false. This fallback is never needed for
    valuations generated for the correct number of atoms. *)
Definition lookup {n} (v : valuation) (i : Fin.t n) : bool :=
  nth (proj1_sig (Fin.to_nat i)) v false.

(** List all [2^n] assignments for [n] atoms. Start with the single empty
    assignment for zero atoms; at each step, prepend false and true to every
    assignment already generated. *)
Fixpoint all_valuations (n : nat) : list valuation :=
  match n with
  | 0 => [[]]
  | S k => map (cons false) (all_valuations k) ++
           map (cons true) (all_valuations k)
  end.

(** Every generated assignment has the requested length, so it has an entry
    for each atom in the language. *)
Lemma all_valuations_length n v :
  In v (all_valuations n) -> length v = n.
Proof.
  revert v. induction n as [|n IH]; intros v H; simpl in H.
  - destruct H as [<-|[]]. reflexivity.
  - apply in_app_iff in H as [H|H];
      apply in_map_iff in H as [tl [<- Htl]]; simpl; f_equal; now apply IH.
Qed.

(** Every Boolean list of length [n] appears in [all_valuations n]. The
    search therefore covers every assignment to the [n] atoms. *)
Lemma all_valuations_complete n v :
  length v = n -> In v (all_valuations n).
Proof.
  revert v. induction n as [|n IH]; intros v Hlen.
  - destruct v; [simpl; auto|discriminate].
  - destruct v as [|b tl]; [discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. apply in_app_iff. destruct b; [right|left];
      apply in_map; now apply IH.
Qed.

(** Return true if the given valuation occurs in the list. *)
Definition mem_valuation (v : valuation) (xs : list valuation) : bool :=
  existsb (valuation_eqb v) xs.

(** The membership test returns true exactly when the valuation belongs to
    the list. *)
Lemma mem_valuation_spec v xs :
  mem_valuation v xs = true <-> In v xs.
Proof.
  unfold mem_valuation. rewrite existsb_exists.
  split.
  - intros [x [Hx Heq]]. apply valuation_eqb_spec in Heq. now subst.
  - intros H. exists v. split; [assumption|]. apply valuation_eqb_spec; reflexivity.
Qed.

(** List all choices of entries to keep, from keeping none to keeping all.
    We use this both to enumerate sets of worlds and to choose which modal
    formulas to mark true. Repeated entries in the input can produce
    repeated choices. *)
Fixpoint powerset {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: tl => let ps := powerset tl in ps ++ map (cons x) ps
  end.


(** Filtering a list always produces one of the choices in its powerset. A
    candidate built by keeping entries that pass a test is therefore
    included in the exhaustive enumeration. *)
Lemma filter_in_powerset {A} (keep : A -> bool) xs :
  In (filter keep xs) (powerset xs).
Proof.
  induction xs as [|x xs IH]; simpl; [now left|].
  destruct (keep x); apply in_app_iff.
  - right. now apply in_map.
  - now left.
Qed.


(** A cluster stores the worlds an agent considers possible. A formula is
    known or believed when it holds in every world of the relevant cluster.
    The list is just a representation: set comparisons ignore order and
    repetitions. *)
Definition cluster := list valuation.

(** Decide whether two cluster lists are equal, including their order and
    repeated entries. *)
Definition cluster_eq_dec : forall x y : cluster, {x = y} + {x <> y} :=
  list_eq_dec valuation_eq_dec.

(** Compare two cluster lists for exact equality. To compare just the sets
    of worlds they contain, use [same_set] below. *)
Definition cluster_eqb (x y : cluster) : bool :=
  if cluster_eq_dec x y then true else false.

(** The comparison returns true exactly when the cluster lists are equal. *)
Lemma cluster_eqb_spec x y : cluster_eqb x y = true <-> x = y.
Proof.
  unfold cluster_eqb. destruct (cluster_eq_dec x y); split; congruence.
Qed.

(** Return true if this exact cluster list occurs among the candidates. *)
Definition mem_cluster (c : cluster) (cs : list cluster) : bool :=
  existsb (cluster_eqb c) cs.

(** The membership test returns true exactly when the cluster list belongs
    to the candidate list. *)
Lemma mem_cluster_spec c cs : mem_cluster c cs = true <-> In c cs.
Proof.
  unfold mem_cluster. rewrite existsb_exists.
  split.
  - intros [d [Hd Heq]]. apply cluster_eqb_spec in Heq. now subst.
  - intros H. exists c. split; [assumption|]. apply cluster_eqb_spec; reflexivity.
Qed.

(** List every subset of the valuation universe. There are [2^n] valuations
    for [n] atoms, so this list has [2^(2^n)] candidate clusters. This is
    where direct model search becomes expensive. *)
Definition all_clusters n : list cluster := powerset (all_valuations n).

(** A cluster is canonical if it comes from [all_clusters n]. Its worlds
    then have the right length, and their order follows the fixed
    enumeration. *)
Definition canonical_cluster n (c : cluster) : Prop :=
  In c (all_clusters n).

(** Check whether every world in [xs] also belongs to [ys]. Equality counts
    as containment, and list order does not matter. *)
Definition subsetb (xs ys : cluster) : bool :=
  forallb (fun x => mem_valuation x ys) xs.


(** Check whether [ys] contains all the worlds of [xs] and at least one
    more. Adding possibilities means committing to less information. *)
Definition proper_subsetb (xs ys : cluster) : bool :=
  subsetb xs ys && negb (subsetb ys xs).

(** Write containment as a logical statement: every world in [xs] is also in
    [ys]. This is the condition computed by [subsetb]. *)
Definition subset (xs ys : cluster) : Prop :=
  forall x, In x xs -> In x ys.

(** Two clusters represent the same set when each contains all the worlds of
    the other. Their list order and repeated entries may differ. *)
Definition same_set (xs ys : cluster) : Prop :=
  subset xs ys /\ subset ys xs.

(** Say that [ys] contains all the worlds of [xs] and some additional
    possibilities. Model definitions use this relation to ask whether a
    candidate could leave more worlds open and still satisfy the theory. *)
Definition proper_subset (xs ys : cluster) : Prop :=
  subset xs ys /\ ~ subset ys xs.

(** The Boolean containment check agrees with the logical definition of
    containment. *)
Lemma subsetb_spec xs ys :
  subsetb xs ys = true <-> subset xs ys.
Proof.
  unfold subsetb, subset. rewrite forallb_forall.
  setoid_rewrite mem_valuation_spec. reflexivity.
Qed.


(** The Boolean strict-containment check agrees with the logical definition:
    the second cluster must contain every world of the first and at least
    one more. *)
Lemma proper_subsetb_spec xs ys :
  proper_subsetb xs ys = true <-> proper_subset xs ys.
Proof.
  unfold proper_subsetb, proper_subset.
  rewrite andb_true_iff, negb_true_iff, subsetb_spec.
  split.
  - intros [Hxy Hyx]. split; [assumption|].
    intro H. apply subsetb_spec in H. congruence.
  - intros [Hxy Hyx]. split; [assumption|].
    destruct (subsetb ys xs) eqn:H; [|reflexivity].
    apply subsetb_spec in H. contradiction.
Qed.

(** Every entry of a powerset choice comes from the original list. Choosing
    a cluster from the valuation universe cannot introduce a new, invalid
    world. *)
Lemma powerset_member_is_subset {A} (xs ys : list A) :
  In ys (powerset xs) -> forall y, In y ys -> In y xs.
Proof.
  revert ys. induction xs as [|x xs IH]; intros ys Hps y Hy; simpl in Hps.
  - destruct Hps as [Hps|Hps]; [subst ys; contradiction|contradiction].
  - apply in_app_iff in Hps as [Hps|Hps].
    + right. eapply IH; eauto.
    + apply in_map_iff in Hps as [zs [<- Hzs]].
      destruct Hy as [<-|Hy]; [left; reflexivity|right]. eapply IH; eauto.
Qed.

(** Every world in a canonical cluster for [n] atoms has exactly [n] Boolean
    entries. *)
Lemma canonical_valuation_length n c v :
  canonical_cluster n c -> In v c -> length v = n.
Proof.
  intros Hc Hv. apply all_valuations_length.
  eapply powerset_member_is_subset; eauto.
Qed.
