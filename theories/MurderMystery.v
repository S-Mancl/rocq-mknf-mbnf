From Stdlib Require Import Bool List Vectors.Fin.
From MKNF Require Import Finite Syntax Semantics Algorithms.
Import ListNotations.
Set Implicit Arguments.

(** * Chapter 4: The case of Mr. Charlie *)

(** ** Intro *)

(**
It was a bleak morning when Detective David and I arrived at Mr. Charlie's house, an imposing, timeworn manor which appeared to date back at least two centuries. Its somewhat dilapidated appearance suggested that it had suffered decades of neglect.

As we crossed the threshold, David briefed me.

Mr. Charlie had once been a prominent figure in literary circles, until a scandal had partly ruined his reputation, though not his fortune. He had since then withdrawn from public life, living in this secluded estate with his maid, Alice, in this building constantly swept by the cold winds blowing down from the mountains.

His only regular visitor was his long-standing acquaintance Bob, a businessman of considerable means who used to bring him the latest gossip and economic news from the city.

That had been Mr. Charlie's quiet existence until he was found dead.

In his own study.

Poisoned.

It was Alice who had apparently discovered the body. And, as David explained, the only people in the house the previous day had been Alice and Bob.

I glanced at David. There were two people to question and a dead man.

The mystery was ours to unravel.
*)

(** ** Boring background things *)
Inductive case_atom : Type :=
| AlicePoisoned | BobPoisoned | EvePoisoned
| AliceUnable | BobUnable
| EveConfesses | BobConfesses
| AliceOpportunity | BobOpportunity
| AliceAlibiTelegram.
Definition encode_atom (x : case_atom) : Fin.t 10 :=
  match x with
  | AlicePoisoned => Fin.F1
  | BobPoisoned => Fin.FS Fin.F1
  | EvePoisoned => Fin.FS (Fin.FS Fin.F1)
  | AliceUnable => Fin.FS (Fin.FS (Fin.FS Fin.F1))
  | BobUnable => Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
  | EveConfesses => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
  | BobConfesses => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
  | AliceOpportunity => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))))))
  | BobOpportunity => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1))))))))
  | AliceAlibiTelegram => Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.F1)))))))))
  end.
Definition alice : mbnf_formula 10 := MBAtom (encode_atom AlicePoisoned).
Definition bob : mbnf_formula 10 := MBAtom (encode_atom BobPoisoned).
Definition eve : mbnf_formula 10 := MBAtom (encode_atom EvePoisoned).
Definition alice_unable : mbnf_formula 10 := MBAtom (encode_atom AliceUnable).
Definition bob_unable : mbnf_formula 10 := MBAtom (encode_atom BobUnable).
Definition eve_confesses : mbnf_formula 10 := MBAtom (encode_atom EveConfesses).
Definition bob_confesses : mbnf_formula 10 := MBAtom (encode_atom BobConfesses).
Definition alice_opportunity : mbnf_formula 10 := MBAtom (encode_atom AliceOpportunity).
Definition bob_opportunity : mbnf_formula 10 := MBAtom (encode_atom BobOpportunity).
Definition alice_telegram : mbnf_formula 10 := MBAtom (encode_atom AliceAlibiTelegram).
Definition exactly_one : mbnf_formula 10 :=
  ((alice or bob or eve) and ~ (alice and bob) and
    ~ (alice and eve) and ~ (bob and eve))%mbnf.
Definition case_laws : mbnf_formula 10 :=
  (exactly_one and (alice_unable implies ~ alice) and
    (bob_unable implies ~ bob))%mbnf.
Definition alice_default : mbnf_formula 10 :=
  ((B alice_opportunity and not alice_unable) implies B alice)%mbnf.
Definition bob_default : mbnf_formula 10 :=
  ((B bob_opportunity and B alice_unable and not bob_unable) implies B bob)%mbnf.
Definition telegram_rule : mbnf_formula 10 :=
  (alice_telegram implies (alice_unable and B alice_unable))%mbnf.
Definition eve_confession_rule : mbnf_formula 10 :=
  ((B eve and eve_confesses) implies eve)%mbnf.
Definition bob_confession_rule : mbnf_formula 10 :=
  ((B bob and bob_confesses) implies bob)%mbnf.
Definition detective_policy : mbnf_theory 10 :=
  [case_laws; (B case_laws)%mbnf; alice_default; bob_default; telegram_rule;
   eve_confession_rule; bob_confession_rule].
Definition initial_evidence : mbnf_theory 10 :=
  [alice_opportunity; bob_opportunity;
   (B alice_opportunity)%mbnf; (B bob_opportunity)%mbnf].
Definition stage1 : mbnf_theory 10 := detective_policy ++ initial_evidence.
Definition stage2 : mbnf_theory 10 := stage1 ++ [alice_telegram].
Definition stage3 : mbnf_theory 10 := stage2 ++ [eve_confesses].
Definition stage4 : mbnf_theory 10 := stage3 ++ [bob_confesses].
Definition telegram_policy_check : mbnf_theory 10 :=
  [case_laws; (B case_laws)%mbnf; telegram_rule; alice_telegram].
Inductive stage : Type :=
| Initial | AliceAlibi | EveConfession | BobConfession | TelegramRuleOnly.
Definition investigation (s : stage) : mbnf_theory 10 :=
  match s with
  | Initial => stage1 | AliceAlibi => stage2 | EveConfession => stage3
  | BobConfession => stage4
  | TelegramRuleOnly => telegram_policy_check
  end.
Definition initial_partitions := Eval vm_compute in
  rosati_distinct_cached_partitions stage1.
Definition alibi_partitions := Eval vm_compute in
  rosati_distinct_cached_partitions stage2.
Definition eve_partitions := Eval vm_compute in
  rosati_distinct_cached_partitions stage3.
Definition final_partitions := Eval vm_compute in
  rosati_distinct_cached_partitions stage4.
Definition telegram_rule_partitions := Eval vm_compute in
  rosati_distinct_cached_partitions telegram_policy_check.
Definition partition_catalogue (s : stage) :=
  match s with
  | Initial => initial_partitions | AliceAlibi => alibi_partitions
  | EveConfession => eve_partitions | BobConfession => final_partitions
  | TelegramRuleOnly => telegram_rule_partitions
  end.
Lemma partition_catalogue_complete s :
  filter (rosati_preferred_partitionb (investigation s))
    (rosati_distinct_partitions (investigation s)) = partition_catalogue s.
Proof.
  destruct s; rewrite <- rosati_distinct_cached_partitions_eq; vm_compute; reflexivity.
Qed.
Theorem every_stage_has_a_model s :
  exists i m, MBNFModel (investigation s) i m.
Proof.
  apply rosati_distinct_catalogue_has_model with (models:=partition_catalogue s).
  - apply partition_catalogue_complete.
  - destruct s; vm_compute; reflexivity.
Qed.

(** ** The crime scene *)

(**
We quickly went to the crime scene. The body was still there, cold, a cup of tea spilled on the floor.

"I suspect that's where the poison came from", David said.

I collected my leather-bound notebook and began recording his observations.

"There can be only one culprit: that's how it works in these cases."

He stopped, and took a cautious sniff at the cup.

"Judging by the inexpensive nature of the poison" he continued, "I infer that it has been a person with limited resources."

"So it must have been Alice, the maid?" I inquired. As far as I could tell, she was the only one who had motive, means and opportunity.

"Unless proven otherwise, she's our main suspect in this moment. But beware of jumping to conclusions this early. We will question both of them, and see what we can find out.
I see no reason to suspect Bob at present: he didn't have a motive, given his conditions, and his reputation is as clean as his silver.
I'm temporarily excluding him, until further evidence comes to light."
*)

Theorem the_initial_default_premises :
  MBNFEntails stage1
    (B alice_opportunity and B bob_opportunity and
     not alice_unable and ~ B alice_unable)%mbnf.
Proof.
  Print stage1.
  Print initial_evidence.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete Initial)). vm_compute. reflexivity.
Qed.

Theorem initially_alice_is_the_only_believed_culprit :
  MBNFEntails stage1 (B alice and ~ B bob and ~ B eve)%mbnf.
Proof.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete Initial)).
  vm_compute. reflexivity.
Qed.

(** ** The telegram from the city *)

(**
We brought Alice to the kitchen for questioning. The kettle used yesterday was still there. The girl appeared visibly shaken, though that's no proof of innocence nor guilt.

"Would you kindly reconstruct your movements before Mr. Charlie's death?" David asked, quiet but firm.

"After preparing the tea for both of us and Mr. Bob, I went to the kitchen to clean up, and later to the city to visit my brother. I came back in the very late evening, and went to Mr. Charlie's study to check on him... and..." she hesitated, staring into the void. "That's when I found him.""

"You all did take the tea together yesterday?" David asked. If I had not known him, I would have thought he was judging Charlie's choice to take tea with his maid, but I knew David was not a man given to such prejudices.

"Yes, and everything was fine at that time. Whoever poisoned it, must have done it after I left for the city."

While David continued questioning her, he instructed me to send a telegram to the city seeking confirmation.
Much to my surprise, the reply arrived within the hour. "CONFIRMED. VISITING ILL BROTHER. STOP."
Apparently, the suspicion had been misplaced.
#<!-- " -->#
*)

Theorem the_telegram_establishes_alices_alibi :
  ~ MBNFEntails stage1 alice_telegram /\
  MBNFEntails stage2 (alice_telegram and alice_unable and B alice_unable)%mbnf.
Proof.
  split.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete Initial)). vm_compute. discriminate.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete AliceAlibi)). vm_compute. reflexivity.
Qed.

Theorem the_alibi_changes_the_default_premises :
  MBNFEntails stage2
    (~ (not alice_unable) and B alice_unable and
     B bob_opportunity and not bob_unable)%mbnf.
Proof.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete AliceAlibi)). vm_compute. reflexivity.
Qed.

Theorem the_alibi_moves_suspicion_to_bob :
  MBNFEntails stage2 (B bob and ~ alice)%mbnf.
Proof.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete AliceAlibi)).
  vm_compute. reflexivity.
Qed.

Theorem the_new_alibi_withdraws_the_old_belief :
  stage2 = stage1 ++ [alice_telegram] /\
  MBNFEntails stage1 (B alice)%mbnf /\
  ~ MBNFEntails stage2 (B alice)%mbnf.
Proof.
  split; [reflexivity|]. split.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete Initial)). vm_compute. reflexivity.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete AliceAlibi)). vm_compute. discriminate.
Qed.

Theorem the_telegram_alone_does_not_identify_bob :
  MBNFEntails telegram_policy_check
    (alice_unable and B alice_unable and ~ alice and ~ B bob and ~ B eve)%mbnf /\
  ~ MBNFEntails telegram_policy_check bob.
Proof.
  split.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete TelegramRuleOnly)). vm_compute. reflexivity.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete TelegramRuleOnly)). vm_compute. discriminate.
Qed.

(** ** The new suspect *)

(**
As the wind continued to howl, we went on to question Bob. We brought him to the kitchen, asking Alice to wait back in the living room.

"Why would I ever want to poison my old friend?" he asked, visibly upset.
"We have known each other for decades, and I've always stood by him, loyal, even when everyone else abandoned him."

"Look, we are only trying to assess the situation, Mr. Bob. Alice, the maid, has an alibi. She was in the city visiting her ill brother when the poisoning occurred, as independent witnesses guaranteed. And you were the only other person in the house at the time."

"Well, maybe the old man just took his own life. He suffered from low spirits lately, which was precisely the reason for which I intensified my visits here: to try and cheer him up."

My sight met David's. This clearly was a case of murder, and the fact that Bob tried to declare otherwise only reinforced the idea that he was the murderer. Yet, without a confession, nothing was to be established.
*)

Theorem suspicion_of_bob_after_the_alibi_is_not_factual_guilt :
  MBNFEntails stage2 (B bob)%mbnf /\ ~ MBNFEntails stage2 bob.
Proof.
  split.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete AliceAlibi)). vm_compute. reflexivity.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete AliceAlibi)). vm_compute. discriminate.
Qed.

(**
While the intense discussion was going on, a sudden commotion caught our attention.

First, a door slamming open, then the unmistakable sound of an animated discussion between two female voices.

Shortly afterwards, two women appeared. One was Alice, the other a woman in her late thirties.

"Leave them to their enquiries", Alice said.

"I insist to speak with the detective, privately, now!".

David and the mysterious woman retired to the kitchen, while I brought both Alice and Bob downstairs to the living room. They sat down on the sofa, still exchanging glances in suspicion.

After some minutes, David asked me upstairs. We conferred in whispers.

"So, what did you find out?", I asked.

"She confessed. Her name's Eve, and she just confessed the crime. But I cannot believe her, since she had no way of being here."

I couldn't believe my ears. "If she confessed, then she must be guilty. Why would a person arrive to a crime scene just to lie?"

"Money, love, revenge... who knows. The very same reasons that could bring her to kill. I still believe that it has been Bob, but without a confession I cannot establish it beyond any reasonable doubt."
*)


Theorem eve_lacks_the_required_prior_belief :
  MBNFEntails stage2 (~ B eve)%mbnf.
Proof.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete AliceAlibi)). vm_compute. reflexivity.
Qed.

Theorem eves_confession_does_not_establish_her_guilt :
  MBNFEntails stage3 (B bob and ~ B eve)%mbnf /\ ~ MBNFEntails stage3 eve.
Proof.
  split.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete EveConfession)). vm_compute. reflexivity.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete EveConfession)). vm_compute. discriminate.
Qed.

Theorem belief_in_bob_before_his_confession_is_not_factual_guilt :
  MBNFEntails stage3 (B bob)%mbnf /\ ~ MBNFEntails stage3 bob.
Proof.
  split.
  - apply rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete EveConfession)). vm_compute. reflexivity.
  - rewrite <- rosati_general_entailsb_correct.
    rewrite (rosati_general_entailsb_from_distinct_catalogue
      (partition_catalogue_complete EveConfession)). vm_compute. discriminate.
Qed.

(** ** The confession and the conclusion *)

(**
A few days later, we heard that most of Bob's businesses had gone bankrupt, and that he was in no position to pay his debts. After interrogating him, he confessed the crime, and the case was finally closed.
*)

Theorem bob_is_the_factual_culprit :
  MBNFEntails stage4 (bob and ~ alice and ~ eve)%mbnf.
Proof.
  apply rosati_general_entailsb_correct.
  rewrite (rosati_general_entailsb_from_distinct_catalogue
    (partition_catalogue_complete BobConfession)). vm_compute. reflexivity.
Qed.
