(** The Coq module [ArithUtils] contains arithmetic related lemmas
    that help in proving the properties of interest in the formalization.

    - @author Anonymized
    - @author Anonymized
    - @author Anonymized
    - @author Anonymized

*)

Require Import ZArith.
Require Import Lia.
Require Import Int63.Sint63.
Require Import Ascii String Coq.Strings.Byte.
Require Import Lists.List.
Import ListNotations.


Lemma to_Z_of_nat:
  forall (n:nat),
    (Z.of_nat n < wB / 2)%Z ->
    to_Z (Int63.Uint63.of_nat n) = Z.of_nat n.
Proof.
  intros.
  rewrite of_Z_spec.
  rewrite cmod_small;  lia.
Qed.



  
Lemma of_nat_succ:
  forall n,
    (Z.of_nat (S n) < wB / 2)%Z ->
    Int63.Uint63.of_nat (S n) = (1 + Int63.Uint63.of_nat n)%sint63.
Proof.
  induction n.
  * intros. simpl.
    now cbv.
  * intros.
    apply to_Z_inj.
    rewrite IHn; try lia.
    rewrite add_spec.
    rewrite add_spec.
    rewrite to_Z_of_nat by lia.
    replace (S (S n)) with (1 + (1 + n)) by lia.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_add.
    rewrite Nat2Z.inj_succ in H.
    rewrite Nat2Z.inj_succ in H.
    replace (Z.of_nat 1) with 1%Z by now cbv.
    replace (to_Z 1) with 1%Z by now cbv.
    rewrite cmod_small.
    ** rewrite to_Z_of_nat by lia.
       rewrite cmod_small; try lia.
    ** rewrite to_Z_of_nat by lia.
      rewrite cmod_small; try lia.
Qed.

Lemma of_nat_plus:
  forall n m,
    (Z.of_nat (n + m) < wB / 2)%Z ->
    Int63.Uint63.of_nat (n + m)%nat = ((Int63.Uint63.of_nat n) + (Int63.Uint63.of_nat m))%uint63.
Proof.
  induction n.
  * intros.
    simpl.
    rewrite add_of_Z.
    simpl.
    rewrite of_Z_spec.
    now rewrite of_Z_cmod.
  * intros.
    rewrite plus_Sn_m.
    rewrite of_nat_succ by lia.
    rewrite of_nat_succ by lia.
    rewrite IHn by lia.
    now rewrite add_assoc.
Qed.

Check mul_of_Z.

Search "nat".

Print cmod.

Lemma of_nat_mult:
  forall n m,
    (Z.of_nat (n * m) < wB / 2)%Z ->
    Int63.Uint63.of_nat (n * m)%nat = ((Int63.Uint63.of_nat n) * (Int63.Uint63.of_nat m))%uint63.
Proof.
  induction n.
  * intros.
    simpl.
    rewrite mul_of_Z.
    now simpl.
  * intros.
    replace (S n * m)%nat with (m + n * m)%nat by lia.
    apply to_Z_inj.
    rewrite to_Z_mul.
    ** replace (S n) with (1 + n)%nat by lia.
       rewrite of_nat_plus.
       rewrite of_nat_plus.
       *** replace (to_Z (Uint63.of_nat 1 + Uint63.of_nat n)) with ((to_Z (Uint63.of_nat 1) + to_Z (Uint63.of_nat n)))%Z.
        ****  replace (to_Z (Uint63.of_nat 1)) with 1%Z by now cbv.
              replace (((1 + to_Z (Uint63.of_nat n)) * to_Z (Uint63.of_nat m)))%Z with ((to_Z (Uint63.of_nat m)) + (to_Z (Uint63.of_nat n)) * (to_Z (Uint63.of_nat m)))%Z.
              rewrite <- to_Z_mul.
              rewrite IHn.
              rewrite <- to_Z_add.

              Search "to_Z".
             (* rewrite to_Z_of_nat by lia.
             rewrite cmod_small; try lia. *)
       (* rewrite to_Z_add at 3. *)
       (* Search "to_Z". *)

    (* Search "to_Z".


    rewrite of_nat_plus.
    ** rewrite of_nat_succ.
       *** Search "to_Z".

       *** replace (((1 + Uint63.of_nat n) * Uint63.of_nat m)%sint63)  with ((Uint63.of_nat m + Uint63.of_nat (n * m))%sint63).
           **** now simpl.
           ****  

    rewrite <- of_to_Z at 1.
    rewrite mul_of_Z.
    rewrite of_Z_spec.
    rewrite cmod_small; try lia.



    Check Nat2Z.id.
    Search of_Z.
    rewrite <- Nat2Z.id.
    simpl.


    Search to_Z.
    replace (S n * m) with (m + n * m)%nat by lia.
    rewrite of_nat_plus.
    ** rewrite IHn. *)
        (* rewrite Nmult_Sn_m.
    rewrite of_nat_succ by lia.
    rewrite of_nat_succ by lia.
    rewrite IHn by lia.
    now rewrite add_assoc. *)
Admitted.


Lemma of_nat_minus:
  forall n m,
    (Z.of_nat n < wB / 2)%Z ->
    m <= n ->
    Int63.Uint63.of_nat (n - m)%nat = ((Int63.Uint63.of_nat n) - (Int63.Uint63.of_nat m))%uint63.
Proof.
  induction n.
  * intros.
    apply Nat.le_0_r in H0.
    subst m.
    now simpl.
  * intros.
    assert (1 + Z.of_nat  n < wB / 2)%Z. {
      replace (S n) with (n + 1) in H by lia. 
      rewrite Nat2Z.inj_add in H.
      simpl in H.
      lia.
    }
    destruct (le_gt_dec (S n) m).
    ** assert (m = S n) by lia.
       subst m.
       rewrite Nat.sub_diag.
       rewrite sub_of_Z.
       rewrite Z.sub_diag.
       now simpl. 
    ** assert (m <= n) by lia.
      rewrite Nat.sub_succ_l by lia.
       rewrite of_nat_succ by lia.
       rewrite of_nat_succ by lia.
       rewrite IHn by lia.
       assert (Z.of_nat m <= Z.of_nat n)%Z by auto using inj_le.
       assert (to_Z (Int63.Uint63.of_nat m) >= 0)%Z. {
         rewrite of_Z_spec.
         rewrite cmod_small; lia.
       }
       apply  to_Z_inj.
       rewrite add_spec.
       rewrite sub_spec.
       rewrite sub_spec.
       rewrite add_spec.
       replace (to_Z 1) with 1%Z by now cbv.
       rewrite to_Z_of_nat by lia.
       rewrite to_Z_of_nat by lia.
       rewrite cmod_small.
       *** rewrite cmod_small; try lia.
           rewrite cmod_small; try lia.
           rewrite cmod_small; try lia.
           rewrite cmod_small; try lia.
       *** rewrite cmod_small; try lia.
Qed.


Lemma zero_leq_max_int:
  (0 <= to_Z max_int)%Z.
Proof.
  replace 0%Z with (to_Z 0) by now simpl.
  apply to_Z_bounded.
Qed.


Lemma abs_int_low:
  (to_Z min_int < 0)%Z.
Proof.
  now compute.
Qed.

Definition is_one_byte (n:int) := (0 <= (to_Z n) <= 2^8 - 1)%Z.

(** A predicate to check if the integer [n] fits in two octets. *)
Definition is_two_byte (n:int) := (0 <= (to_Z n) <= 2^16 - 1)%Z.

Definition is_one_byte_sint (n: int): bool :=
  (0 <=? n)%sint63 && (n <? 256)%sint63.

Definition is_two_byte_sint (n: int): bool :=
  (0 <=? n)%sint63 && (n <? 65536)%sint63.

Lemma is_one_byte_non_negative:
  forall n, is_one_byte n -> (0 <=? to_Z n)%Z = true.
Proof.
  intros.
  unfold is_one_byte in H.
  apply Z.leb_le.
  now apply H.
Qed.

Lemma is_one_byte_negative:
  forall n, is_one_byte n -> (to_Z n <? 0)%Z = false.
Proof.
  intros.
  unfold is_one_byte in H.
  now apply Z.ltb_ge.
Qed.

Lemma is_two_byte_non_negative:
  forall n, is_two_byte n -> (0 <=? to_Z n)%Z = true.
Proof.
  intros.
  unfold is_two_byte in H.
  apply Z.leb_le.
  now apply H.
Qed.

Lemma is_two_byte_negative:
  forall n, is_two_byte n -> (to_Z n <? 0)%Z = false.
Proof.
  intros.
  unfold is_two_byte in H.
  now apply Z.ltb_ge.
Qed.

(** Create a one byte out of an integer [no] in the range 0..255.

 It should not be used for integers outside the range. *)

(** Create a two bytes out of an integer [no] in the range 0..65535.

 It should not be used for integers outside the range. *)
Definition two_byte_of_int (no:int) :=
  let hibyte := (to_Z (no / 256%uint63))%Z in
  let lobyte := (to_Z (no mod 256%uint63))%Z in
  if (256 <=? hibyte)%Z
  then (string_of_list_ascii ["000"%char; "000"%char])
  else (string_of_list_ascii [(ascii_of_nat (Z.to_nat hibyte));
                              (ascii_of_nat (Z.to_nat lobyte))]).


Lemma is_two_byte_leq256:
  forall no,
    is_two_byte no ->      
    (256 <=? to_Z (no / 256%sint63))%Z= false.
Proof.
  intros.
  unfold is_two_byte in H.
  apply Z.leb_nle.
  intro.
  destruct H.
  apply Z.le_ge in H0.
  assert (256 > 0)%Z by lia.
  rewrite div_spec in H0.
  * rewrite Z.quot_div_nonneg in H0;[|auto|now compute]; try lia.
    apply Z.le_ge in H1.
    eapply Z_div_ge in H1; eauto.
    replace (to_Z 256) with (256%Z) in H0 by now compute.
    simpl in H1.
    replace (65535 / 256)%Z with 255%Z in H1 by now compute.
    lia.
  * right;now compute.
Qed.

Lemma split_two_bytes_eq_init:
  forall (no:int),
    is_two_byte no ->
    (of_Z           
       (Z.of_nat   
          (256 * nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (no / 256)))) +
             nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (no mod 256))))))) = no.
Proof.
  intros.
  unfold is_two_byte in H.
  assert (to_Z 256 = 256%Z) as to256. { 
    now compute.
  }
  rewrite nat_ascii_embedding.
  rewrite nat_ascii_embedding.  
  * rewrite Nat2Z.inj_add.
    replace 256  with (Z.to_nat 256%Z); [|now compute].
    rewrite div_spec;[|right;now compute].
    rewrite Z.quot_div_nonneg; try lia. 
    rewrite <- Z2Nat.inj_mul;try apply Z.div_pos; try lia. 
    rewrite Z2Nat.id.
    rewrite Z2Nat.id.
    ** rewrite mod_spec.
       rewrite Z.rem_mod_nonneg; try lia.    
       rewrite to256.   
       rewrite <- Z_div_mod_eq_full.
       now rewrite of_to_Z.
    ** rewrite mod_spec.
       rewrite Z.rem_mod_nonneg; try lia.
       rewrite to256.
       apply Z_mod_nonneg_nonneg;lia.
    ** apply Ztac.mul_le;try lia.
       apply Z.div_pos; try lia.
  * rewrite mod_spec.
    rewrite Z.rem_mod_nonneg; try lia.
    rewrite to256.
    rewrite Z2Nat.inj_mod;try lia.
    replace (Z.to_nat 256) with 256;[|now compute].
    apply Nat.mod_bound_pos; try lia.
  * replace 256 with (Z.to_nat 256%Z) by lia. 
    apply Z2Nat.inj_lt; try lia. 
    ** rewrite div_spec;[|right;now compute].
       rewrite Z.quot_div_nonneg; try lia. 
       rewrite to256.
       apply Z_div_nonneg_nonneg; try lia.
    ** rewrite div_spec;[|right;now compute].
       rewrite Z.quot_div_nonneg; [|lia|lia].
       rewrite to256.
       apply Z.div_lt_upper_bound; try lia.
Qed.




Lemma max_zero_rem:
  forall no,
    (0 <= to_Z no <= 2 ^ 16 - 1)%Z ->
    Z.max 0 (Z.rem (to_Z no) (to_Z 256)) =  (Z.rem (to_Z no) (to_Z 256)).
Proof.
  intros.
  decompose [and] H;clear H.
  rewrite Z.max_r;auto.
  apply Z.rem_bound_pos;eauto.
  now compute.
Qed.

Lemma max_zero_quot:
  forall no,
    (0 <= to_Z no <= 2 ^ 16 - 1)%Z ->
    (Z.max 0 (to_Z no  ÷ to_Z 256) = (to_Z no  ÷ to_Z 256))%Z.
Proof.
  intros.
  decompose [and] H;clear H.
  rewrite Z.max_r;auto.
  apply Z.quot_le_lower_bound; auto.
  now compute.
Qed.

Lemma rem_of_Z:
  forall x y,
    of_Z (Z.rem (to_Z x) (to_Z y)) = (x mod y)%sint63.
Proof.
  intros.
  rewrite <- mod_spec.
  now rewrite of_to_Z.
Qed.
  
Lemma quot_of_Z:
  forall x y,
     x <> min_int \/ to_Z y <> (-1)%Z ->
    of_Z (to_Z x  ÷ to_Z y) = (x / y)%sint63.
Proof.
  intros.
  rewrite <- div_spec.
  * now rewrite of_to_Z.
  * destruct H.
    ** left.
       intro.
       apply H.
       now apply to_Z_inj.
    ** now right.
Qed.


Lemma split_two_bytes_eq_init_int:
  forall (no:int),
    is_two_byte no ->
    (256 * Int63.Uint63.of_nat (nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (no / 256))))) +
       Int63.Uint63.of_nat (nat_of_ascii (ascii_of_nat (Z.to_nat (to_Z (no mod 256))))))%sint63  = no.
Proof.
  intros.
  unfold is_two_byte in H.
  decompose [and] H.
  assert (to_Z 256 = 256%Z) as to256. { 
    now compute.
  }
  rewrite nat_ascii_embedding.
  rewrite nat_ascii_embedding.
  * rewrite add_of_Z.
    rewrite div_spec;[|right;now compute].
    rewrite ZifyInst.of_nat_to_nat_eq.
    rewrite ZifyInst.of_nat_to_nat_eq.
    rewrite mod_spec.
    rewrite max_zero_rem;auto.
    rewrite max_zero_quot;auto.
    rewrite <- is_int.
    **  assert (
            to_Z (256 * of_Z (to_Z no ÷ to_Z 256)) =
              (to_Z 256) * (to_Z no ÷ to_Z 256))%Z as tvs.
        {
          assert (to_Z no ÷ to_Z 256 < 256)%Z.
          {
            apply Z.quot_lt_upper_bound; try lia.
          }
          assert (256 < Z.pow_pos 2 63 / 2)%Z by now compute.
          assert (0 <= to_Z no ÷ to_Z 256)%Z. {
            rewrite to256.
            apply Z.quot_le_lower_bound; lia.
          }
          rewrite to_Z_mul.
          -  rewrite of_Z_spec.
             replace (cmod (to_Z no ÷ to_Z 256) wB)%Z with (to_Z no ÷ to_Z 256)%Z.
             auto.
             rewrite cmod_small.
             auto.
             split.
             -- simpl.
                lia.
             -- unfold wB.
                unfold size.
                simpl.
                lia.
          - split.
            -- assert (0 <= to_Z 256 * to_Z (of_Z (to_Z no ÷ to_Z 256)))%Z. {
                 rewrite to256.
                 rewrite of_Z_spec.
                 apply Z.mul_nonneg_nonneg; try lia.
                 rewrite cmod_small.
                 + apply Z.quot_pos; try lia.
                 + split.
                   ++ rewrite to256 in *.
                      simpl.
                      lia.
                   ++ rewrite to256 in *.
                      unfold wB.
                      simpl.
                      lia.
               }
               replace (to_Z min_int) with  (-4611686018427387904)%Z by now compute.
               lia.
            -- rewrite to256.
               assert (to_Z (of_Z (to_Z no ÷ 256)) <= 256)%Z. {
                 replace   (to_Z (of_Z (to_Z no ÷ 256))) with (cmod (to_Z no ÷ 256) wB)
                   by now rewrite of_Z_spec.
                 rewrite cmod_small.
                 + apply Z.quot_le_upper_bound; try lia.
                 + split.
                   ++ unfold wB.
                      simpl.
                      rewrite <- to256.
                      lia.
                   ++ rewrite <- to256.
                      unfold wB.
                      simpl.
                      lia.
               }
               assert ( 256 * to_Z (of_Z (to_Z no ÷ 256)) <= 256*256)%Z. {
                 apply Z.mul_le_mono_nonneg_l;lia.
               }
               assert (256 * 256 <= to_Z max_int)%Z by now compute.
               lia.
        }
        rewrite tvs.
        rewrite to256.
        rewrite <- Z.quot_rem'.
        now rewrite of_to_Z.
    ** split.
       *** assert (0 <= Z.rem (to_Z no) (to_Z 256))%Z.
           {apply  Z.rem_nonneg;auto.
            rewrite to256.
            congruence.
           }
           generalize abs_int_low;intros.
           lia.
       *** generalize Z.rem_bound_pos_pos;intros.
           assert (2 ^ 16 - 1 <= to_Z max_int)%Z. {
             unfold max_int.
             now compute.
           }
           assert ((to_Z no) <= to_Z max_int)%Z by lia.
           assert (0 <=Z.rem (to_Z no) (to_Z 256) <  (to_Z 256))%Z by (apply H2;auto;lia).
           rewrite to256 in *.
           assert (256 <= to_Z max_int)%Z by now compute.
           lia.
  * assert (to_Z (no mod 256) < 256%Z)%Z. {
      rewrite mod_spec.
      apply Z.rem_bound_pos_pos; lia.
    }
    replace 256 with (Z.to_nat 256) by now compute.
    lia.
  * assert (to_Z (no / 256) < 256%Z)%Z. {
      rewrite div_spec.
      apply Z.quot_lt_upper_bound; try lia.
      right; congruence.
    } 
    replace 256 with (Z.to_nat 256) by now compute.
    lia.
Qed.
