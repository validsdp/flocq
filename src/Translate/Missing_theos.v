Require Import Float.Veltkamp.
Require Import Float.RND.
Require Export Float.Fast2Sum.
Require Import Float.TwoSum.
Require Import Float.FmaErr.
Require Import Float.Dekker.
Require Import Float.FmaErrApprox.

From Flocq Require Import Fcore Fprop_plus_error Fprop_mult_error Fcalc_ops.
Require Import Ftranslate_flocq2Pff.

Open Scope R_scope.

Section FTS.
Variable emin prec : Z.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let a := round_flt (x+y).
Let b := round_flt (round_flt (a-x)-y).

(** Theorem *)
Theorem FastTwoSum: Rabs y <= Rabs x -> a-b=x+y.
Proof with auto with typeclass_instances.
intros H.
(* *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
(* *)
pose (Iplus := fun (f g:Float.float) => 
  Fnormalize radix2 (make_bound radix2 prec emin) (Zabs_nat prec)
   (Float.Float 
     (Ztrunc (scaled_mantissa radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f+FtoR radix2 g))))
     (canonic_exp radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f+FtoR radix2 g))))).
pose (Iminus := fun (f g:Float.float) => 
  Fnormalize radix2 (make_bound radix2 prec emin) (Zabs_nat prec)
   (Float.Float 
      (Ztrunc (scaled_mantissa radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f-FtoR radix2 g))))
      (canonic_exp radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f-FtoR radix2 g))))).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_; intros x y.
assert (format (round_flt (FtoR 2 x + FtoR 2 y))).
apply generic_format_round...
unfold Iplus; rewrite FnormalizeCorrect.
2: apply radix_gt_1.
rewrite H; change 2%Z with (radix_val radix2).
apply FtoR_F2R; try easy.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_; intros x y.
assert (format (round_flt (FtoR 2 x - FtoR 2 y))).
apply generic_format_round...
unfold Iminus; rewrite FnormalizeCorrect.
2: apply radix_gt_1.
rewrite H; change 2%Z with (radix_val radix2).
apply FtoR_F2R; try easy.
(* *)
assert (K: FtoR 2 (Iminus fy (Iminus (Iplus fx fy) fx)) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Fast2Sum.Dekker with (make_bound radix2 prec emin) (Zabs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
(* . *)
intros p q Fp Fq.
destruct round_NE_is_pff_round with radix2 (make_bound radix2 prec emin) prec (FtoR 2 p +FtoR 2 q)
   as (f, (L1,(L2,L3))); try assumption.
apply make_bound_p; omega.
generalize ClosestCompatible; unfold CompatibleP.
intros T; apply T with (FtoR 2 p + FtoR 2 q) f; clear T; try easy.
apply L2.
change 2%Z with (radix_val radix2).
rewrite L3, H1.
rewrite make_bound_Emin; try easy.
f_equal; f_equal; ring.
unfold Iplus.
apply FnormalizeBounded.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Zabs_nat prec).
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
apply FcanonicFopp.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
rewrite Fopp_correct.
rewrite 2!H1.
rewrite <- round_NE_opp.
rewrite 2!Fopp_correct.
f_equal; ring.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Zabs_nat prec).
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
rewrite H1,H2.
rewrite Fopp_correct.
f_equal; ring.
(* . *)
unfold Fast2Sum.FtoRradix.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; assumption.
(* *)
generalize K; rewrite 2!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy; fold a; unfold b; intros K'.
apply Rplus_eq_reg_r with (-a).
apply trans_eq with (round_flt (y - round_flt (a - x))).
2: rewrite K'; ring.
ring_simplify.
rewrite <- round_NE_opp.
f_equal; ring.
Qed.

End FTS.

Section TS.

Variable emin prec : Z.
Hypothesis precisionNotZero : (1 < prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format radix2 (FLT_exp emin prec)).
Notation round_flt :=(round radix2 (FLT_exp emin prec) ZnearestE).
Notation bpow e := (bpow radix2 e).

(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let a  := round_flt (x+y).
Let x' := round_flt (a-x).
Let dx := round_flt (x- round_flt (a-x')).
Let dy := round_flt (y - x').
Let b  := round_flt (dx + dy).

(** Theorem *)
Theorem TwoSum: a+b=x+y.
Proof with auto with typeclass_instances.
(* *)
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format radix2 (make_bound radix2 prec emin)
   prec (make_bound_p radix2 prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
(* *)
pose (Iplus := fun (f g:Float.float) => 
  Fnormalize radix2 (make_bound radix2 prec emin) (Zabs_nat prec)
   (Float.Float 
     (Ztrunc (scaled_mantissa radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f+FtoR radix2 g))))
     (canonic_exp radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f+FtoR radix2 g))))).
pose (Iminus := fun (f g:Float.float) => 
  Fnormalize radix2 (make_bound radix2 prec emin) (Zabs_nat prec)
   (Float.Float 
      (Ztrunc (scaled_mantissa radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f-FtoR radix2 g))))
      (canonic_exp radix2 (FLT_exp (emin) prec) (round_flt (FtoR radix2 f-FtoR radix2 g))))).
assert (H1: forall x y, FtoR 2 (Iplus x y) = round_flt (FtoR 2 x + FtoR 2 y)).
clear -prec_gt_0_; intros x y.
assert (format (round_flt (FtoR 2 x + FtoR 2 y))).
apply generic_format_round...
unfold Iplus; rewrite FnormalizeCorrect.
2: apply radix_gt_1.
rewrite H; change 2%Z with (radix_val radix2).
apply FtoR_F2R; try easy.
assert (H2: forall x y, FtoR 2 (Iminus x y) = round_flt (FtoR 2 x - FtoR 2 y)).
clear -prec_gt_0_; intros x y.
assert (format (round_flt (FtoR 2 x - FtoR 2 y))).
apply generic_format_round...
unfold Iminus; rewrite FnormalizeCorrect.
2: apply radix_gt_1.
rewrite H; change 2%Z with (radix_val radix2).
apply FtoR_F2R; try easy.
(* *)
assert (K: FtoR 2 (Iplus (Iminus fx (Iminus (Iplus fx fy) (Iminus (Iplus fx fy) fx)))
            (Iminus fy (Iminus (Iplus fx fy) fx))) =
       FtoR 2 fx + FtoR 2 fy - FtoR 2 (Iplus fx fy)).
apply Knuth with (make_bound radix2 prec emin) (Zabs_nat prec); try assumption.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
(* . *)
intros p q Fp Fq.
destruct round_NE_is_pff_round with radix2 (make_bound radix2 prec emin) prec (FtoR 2 p +FtoR 2 q)
   as (f, (L1,(L2,L3))); try assumption.
apply make_bound_p; omega.
generalize ClosestCompatible; unfold CompatibleP.
intros T; apply T with (FtoR 2 p + FtoR 2 q) f; clear T; try easy.
apply L2.
change 2%Z with (radix_val radix2).
rewrite L3, H1.
rewrite make_bound_Emin; try easy.
f_equal; f_equal; ring.
unfold Iplus.
apply FnormalizeBounded.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
(* . *)
unfold TwoSum.FtoRradix.
intros p q r s Fp Fq Fr Fs M1 M2.
now rewrite 2!H1, M1, M2.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Zabs_nat prec).
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
rewrite 2!H1.
f_equal; ring.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Zabs_nat prec).
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
apply FcanonicFopp.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
rewrite Fopp_correct.
rewrite 2!H1.
rewrite <- round_NE_opp.
rewrite 2!Fopp_correct.
f_equal; ring.
(* . *)
intros p q.
apply FcanonicUnique with radix2 (make_bound radix2 prec emin) (Zabs_nat prec).
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
apply FnormalizeCanonic.
apply radix_gt_1.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
replace emin with (-dExp (make_bound radix2 prec emin))%Z at 2 4.
apply format_is_pff_format'; try omega.
apply make_bound_p; omega.
rewrite make_bound_Emin; try easy.
rewrite Zopp_involutive.
apply generic_format_round...
rewrite make_bound_Emin; omega.
rewrite H1,H2.
rewrite Fopp_correct.
f_equal; ring.
(* *)
generalize K; rewrite 2!H1, 5!H2, H1.
change 2%Z with (radix_val radix2).
rewrite Hfx, Hfy.
fold a; fold x'; fold dx; fold dy; fold b.
intros K'; rewrite K'; ring.
Qed.


End TS.




Section Veltkamp.

Variable beta : radix.
Variable emin prec : Z.
Variable s:Z.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

(** inputs *)
Hypothesis SLe: (2 <= s)%Z.
Hypothesis SGe: (s <= prec-2)%Z.
Variable x:R.
Hypothesis Fx: format x.

(** algorithm *)
Let p := round_flt (x*(bpow s+1)).
Let q:= round_flt (x-p).
Let hx:=round_flt (q+p).
Let tx:=round_flt (x-hx).


(** Theorems *)

Lemma C_format: format (bpow s +1).
Proof with auto with typeclass_instances.
apply generic_format_FLT.
unfold FLT_format.
exists (Fcore_defs.Float beta (Zpower beta s+1)%Z 0%Z).
split; try split; simpl; try easy.
unfold F2R; simpl.
rewrite Z2R_plus, Z2R_Zpower; try omega.
simpl; ring.
rewrite Zabs_eq.
apply Zle_lt_trans with (beta^s+beta^0)%Z.
simpl; omega.
apply Zle_lt_trans with (beta^s+beta^s)%Z.
apply Zplus_le_compat_l.
apply Zpower_le; omega.
apply Zle_lt_trans with (2*beta^s)%Z.
omega.
apply Zle_lt_trans with (beta^1*beta^s)%Z.
apply Zmult_le_compat_r.
rewrite Z.pow_1_r. 
apply Zle_bool_imp_le; apply beta.
apply Zpower_ge_0.
rewrite <- Zpower_plus; try omega.
apply Zpower_lt; omega.
apply Zle_trans with (beta^s)%Z; try omega.
apply Zpower_ge_0.
Qed.


Theorem Veltkamp_Even: hx = round_flt_s x.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by omega.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by omega.
(* *)
destruct VeltkampEven with beta (make_bound beta prec emin) (Zabs_nat s) 
   (Zabs_nat prec) fx fp fq fhx as (hx', (H1,H2)); try assumption.
apply radix_gt_1.
apply make_bound_p; omega.
replace 2%nat with (Zabs_nat 2) by easy.
apply Zabs_nat_le; omega.
apply Nat2Z.inj_le.
rewrite inj_abs; try omega.
rewrite inj_minus, Zmax_r; rewrite inj_abs; simpl; omega.
rewrite Hfx; rewrite inj_abs; try omega.
rewrite bpow_powerRZ in Hfp'; rewrite Z2R_IZR in Hfp'; exact Hfp'.
rewrite Hfx, Hfp''; assumption.
rewrite Hfp'', Hfq''; assumption.
(* *)
unfold hx; rewrite <- Hfhx'', <- H1.
apply trans_eq with (FtoR beta (RND_EvenClosest 
 (make_bound beta (prec-s) emin) beta (Zabs_nat (prec-s)) x)).
generalize (EvenClosestUniqueP (make_bound beta (prec-s) emin) beta 
   (Zabs_nat (prec-s))); unfold UniqueP; intros T.
apply T with x; clear T.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
rewrite <- Hfx.
replace (Zabs_nat (prec-s)) with (Zabs_nat prec - Zabs_nat s)%nat.
replace (make_bound beta (prec - s) emin) with
  (Bound  (Pos.of_succ_nat
                 (Peano.pred
                    (Z.abs_nat
                       (Zpower_nat beta (Z.abs_nat prec - Z.abs_nat s)))))
           (dExp (make_bound beta prec emin))).
exact H2.
generalize (make_bound_Emin beta (prec-s) _ emin_neg).
generalize (make_bound_p beta (prec-s) emin).
destruct (make_bound beta (prec-s) emin) as (l1,l2).
simpl; intros H3 H4; f_equal.
apply Pos2Z.inj.
rewrite H3; try omega.
replace (Z.abs_nat (prec - s)) with (Z.abs_nat prec - Z.abs_nat s)%nat.
rewrite <- (p'GivesBound beta (make_bound beta prec emin) (Zabs_nat s) (Zabs_nat prec)) at 2.
simpl; easy.
apply radix_gt_1.
apply Nat2Z.inj.
rewrite inj_abs; try omega.
rewrite inj_minus, Zmax_r; rewrite 2!inj_abs; omega.
apply N2Z.inj.
rewrite H4.
rewrite Zabs2N.id_abs.
now apply Z.abs_neq.
apply Nat2Z.inj.
rewrite inj_abs; try omega.
rewrite inj_minus, Zmax_r; rewrite 2!inj_abs; omega.
apply RND_EvenClosest_correct.
apply radix_gt_1.
apply Nat2Z.inj_lt.
rewrite inj_abs; simpl; omega.
apply make_bound_p; omega.
rewrite pff_round_NE_is_round; try omega.
f_equal; f_equal.
rewrite make_bound_Emin; omega.
apply make_bound_p; omega.
Qed.


Theorem Veltkamp_Tail:
 x = hx+tx /\  generic_format beta (FLT_exp emin s) tx.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by omega.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x*(bpow s+1)))
  as (fp,(Hfp, (Hfp',Hfp''))).
rewrite make_bound_Emin in Hfp''; try assumption.
replace (--emin)%Z with emin in Hfp'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x-p))
  as (fq,(Hfq, (Hfq',Hfq''))).
rewrite make_bound_Emin in Hfq''; try assumption.
replace (--emin)%Z with emin in Hfq'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (q+p))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by omega.
(* *)
destruct Veltkamp_tail with beta (make_bound beta prec emin) (Zabs_nat s) 
   (Zabs_nat prec) fx fp fq fhx ftx as (tx', (H1,(H2,(H3,H4)))); try assumption.
apply radix_gt_1.
apply make_bound_p; omega.
replace 2%nat with (Zabs_nat 2) by easy.
apply Zabs_nat_le; omega.
apply Nat2Z.inj_le.
rewrite inj_abs; try omega.
rewrite inj_minus, Zmax_r; rewrite inj_abs; simpl; omega.
rewrite Hfx; rewrite inj_abs; try omega.
rewrite bpow_powerRZ in Hfp'; rewrite Z2R_IZR in Hfp'; apply Hfp'.
rewrite Hfx, Hfp''; apply Hfq'.
rewrite Hfp'', Hfq''; apply Hfhx'.
rewrite Hfhx'', Hfx; apply Hftx'.
(* *)
split.
rewrite <- Hfx, <-H2, Hfhx'', H1, Hftx''; easy.
unfold tx; rewrite <- Hftx'', <- H1.
replace emin with (-dExp (Bound
       (Pos.of_succ_nat
                 (Peano.pred (Z.abs_nat (Zpower_nat beta (Z.abs_nat s)))))
       (dExp (make_bound beta prec emin))))%Z.
apply pff_format_is_format; try assumption; try omega.
simpl.
rewrite Zpos_P_of_succ_nat, inj_pred.
rewrite <- Zsucc_pred.
apply inj_abs.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
apply notEqLt, lt_Zlt_inv.
rewrite inj_abs.
apply Zpower_nat_less.
apply radix_gt_1.
apply Zpower_NR0.
apply Zlt_le_weak; apply radix_gt_0.
simpl.
rewrite Zabs2N.id_abs.
rewrite Z.abs_neq; omega.
Qed.

End Veltkamp.

Section Underf_mult_aux.

Variable beta : radix.
Variable b: Fbound.
Variable prec: Z.

Hypothesis pGivesBound : Zpos (vNum b) = Zpower_nat beta (Zabs_nat prec).
Hypothesis precisionGt1 : (1 < prec)%Z.

Lemma underf_mult_aux:
 forall x y, 
  Fbounded b x ->
  Fbounded b y ->
   (bpow beta (-dExp b + 2 * prec - 1)%Z <= Rabs (FtoR beta x * FtoR beta y)) ->
     (-dExp b <= Float.Fexp x + Float.Fexp y)%Z.
Proof.
intros x y Fx Fy H.
assert (HH: forall z, Fbounded b z 
   -> Rabs (FtoR beta z) < bpow beta (Float.Fexp z + prec)).
clear -precisionGt1 pGivesBound; intros z Hz.
unfold FtoR; rewrite <- 2!Z2R_IZR; rewrite <- bpow_powerRZ.
rewrite Rabs_mult, Rmult_comm.
rewrite Rabs_right.
2: apply Rle_ge, bpow_ge_0.
rewrite bpow_plus; apply Rmult_lt_compat_l.
apply bpow_gt_0.
destruct Hz as (T1,T2).
rewrite pGivesBound in T1.
rewrite <- Z2R_abs, <- Z2R_Zpower;[idtac|omega].
apply Z2R_lt.
apply Zlt_le_trans with (1:=T1).
rewrite Zpower_Zpower_nat; omega.
assert (-dExp b+2*prec-1 < (Float.Fexp x+prec) +(Float.Fexp y +prec))%Z; try omega.
(* *)
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
now apply HH.
now apply HH.
Qed.

End Underf_mult_aux.


Section Dekker.

Variable beta : radix.
Variable emin prec: Z.
Let s:= (prec- Z.div2 prec)%Z.

Hypothesis precisionGe4 : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin < 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation round_flt_s :=(round beta (FLT_exp emin (prec-s)) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).
Notation bpow e := (bpow beta e).

(** inputs *)
Variable x y:R.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(*** algorithm *)
(** first Veltkamp *)
Let px := round_flt (x*(bpow s+1)).
Let qx:= round_flt (x-px).
Let hx:=round_flt (qx+px).
Let tx:=round_flt (x-hx).

(** second Veltkamp *)
Let py := round_flt (y*(bpow s+1)).
Let qy:= round_flt (y-py).
Let hy:=round_flt (qy+py).
Let ty:=round_flt (y-hy).

(** all products *)
Let x1y1:=round_flt (hx*hy).
Let x1y2:=round_flt (hx*ty).
Let x2y1:=round_flt (tx*hy).
Let x2y2:=round_flt (tx*ty).

(** final summation *)
Let r :=round_flt(x*y).
Let t1 :=round_flt (-r+x1y1).
Let t2 :=round_flt (t1+x1y2).
Let t3 :=round_flt (t2+x2y1).
Let t4 :=round_flt (t3+x2y2).

Theorem Dekker: (radix_val beta=2)%Z \/ (Z.Even prec) ->
  (bpow (emin + 2 * prec - 1) <= Rabs (x * y) ->  (x*y=r+t4)%R) /\
    (Rabs (x*y-(r+t4)) <= (7/2)*bpow emin)%R.
Proof with auto with typeclass_instances.
intros HH.
(* Veltkamp x *)
assert (precisionNotZero : (1 < prec)%Z) by omega.
assert (emin_neg': (emin <= 0)%Z) by omega.
destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x*(bpow s+1)))
  as (fpx,(Hfpx, (Hfpx',Hfpx''))).
rewrite make_bound_Emin in Hfpx''; try assumption.
replace (--emin)%Z with emin in Hfpx'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x-px))
  as (fqx,(Hfqx, (Hfqx',Hfqx''))).
rewrite make_bound_Emin in Hfqx''; try assumption.
replace (--emin)%Z with emin in Hfqx'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (qx+px))
  as (fhx,(Hfhx, (Hfhx',Hfhx''))).
rewrite make_bound_Emin in Hfhx''; try assumption.
replace (--emin)%Z with emin in Hfhx'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x-hx))
  as (ftx,(Hftx, (Hftx',Hftx''))).
rewrite make_bound_Emin in Hftx''; try assumption.
replace (--emin)%Z with emin in Hftx'' by omega.
(* Veltkamp y*)
destruct (format_is_pff_format_can beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (y*(bpow s+1)))
  as (fpy,(Hfpy, (Hfpy',Hfpy''))).
rewrite make_bound_Emin in Hfpy''; try assumption.
replace (--emin)%Z with emin in Hfpy'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (y-py))
  as (fqy,(Hfqy, (Hfqy',Hfqy''))).
rewrite make_bound_Emin in Hfqy''; try assumption.
replace (--emin)%Z with emin in Hfqy'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (qy+py))
  as (fhy,(Hfhy, (Hfhy',Hfhy''))).
rewrite make_bound_Emin in Hfhy''; try assumption.
replace (--emin)%Z with emin in Hfhy'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (y-hy))
  as (fty,(Hfty, (Hfty',Hfty''))).
rewrite make_bound_Emin in Hfty''; try assumption.
replace (--emin)%Z with emin in Hfty'' by omega.
(* products *)
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (hx*hy))
  as (fx1y1,(Hfx1y1, (Hfx1y1',Hfx1y1''))).
rewrite make_bound_Emin in Hfx1y1''; try assumption.
replace (--emin)%Z with emin in Hfx1y1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (hx*ty))
  as (fx1y2,(Hfx1y2, (Hfx1y2',Hfx1y2''))).
rewrite make_bound_Emin in Hfx1y2''; try assumption.
replace (--emin)%Z with emin in Hfx1y2'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (tx*hy))
  as (fx2y1,(Hfx2y1, (Hfx2y1',Hfx2y1''))).
rewrite make_bound_Emin in Hfx2y1''; try assumption.
replace (--emin)%Z with emin in Hfx2y1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (tx*ty))
  as (fx2y2,(Hfx2y2, (Hfx2y2',Hfx2y2''))).
rewrite make_bound_Emin in Hfx2y2''; try assumption.
replace (--emin)%Z with emin in Hfx2y2'' by omega.
(* t_is *)
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (x*y))
  as (fr,(Hfr, (Hfr',Hfr''))).
rewrite make_bound_Emin in Hfr''; try assumption.
replace (--emin)%Z with emin in Hfr'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (-r+x1y1))
  as (ft1,(Hft1, (Hft1',Hft1''))).
rewrite make_bound_Emin in Hft1''; try assumption.
replace (--emin)%Z with emin in Hft1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (t1+x1y2))
  as (ft2,(Hft2, (Hft2',Hft2''))).
rewrite make_bound_Emin in Hft2''; try assumption.
replace (--emin)%Z with emin in Hft2'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (t2+x2y1))
  as (ft3,(Hft3, (Hft3',Hft3''))).
rewrite make_bound_Emin in Hft3''; try assumption.
replace (--emin)%Z with emin in Hft3'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero 
  (t3+x2y2))
  as (ft4,(Hft4, (Hft4',Hft4''))).
rewrite make_bound_Emin in Hft4''; try assumption.
replace (--emin)%Z with emin in Hft4'' by omega.
(* *)
assert (Hs:(s =(Z.abs_nat prec - Nat.div2 (Z.abs_nat prec))%nat)).
unfold s; rewrite inj_minus.
assert (TT: (Z.div2 prec = Nat.div2 (Z.abs_nat prec))%Z).
rewrite Nat.div2_div, Z.div2_div, div_Zdiv; simpl.
rewrite inj_abs; omega.
omega.
rewrite <- TT.
rewrite inj_abs; try omega.
rewrite Z.max_r; try omega.
assert (Z.div2 prec <= prec)%Z; try omega.
rewrite Z.div2_div; apply Zlt_le_weak.
apply Z_div_lt; omega.
(* *)
assert (D:(((- dExp (make_bound beta prec emin) <= Float.Fexp fx + Float.Fexp fy)%Z -> 
        (FtoR beta fx * FtoR beta fy = FtoR beta fr + FtoR beta ft4)) /\
   Rabs (FtoR beta fx * FtoR beta fy - (FtoR beta fr + FtoR beta ft4)) <=
       7 / 2 * powerRZ beta (- dExp (make_bound beta prec emin)))).
apply Dekker.Dekker with (Zabs_nat prec) fpx fqx fhx ftx fpy fqy fhy fty 
   fx1y1 fx1y2 fx2y1 fx2y2 ft1 ft2 ft3; try assumption.
apply radix_gt_1.
apply make_bound_p; omega.
replace 4%nat with (Zabs_nat 4) by easy.
apply Zabs_nat_le; omega.
(* . *)
rewrite Hfx, <- Hs, <- Z2R_IZR, <- bpow_powerRZ; apply Hfpx'.
rewrite Hfx, Hfpx''; apply Hfqx'.
rewrite Hfpx'', Hfqx''; apply Hfhx'.
rewrite Hfx, Hfhx''; apply Hftx'.
rewrite Hfy, <- Hs, <- Z2R_IZR, <- bpow_powerRZ; apply Hfpy'.
rewrite Hfy, Hfpy''; apply Hfqy'.
rewrite Hfpy'', Hfqy''; apply Hfhy'.
rewrite Hfy, Hfhy''; apply Hfty'.
rewrite Hfhx'', Hfhy''; apply Hfx1y1'.
rewrite Hfhx'', Hfty''; apply Hfx1y2'.
rewrite Hftx'', Hfhy''; apply Hfx2y1'.
rewrite Hftx'', Hfty''; apply Hfx2y2'.
rewrite Hfx, Hfy; apply Hfr'.
rewrite Hfr'', Hfx1y1''; apply Hft1'.
rewrite Hft1'', Hfx1y2''; apply Hft2'.
rewrite Hft2'', Hfx2y1''; apply Hft3'.
rewrite Hft3'', Hfx2y2''; apply Hft4'.
rewrite make_bound_Emin; omega.
case HH; intros K;[now left|right].
destruct K as (l,Hl).
apply even_equiv.
exists (Zabs_nat l).
apply Nat2Z.inj.
rewrite inj_mult.
rewrite 2!inj_abs; try omega.
rewrite Hl; simpl; easy.
(* *)
rewrite <- Hfx, <- Hfy.
unfold r; rewrite <- Hfr''.
unfold t4; rewrite <- Hft4''.
destruct D as (D1,D2); split.
intros L.
apply D1.
apply underf_mult_aux with beta prec; try assumption.
apply make_bound_p; assumption.
now apply FcanonicBound with beta.
now apply FcanonicBound with beta.
apply Rle_trans with (2:=L).
right; repeat f_equal.
rewrite make_bound_Emin, Zopp_involutive; omega.
apply Rle_trans with (1:=D2).
rewrite make_bound_Emin, Zopp_involutive.
2: omega.
rewrite bpow_powerRZ, Z2R_IZR.
now right.
Qed.


End Dekker.

Section ErrFMA_V1.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

(** Non-underflow hypotheses *)
Hypothesis V1_Und1: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis V1_Und2: alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Hypothesis V1_Und4: beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Hypothesis V1_Und5: r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.

(** Deduced from non-underflow hypotheses *)
Lemma V1_Und3': u1 = 0 \/ bpow beta (emin + 2*prec-1) <= Rabs u1.
Proof with auto with typeclass_instances.
case V1_Und1; intros K.
left; unfold u1.
rewrite K; apply round_0...
right; unfold u1.
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
Qed.

Lemma V1_Und3: u1 = 0 \/ bpow beta (emin + prec) <= Rabs u1.
Proof.
case V1_Und3';[now left|right].
apply Rle_trans with (2:=H).
apply bpow_le; omega.
Qed.


(** Theorems *)
Lemma ErrFMA_bounded: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
split.
apply generic_format_round...
split.
apply generic_format_round...
replace (r3) with (-(r2-(gamma+alpha2))) by (unfold r3; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
Qed.


Lemma ErrFMA_correct:
   a*x+y = r1+r2+r3.
Proof with auto with typeclass_instances.
(* *)
destruct V1_Und1 as [HZ|Und1'].
assert (HZ1: u1 = 0).
unfold u1; rewrite HZ; apply round_0...
rewrite HZ; unfold r3; ring_simplify.
unfold gamma, alpha2, beta2, beta1, alpha1.
rewrite HZ1; replace u2 with 0.
rewrite Rplus_0_r, Rplus_0_l; rewrite 2!round_generic with (x:=y)...
replace r1 with y.
replace (y-y) with 0 by ring.
rewrite Rplus_0_r, round_0...
rewrite Rplus_0_r, round_0...
ring.
unfold r1; rewrite HZ.
rewrite Rplus_0_l, round_generic...
unfold u2; rewrite HZ, HZ1; ring.
(* *)
assert (precisionNotZero : (1 < prec)%Z) by omega.
replace (r1+r2+r3) with (r1+gamma+alpha2).
2: unfold r3; ring.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
assert (J2: format alpha2).
replace (alpha2) with (-(alpha1-(y+u2))) by (unfold alpha2; ring).
apply generic_format_opp.
apply plus_error...
assert (J3: format beta2).
replace (beta2) with (-(beta1-(u1+alpha1))) by (unfold beta2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
apply generic_format_round...
(* values *)
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero alpha2)
  as (fal2,(Hfal2,Hfal2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero beta2)
  as (fbe2,(Hfbe2,Hfbe2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
rewrite <- Hfa, <- Hfx, <- Hfy, <- Hfal2.
(* roundings *)
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (a*x+y))
  as (fr1,(Hfr1, (Hfr1',Hfr1''))).
rewrite make_bound_Emin in Hfr1''; try assumption.
replace (--emin)%Z with emin in Hfr1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (y+u2))
  as (fal1,(Hfal1, (Hfal1',Hfal1''))).
rewrite make_bound_Emin in Hfal1''; try assumption.
replace (--emin)%Z with emin in Hfal1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (u1+alpha1))
  as (fbe1,(Hfbe1, (Hfbe1',Hfbe1''))).
rewrite make_bound_Emin in Hfbe1''; try assumption.
replace (--emin)%Z with emin in Hfbe1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (beta1-r1))
  as (ff,(Hff, (Hff',Hff''))).
rewrite make_bound_Emin in Hff''; try assumption.
replace (--emin)%Z with emin in Hff'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (FtoR beta ff+beta2))
  as (fga,(Hfga, (Hfga',Hfga''))).
rewrite make_bound_Emin in Hfga''; try assumption.
replace (--emin)%Z with emin in Hfga'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (gamma+alpha2))
  as (fr2,(Hfr2, (Hfr2',Hfr2''))).
rewrite make_bound_Emin in Hfr2''; try assumption.
replace (--emin)%Z with emin in Hfr2'' by omega.
unfold r1; rewrite <- Hfr1''.
unfold gamma; rewrite <- Hff'', <- Hfga''.
(* *)
apply FmaErr_Even with (make_bound beta prec emin) (Z.abs_nat prec) fu1 fu2 fal1 fbe1 fbe2 ff;
  try assumption.
apply radix_gt_1.
apply make_bound_p; omega.
replace 3%nat with (Z.abs_nat 3).
apply Zabs_nat_le; omega.
now unfold Z.abs_nat, Pos.to_nat.
(* . underflow *)
rewrite Hfal1''; fold alpha1.
case V1_Und2; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; omega.
omega.
apply FcanonicBound with (1:=Hfal1).
rewrite Hfal1''; fold alpha1.
now rewrite make_bound_Emin, Zopp_involutive.
rewrite Hfu1''; fold u1.
case V1_Und3; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; omega.
omega.
apply FcanonicBound with (1:=Hfu1).
rewrite Hfu1''; fold u1.
now rewrite make_bound_Emin, Zopp_involutive.
rewrite Hfbe1''; fold beta1.
case V1_Und4; intros V;[now right|left].
apply FloatFexp_gt with beta (make_bound beta prec emin) prec.
apply make_bound_p; omega.
omega.
apply FcanonicBound with (1:=Hfbe1).
rewrite Hfbe1''; fold beta1.
rewrite make_bound_Emin, Zopp_involutive; try assumption.
apply Rle_trans with (2:=V); right.
f_equal; ring.
rewrite Hfr1''; fold r1.
case V1_Und5; intros V;[now right|left].
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; omega.
rewrite Hfr1''; fold r1.
rewrite make_bound_Emin, Zopp_involutive; try assumption.
apply underf_mult_aux with beta prec; try assumption.
apply make_bound_p; omega.
rewrite Hfa, Hfx.
apply Rle_trans with (2:=Und1').
rewrite make_bound_Emin, Zopp_involutive.
now right.
omega.
(* . end of underflow *)
rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfy, Hfu2; apply Hfal1'.
now rewrite Hfal2, Hfy, Hfu2, Hfal1''.
now rewrite Hfbe2, Hfu1'', Hfal1'', Hfbe1''.
rewrite Hfbe1'', Hfr1''; apply Hff'.
rewrite Hfbe2; apply Hfga'.
rewrite Hfa, Hfx, Hfy; apply Hfr1'.
rewrite Hfu1'', Hfal1''; apply Hfbe1'.
Qed.

End ErrFMA_V1.

Section ErrFMA_V2.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis Even_radix: Even beta.
Hypothesis precisionGe3 : (3 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).


Lemma F2R_ge: forall (y:float beta), 
   (F2R y <> 0)%R -> (bpow beta (Fexp y) <= Rabs (F2R y))%R.
Proof.
intros (ny,ey).
rewrite <- F2R_Zabs; unfold F2R; simpl.
case (Zle_lt_or_eq 0 (Z.abs ny)).
apply Z.abs_nonneg.
intros Hy _.
rewrite <- (Rmult_1_l (bpow _ _)) at 1.
apply Rmult_le_compat_r.
apply bpow_ge_0.
replace 1 with (Z2R 1) by reflexivity; apply Z2R_le; omega.
intros H1 H2; contradict H2.
replace ny with 0%Z.
simpl; ring.
now apply sym_eq, Z.abs_0_iff, sym_eq.
Qed.



Lemma mult_error_FLT_ge: forall a b e, format a -> format b -> 
   a*b = 0 \/ bpow beta e <= Rabs (a*b) ->
   a*b-round_flt (a*b) = 0 \/
     bpow beta (e+1-2*prec) <= Rabs (a*b-round_flt (a*b)).
Proof with auto with typeclass_instances.
intros a b e Fa Fb H.
pose (x:=a * b - round_flt (a * b)); fold x.
case (Req_dec x 0); intros Zx.
now left.
case (Req_dec (a * b) 0); intros Zab.
contradict Zx.
unfold x; rewrite Zab, round_0...
ring.
case H; clear H; intros H.
now contradict H.
right; generalize Zx.
unfold x; rewrite Fa, Fb, <- F2R_mult.
simpl (Fmult _ _ _).
destruct (round_repr_same_exp beta (FLT_exp emin prec) 
 ZnearestE (Ztrunc (scaled_mantissa beta (FLT_exp emin prec) a) *
             Ztrunc (scaled_mantissa beta (FLT_exp emin prec) b))
      (canonic_exp beta (FLT_exp emin prec) a +
             canonic_exp beta (FLT_exp emin prec) b)) as (n,Hn).
rewrite Hn; clear Hn.
rewrite <- F2R_minus, Fminus_same_exp.
intros K.
eapply Rle_trans with (2:=F2R_ge _ K).
simpl (Fexp _).
apply bpow_le.
unfold canonic_exp, FLT_exp.
destruct (ln_beta beta a) as (ea,Ha).
destruct (ln_beta beta b) as (eb,Hb).
apply Zle_trans with ((ea-prec)+(eb-prec))%Z.
replace ((ea-prec)+(eb-prec))%Z with ((-1+(ea+eb))+(1-2*prec))%Z by ring.
rewrite <- Z.add_sub_assoc.
apply Zplus_le_compat_r.
assert (e < ea+eb)%Z;[idtac|omega].
apply lt_bpow with beta.
apply Rle_lt_trans with (1:=H).
rewrite Rabs_mult, bpow_plus.
apply Rmult_lt_compat.
apply Rabs_pos.
apply Rabs_pos.
apply Ha.
intros K'; apply Zab; rewrite K'; ring.
apply Hb.
intros K'; apply Zab; rewrite K'; ring.
apply Zplus_le_compat; apply Z.le_max_l.
Qed.


(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let r1 := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let alpha1 := round_flt (y+u2).
Let alpha2 := (y+u2)-alpha1.
Let beta1 := round_flt (u1+alpha1).
Let beta2 := (u1+alpha1) - beta1.
Let gamma := round_flt (round_flt (beta1-r1)+beta2).
Let r2 := round_flt (gamma+alpha2).
Let r3 := (gamma+alpha2) -r2.

(** Non-underflow hypotheses *)
Hypothesis U1: a * x = 0 \/ bpow beta (emin + 4*prec - 3) <= Rabs (a * x).
Hypothesis U2: y = 0 \/ bpow beta (emin + 2*prec) <= Rabs y.

Lemma ErrFMA_bounded_simpl: format r1 /\ format r2 /\ format r3.
Proof with auto with typeclass_instances.
apply ErrFMA_bounded; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
omega.
Qed.


Lemma V2_Und4: a*x <> 0 -> beta1 = 0 \/ bpow beta (emin + prec+1) <= Rabs beta1.
Proof with auto with typeclass_instances.
intros Zax.
unfold beta1; case U1; intros H.
now contradict H.
replace (emin+prec+1)%Z with ((emin+2*prec+1)-prec)%Z by ring.
apply rnd_0_or_ge_FLT; try assumption...
apply generic_format_round...
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (2:=H).
apply bpow_le; omega.
Qed.

Lemma V2_Und2:  y <> 0 ->  alpha1 = 0 \/ bpow beta (emin + prec) <= Rabs alpha1.
Proof with auto with typeclass_instances.
intros Zy.
unfold alpha1.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
omega.
replace (emin+prec)%Z with ((emin+2*prec)-prec)%Z by ring.
apply rnd_0_or_ge_FLT...
case U2; try easy.
Qed.

Lemma V2_Und5: a*x <> 0 -> r1 = 0 \/ bpow beta (emin + prec-1) <= Rabs r1.
Proof with auto with typeclass_instances.
intros Zax.
case (Req_dec r1 0); intros Zr1.
now left.
case U1; intros H.
now contradict H.
right.
case U2; intros Hy.
unfold r1; rewrite Hy, Rplus_0_r.
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (2:=H).
apply bpow_le; omega.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
case (Req_dec u2 0); intros Zu2.
rewrite Zu2, Rplus_0_r.
case (rnd_0_or_ge_FLT beta ZnearestE emin prec y u1 (emin + 2*prec))...
apply generic_format_round...
intros Z; contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
now rewrite Zu2, Rplus_0_r, Rplus_comm.
intros H1; rewrite Rplus_comm; apply Rle_trans with (2:=H1).
apply bpow_le; omega.
(* *)
case (rnd_0_or_ge_FLT beta ZnearestE emin prec u1 y (emin + 3 * prec - 2))...
apply generic_format_round...
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (2:=H).
apply bpow_le; omega.
intros H1.
apply round_plus_eq_zero in H1...
2: apply generic_format_round...
unfold r1; replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
case (mult_error_FLT_ge a x (emin + 4 * prec - 3)); try assumption.
intros H2; contradict Zr1.
unfold r1; replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with (u1+y+u2) by ring.
rewrite H1, Rplus_0_l.
unfold u2, u1; rewrite H2, round_0...
fold u1 u2; intros H2.
apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
apply Rle_trans with (2:=H2).
apply bpow_le; omega.
intros H1.
generalize Zr1; unfold r1.
replace (a*x)%R with (u1+u2)%R.
2: unfold u2, u1; ring.
replace (u1+u2+y) with ((u1+y)+u2) by ring.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
case U1; intros J; [now left|right].
apply Rle_trans with (2:=J); apply bpow_le.
omega.
intros K; apply abs_round_ge_generic...
apply FLT_format_bpow...
omega.
assert (K':u1 + y + u2 <> 0).
intros L; apply K; rewrite L.
apply round_0...
generalize K'.
unfold u1; unfold round.
rewrite Fy, Fu2.
rewrite <- F2R_plus, <- F2R_plus.
intros L.
apply Rle_trans with (2:=F2R_ge _ L).
rewrite 2!Fexp_Fplus.
apply bpow_le.
apply Z.min_glb.
apply Z.min_glb.
simpl.
apply Zle_trans with (FLT_exp emin prec (emin +3*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; omega.
apply canonic_exp_ge_bpow...
apply Rle_trans with (2:=H).
apply bpow_le; omega.
simpl.
apply Zle_trans with (FLT_exp emin prec (emin +2*prec+1)).
unfold FLT_exp.
rewrite Z.max_l; omega.
apply canonic_exp_ge_bpow...
apply Rle_trans with (2:=Hy).
apply bpow_le; omega.
simpl.
apply Zle_trans with (FLT_exp emin prec (emin +2*prec-1)).
unfold FLT_exp.
rewrite Z.max_l; omega.
apply canonic_exp_ge_bpow...
case (mult_error_FLT_ge a x (emin+4*prec-3)); try assumption.
intros Z; contradict Zu2.
unfold u2, u1; easy.
intros H2.
apply Rle_trans with (2:=H2).
apply bpow_le.
omega.
Qed.


Lemma ErrFMA_correct_simpl:
   a*x+y = r1+r2+r3.
Proof with auto with typeclass_instances.
(* *)
case (Req_dec (a*x) 0); intros Zax.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2,u2,u1.
rewrite Zax, round_0...
unfold Rminus; repeat rewrite Rplus_0_l.
rewrite Ropp_0, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
replace (y+-y) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
rewrite round_0, Rplus_0_l...
ring.
(* *)
case (Req_dec u2 0); intros Zu2.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, u1, alpha1, alpha2.
rewrite Zu2, Rplus_0_r.
repeat rewrite (round_generic _ _ _ y)...
ring_simplify.
assert (G:round_flt (a * x) = a*x).
apply trans_eq with (u1+u2).
now rewrite Zu2, Rplus_0_r.
unfold u2, u1; ring.
rewrite G.
replace (round_flt (a * x + y) - round_flt (a * x + y)) with 0 by ring.
rewrite round_0, Rplus_0_l...
rewrite (round_generic _ _ _ (a * x + y - round_flt (a * x + y))).
ring.
replace (a * x + y - round_flt (a * x + y)) with
 (- (round_flt (a * x + y) -(a*x+y))) by ring.
apply generic_format_opp.
rewrite <- G.
apply plus_error...
apply generic_format_round...
(* *)
case (Req_dec y 0); intros Zy.
assert (Fu2: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
omega.
unfold r3, r2, gamma, alpha2, beta2, beta1, r1, alpha1, alpha2.
rewrite Zy, Rplus_0_r, Rplus_0_l; fold u1.
rewrite (round_generic _ _ _ u2)...
replace (u1+u2) with (a*x).
2: unfold u2, u1; ring.
fold u1; ring_simplify (u1-u1).
rewrite round_0...
rewrite Rplus_0_l.
fold u2; rewrite (round_generic _ _ _ u2)...
ring_simplify (u2+(u2-u2)).
rewrite (round_generic _ _ _ u2)...
unfold u2,u1; ring.
(* *)
apply ErrFMA_correct; try assumption.
case U1; intros H; [now left|right].
apply Rle_trans with (2:=H); apply bpow_le.
omega.
fold u1 u2 alpha1.
now apply V2_Und2.
fold u1 u2 alpha1 alpha2.
now apply V2_Und4.
now apply V2_Und5.
Qed.

End ErrFMA_V2.
Section ErrFmaApprox.

Variable beta : radix.
Variable emin prec : Z.
Hypothesis precisionGe3 : (4 <= prec)%Z.
Context { prec_gt_0_ : Prec_gt_0 prec }.
Hypothesis emin_neg: (emin <= 0)%Z.

Notation format := (generic_format beta (FLT_exp emin prec)).
Notation round_flt :=(round beta (FLT_exp emin prec) ZnearestE).
Notation ulp_flt :=(ulp beta (FLT_exp emin prec)).

Lemma is_Fnormal: forall f, 
  Fcanonic (radix_val beta) (make_bound beta prec emin) f ->
   (bpow beta (emin+prec-1) <= Rabs (FtoR beta f))%R ->
   Fnormal (radix_val beta) (make_bound beta prec emin) f.
Proof.
intros f Cf Hf.
apply CanonicGeNormal with prec; try assumption.
apply make_bound_p; omega.
omega.
apply Rle_trans with (2:=Hf).
apply bpow_le.
rewrite make_bound_Emin; omega.
Qed.



(** inputs *)
Variable a x y:R.
Hypothesis Fa: format a.
Hypothesis Fx: format x.
Hypothesis Fy: format y.

(** algorithm *)
Let z := round_flt (a*x+y).
Let u1 := round_flt (a*x).
Let u2 := a*x-u1.
Let s1 := round_flt (y+u1).
Let s2 := (y+u1)-s1.
Let t := round_flt (s1-z).
Let v := round_flt (u2+s2).
Let z' := round_flt (t+v).

(** Non-underflow hypotheses *)
Hypothesis Und0: a * x = 0 \/ bpow beta (emin + 2 * prec - 1) <= Rabs (a * x).
Hypothesis Und1: z = 0 \/ bpow beta (emin + prec - 1) <= Rabs z.
Hypothesis Und2: u1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs u1.
Hypothesis Und3: s1 = 0 \/ bpow beta (emin + prec - 1) <= Rabs s1.
Hypothesis Und4: v = 0 \/ bpow beta (emin + prec - 1) <= Rabs v.
Hypothesis Und5: z' = 0 \/ bpow beta (emin + prec - 1) <= Rabs z'.


Theorem ErrFmaAppr_correct:
  (Rabs (z+z'-(a*x+y)) <= (3*beta/2+/2)*bpow beta (2-2*prec)*Rabs z)%R.
Proof with auto with typeclass_instances.
assert (precisionNotZero : (1 < prec)%Z) by omega.
assert (J1: format u2).
replace (u2) with (-(u1-(a*x))) by (unfold u2; ring).
apply generic_format_opp.
apply mult_error_FLT...
assert (J2: format s2).
replace (s2) with (-(s1-(y+u1))) by (unfold s2; ring).
apply generic_format_opp.
apply plus_error...
apply generic_format_round...
case (Req_dec (a*x) 0); intros Zax.
assert (L1:(z=y)%R).
unfold z; rewrite Zax, Rplus_0_l.
apply round_generic...
assert (L2:(z'=0)%R).
unfold z', t, v, s2, s1, u2.
replace u1 with 0.
rewrite L1, Zax, Rplus_0_r.
rewrite (round_generic _ _ _ y)...
replace (y-y) with 0 by ring.
rewrite Rminus_0_r, Rplus_0_l, round_0...
rewrite Rplus_0_l; apply round_0...
unfold u1; rewrite Zax, round_0...
rewrite L1, L2, Zax.
replace (y+0-(0+y)) with 0 by ring.
rewrite Rabs_R0; apply Rmult_le_pos.
2: apply Rabs_pos.
apply Rmult_le_pos.
2: apply bpow_ge_0.
apply Rplus_le_le_0_compat.
2: left; apply pos_half_prf.
apply Rmult_le_pos.
apply Rmult_le_pos.
apply Fourier_util.Rle_zero_pos_plus1.
left; apply Rlt_0_2.
left; rewrite <- Z2R_IZR; apply radix_pos.
left; apply pos_half_prf.
(* values *)
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero a)
  as (fa,(Hfa,Hfa')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero x)
  as (fx,(Hfx,Hfx')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero y)
  as (fy,(Hfy,Hfy')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero u2)
  as (fu2,(Hfu2,Hfu2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
destruct (format_is_pff_format beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero s2)
  as (fs2,(Hfs2,Hfs2')).
rewrite make_bound_Emin; try assumption.
replace (--emin)%Z with emin by omega; assumption.
rewrite <- Hfa, <- Hfx, <- Hfy.
(* roundings *)
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (a*x+y))
  as (fz,(Hfz, (Hfz',Hfz''))).
rewrite make_bound_Emin in Hfz''; try assumption.
replace (--emin)%Z with emin in Hfz'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (a*x))
  as (fu1,(Hfu1, (Hfu1',Hfu1''))).
rewrite make_bound_Emin in Hfu1''; try assumption.
replace (--emin)%Z with emin in Hfu1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (y+u1))
  as (fs1,(Hfs1, (Hfs1',Hfs1''))).
rewrite make_bound_Emin in Hfs1''; try assumption.
replace (--emin)%Z with emin in Hfs1'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (s1-z))
  as (ft,(Hft, (Hft',Hft''))).
rewrite make_bound_Emin in Hft''; try assumption.
replace (--emin)%Z with emin in Hft'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (u2+s2))
  as (fv,(Hfv, (Hfv',Hfv''))).
rewrite make_bound_Emin in Hfv''; try assumption.
replace (--emin)%Z with emin in Hfv'' by omega.
destruct (round_NE_is_pff_round beta (make_bound beta prec emin)
   prec (make_bound_p beta prec emin precisionNotZero) precisionNotZero (t+v))
  as (fzz,(Hfzz, (Hfzz',Hfzz''))).
rewrite make_bound_Emin in Hfzz''; try assumption.
replace (--emin)%Z with emin in Hfzz'' by omega.
unfold z; rewrite <- Hfz''.
unfold z'; rewrite <- Hfzz''.
rewrite bpow_powerRZ.
replace prec with ((Z.of_nat (Zabs_nat prec))%Z).
rewrite Z2R_IZR.
(* *)
apply ErrFmaApprox with (make_bound beta prec emin) fu1 fu2 fs1 fs2 ft fv; try assumption.
apply radix_gt_1.
apply make_bound_p; omega.
replace 4%nat with (Z.abs_nat 4).
apply Zabs_nat_le; omega.
now unfold Z.abs_nat, Pos.to_nat.
(* underflow *)
case Und2; intros K.
right; rewrite Hfu1''; fold u1; now rewrite K.
left; apply is_Fnormal; try assumption.
now rewrite Hfu1''.
case Und3; intros K.
right; rewrite Hfs1''; fold s1; now rewrite K.
left; apply is_Fnormal; try assumption.
now rewrite Hfs1''.
case Und1; intros K.
right; rewrite Hfz''; fold z; now rewrite K.
left; apply is_Fnormal; try assumption.
now rewrite Hfz''.
case Und5; intros K.
right; rewrite Hfzz''; fold z'; now rewrite K.
left; apply is_Fnormal; try assumption.
now rewrite Hfzz''.
case Und4; intros K.
right; rewrite Hfv''; fold v; now rewrite K.
left; apply is_Fnormal; try assumption.
now rewrite Hfv''.
apply underf_mult_aux with beta prec; try assumption.
apply make_bound_p; omega.
rewrite Hfa, Hfx.
case Und0; intros K.
now contradict K.
apply Rle_trans with (2:=K).
apply bpow_le.
rewrite make_bound_Emin; omega.
(* EO underflow *)
rewrite Hfa, Hfx, Hfy; apply Hfz'.
rewrite Hfa, Hfx; apply Hfu1'.
now rewrite Hfu2, Hfa, Hfx, Hfu1''.
rewrite Hfu1'', Hfy, Rplus_comm; apply Hfs1'.
rewrite Hfs2, Hfu1'', Hfy, Hfs1''.
unfold s2, s1, u1; ring.
rewrite Hfs1'', Hfz''; apply Hft'.
rewrite Hfu2, Hfs2; apply Hfv'.
rewrite Hft'', Hfv''; apply Hfzz'.
apply inj_abs; omega.
Qed.


End ErrFmaApprox.
