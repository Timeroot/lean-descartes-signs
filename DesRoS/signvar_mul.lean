-- Copyright Alex Meiburg --
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Sign
import Mathlib.Data.List.Range
import Mathlib.Data.List.Destutter

import DesRoS.auxiliary_defs
import DesRoS.sign_variations

namespace DesRoS

--Proof the "major lemma" of Descartes' Rule of Signs, the multiplying a polynomial by a positive root
--adds at least one to the sign changes.

open Polynomial

variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) {η : α} [DecidableEq α]

--first, some lemmas.

--If P starts with [+,-,?...], then multiplying by (X-η) gives [+,-,?...] as well.
--Then P.eraseLead starts with [-,?...], and multiplying by (X-η) gives [-,?...].
lemma signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead
  (hη : η > 0) (hP₀ : leadingCoeff P > 0) (hP₁ : nextCoeff P < 0) :
  sign_variations (eraseLead ((X - C η) * P)) = sign_variations ((X - C η) * (eraseLead P)) := by
    --some facts. Start with writing P.natDegree = dp1 + 1.
    obtain ⟨dp1, hdp1⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nz_nextCoeff (ne_of_lt hP₁))
    rw [zero_add] at hdp1
    --other facts about degrees and high-order terms
    have hPn0 : P ≠ 0 :=
      (leadingCoeff_ne_zero.mp (ne_of_gt hP₀))
    have hePn0 : P.eraseLead ≠ 0 :=
      ne_zero_eraseLead_of_nz_nextCoeff (ne_of_lt hP₁)
    have hndxP : natDegree ((X - C η) * P) = natDegree P + 1 := by
      rw [natDegree_mul (X_sub_C_ne_zero η) hPn0, natDegree_X_sub_C, add_comm]
    have hndxeP : natDegree ((X - C η) * P.eraseLead) = natDegree P := by
      rw [natDegree_mul (X_sub_C_ne_zero η) hePn0, natDegree_X_sub_C, add_comm]
      exact (eraseLead_natDegree_of_nextCoeff (ne_of_lt hP₁)).symm
    have hndeP0 : natDegree ((X - C η) * P.eraseLead) > 0 :=
      Nat.lt_of_sub_eq_succ (hdp1 ▸ hndxeP)
    have hQ : nextCoeff ((X-C η)*P) = coeff P dp1 - coeff P (dp1 + 1) * η := by
      rw [nextCoeff_of_pos_natDegree _ (hndxP ▸ P.natDegree.succ_pos)]
      rw [hndxP, hdp1, Nat.add_sub_cancel, mul_comm, coeff_mul_X_sub_C]
    have hQ₁ : nextCoeff ((X-C η)*P) < 0 := by
      rw [leadingCoeff, hdp1] at hP₀
      rw [nextCoeff_of_pos_natDegree _ (hdp1 ▸ dp1.succ_pos), hdp1, Nat.add_sub_cancel] at hP₁
      have := mul_pos hP₀ hη
      linarith
    have hndexP0 : natDegree (eraseLead ((X - C η) * P)) = natDegree P := by
      apply @Nat.add_right_cancel _ 1
      rw [← hndxP, eraseLead_natDegree_of_nextCoeff (ne_of_lt hQ₁)]
    have hQe₁ : leadingCoeff ((X-C η)*P.eraseLead) < 0 := by
      rwa [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, ← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_lt hP₁)]
    --the theorem is true mainly because all the signs are the same; in fact, the coefficients are all the same
    --except the first.
    suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * (eraseLead P)) by
      suffices (coeffList (eraseLead ((X - C η) * P))).map SignType.sign =
        (coeffList ((X - C η) * (eraseLead P))).map SignType.sign by
          dsimp [sign_variations]
          rw [this]
      obtain ⟨n1, hn1⟩ := coeffList_eraseLead (ne_zero_eraseLead_of_nz_nextCoeff (ne_of_lt hQ₁))
      obtain ⟨n2, hn2⟩ := coeffList_eraseLead (ne_zero_of_natDegree_gt hndeP0)
      have hn1n2 : n1 = n2 := by
        have hl1 : (eraseLead ((X - C η) * P)).coeffList.length = _ := by rfl
        have hl2 : ((X - C η) * eraseLead P).coeffList.length = _ := by rfl
        nth_rewrite 1 [hn1, this] at hl1
        nth_rewrite 1 [hn2] at hl2
        rw [length_coeffList] at hl1 hl2
        have : eraseLead ((X - C η) * P) ≠ 0 := by
          apply ne_zero_of_natDegree_gt
          rw [hndexP0, hdp1]
          exact Nat.lt.base dp1
        rw [if_neg this, hndexP0] at hl1
        rw [if_neg (leadingCoeff_ne_zero.mp (ne_of_lt hQe₁)), hndxeP] at hl2
        simp only [List.length_cons, List.length_append, List.length_replicate] at hl1 hl2
        linarith
      rw [hn1, hn2, List.map_cons, List.map_cons, ← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_lt hQ₁)]
      rw [sign_neg hQ₁, sign_neg hQe₁, hn1n2, this]
    rw [← self_sub_monomial_natDegree_leadingCoeff, hndexP0, ← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_lt hQ₁)]
    rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η)]
    rw [← self_sub_monomial_natDegree_leadingCoeff, leadingCoeff_monic_mul (monic_X_sub_C η), hndxeP, hndxP]
    rw [← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_lt hP₁), ← self_sub_monomial_natDegree_leadingCoeff]
    rw [hQ, mul_sub, sub_mul, sub_mul, X_mul_monomial, C_mul_monomial, monomial_sub]
    rw [leadingCoeff, nextCoeff_of_pos_natDegree _ (hdp1 ▸ dp1.succ_pos), hdp1, Nat.add_sub_cancel, mul_comm η _]
    ring

end DesRoS
