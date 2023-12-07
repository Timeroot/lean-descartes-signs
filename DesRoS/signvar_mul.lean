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

--this is true also without the first hypothesis, but that's considerably more annoying to prove.
lemma signvar_X_sub_C_ge_eraseLead_of_nextCoeff_nz (h : nextCoeff P ≠ 0) (hη : η > 0)
  (h₁ : leadingCoeff P > 0) (h₂ : nextCoeff P > 0) :
  sign_variations ((X - C η) * P) ≥ sign_variations ((X - C η) * (eraseLead P)) := by
    sorry

lemma signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead
  (hη : η > 0) (hP₀ : leadingCoeff P > 0) (hP₁ : nextCoeff P < 0) (hQ₀ : leadingCoeff ((X-C η)*P) > 0) :
  sign_variations (eraseLead ((X - C η) * P)) = sign_variations ((X - C η) * (eraseLead P)) := by
    sorry

--specialization of the final theorem for monomials
lemma succ_sign_lin_mul_monomial {d c} (hqz : Q ≠ 0) (hη : η > 0) (hm : Q = monomial d c) :
  sign_variations ((X - C η) * Q) ≥ sign_variations Q + 1 := by
    suffices sign_variations ((X - C η) * Q) ≥ 1 by
      have : sign_variations Q + 1 = 1 := by rw [hm, sign_var_monomial]
      linarith
    have hc : c ≠ 0 := by
      by_contra hc;
      exact hqz ((hc ▸ hm) ▸ monomial_zero_right d)
    dsimp [sign_variations]
    have h₀ : leadingCoeff ((X - C η) * Q) = c := by rw [hm]; simp
    have h₁ : natDegree ((X - C η) * (monomial d c)) = d + 1 := by
      rw [natDegree_mul (X_sub_C_ne_zero η) (hm ▸ hqz), natDegree_X_sub_C, natDegree_monomial, if_neg hc, add_comm]
    have h₂ : nextCoeff ((X - C η) * Q) = -(c*η) := by
      rw [hm, nextCoeff, h₁];
      simp? says simp only [add_eq_zero, one_ne_zero, and_false, ge_iff_le, add_le_iff_nonpos_left,
        nonpos_iff_eq_zero, add_tsub_cancel_right, ite_false]
      nth_rewrite 2 [← zero_add d]
      rw [mul_comm, coeff_monomial_mul]
      simp
    have h₃ : nextCoeff ((X - C η) * Q) ≠ 0 := h₂ ▸ (neg_ne_zero.mpr (mul_ne_zero hc (ne_of_gt hη)))
    have this : eraseLead ((X - C η) * Q) ≠ 0 := ne_zero_eraseLead_of_nz_nextCoeff h₃
    rw [coeffList_eraseLead_nz h₃]
    obtain ⟨rs, hrs⟩ := coeffList_eraseLead this
    rw [hrs]
    rw [← leadingCoeff_eraseLead_eq_nextCoeff h₃, h₀, h₂]
    have hds : SignType.sign c ≠ SignType.sign (-(c*η)) := by
      simp [sign_pos hη, Left.sign_neg, sign_mul]
      exact hc
    rw [List.map_cons, List.map_cons, List.filter, List.filter]
    simp only [sign_eq_zero_iff, hc, not_false_eq_true, decide_True,
      Left.neg_neg_iff, neg_eq_zero, mul_eq_zero, or_self, decide_not,
      sign_zero, List.filter_append, ne_of_gt hη]
    rw [List.destutter_cons_cons, if_pos hds, List.length_cons]
    apply List.destutter'_length_pos

--if we erase the leading coefficient of a coeffList like [+,0,...], and then multiply by a linear term,
--it's equivalent to erasing the first two coefficients of the product.
lemma eraseLead_two_mul_eq_mul_eraseLead_of_nextCoeff_zero
  (hη : η ≠ 0) (h : nextCoeff P = 0) :
  eraseLead (eraseLead ((X - C η) * P)) = (X - C η) * (eraseLead P) := by
    --can assume P ≠ 0
    by_cases hpz : P = 0
    case pos => simp_all
    case neg => {
      -- degree of (X - C η) * P is one more than degree of P
      have h₁ : natDegree ((X - C η) * P) = natDegree P + 1 := by
        rw [natDegree_mul (X_sub_C_ne_zero η) hpz, natDegree_X_sub_C, add_comm]
      --can assume eraseLead P > 0
      by_cases hez : eraseLead P = 0
      case pos =>
        rw [hez, mul_zero]
        by_cases hez2 : eraseLead ((X - C η) * P) = 0
        case pos => rw [hez2]; simp
        apply card_support_eq_zero.mp
        have := eraseLead_support_card_lt hez2
        have : Finset.card (support (eraseLead ((X - C η) * P))) < Finset.card (support ((X - C η) * P)) := by
          apply eraseLead_support_card_lt
          exact mul_ne_zero (X_sub_C_ne_zero η) hpz
        have : Finset.card (support ((X - C η) * P)) ≤ 2 := by
          have hmul := card_support_mul (X - C η) P
          have hp1 := card_support_lt_one_of_eraseLead_zero hez
          suffices (X - C η).support.card = 2 by
            rw [this] at hmul
            linarith
          have : (C 1 * X ^ 1 + C (-η) * X ^ 0).support.card = 2 :=
            card_support_binomial one_ne_zero one_ne_zero (neg_ne_zero.mpr hη)
          simp at this
          rwa [← sub_eq_add_neg] at this
        linarith
      case neg => {
        -- natDegree P ≥ 2
        obtain ⟨dP, hdP⟩ := Nat.exists_eq_add_of_le (natDegree_ge_2_of_nextCoeff_eraseLead hez h)
        rw [add_comm] at hdP
        --turn "nextCoeff P = 0" into "coeff P dP = 0"
        have h₂ := h
        simp only [nextCoeff, hdP, Nat.succ_ne_zero, one_ne_zero,
          add_tsub_cancel_right, ite_false, Nat.succ_sub_succ_eq_sub, tsub_zero] at h₂
        -- the subleading term of (X - C η) * P is nonzero
        have h₂ : nextCoeff ((X - C η) * P) ≠ 0 := by
          rw [nextCoeff, h₁, mul_comm, hdP]
          simp only [Nat.succ_ne_zero, one_ne_zero, add_tsub_cancel_right, ite_false]
          rw [coeff_mul_X_sub_C, h₂]
          simp only [ne_eq, zero_sub, neg_eq_zero, mul_eq_zero, not_or]
          constructor
          rw [← Nat.succ_eq_add_one, ← Nat.add_succ, ← hdP, ← leadingCoeff]
          exact mt leadingCoeff_eq_zero.mp hpz
          exact hη
        -- the product is one degree higher than P
        have h₃ := eraseLead_natDegree_of_nextCoeff h₂
        -- prove equality by showing all the coefficients are equal
        apply Polynomial.ext; intro n
        -- divide into three cases: low degree, degree equal to P, or higher than P
        rcases Nat.lt_or_ge n (natDegree P) with hn | hn
        case _ => { --n < natDegree P
          rw [← self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial]
          have : natDegree (eraseLead ((X - C η) * P)) ≠ n := by apply ne_of_gt; linarith
          rw [if_neg this]
          rw [← self_sub_monomial_natDegree_leadingCoeff, coeff_sub, coeff_monomial]
          have : natDegree ((X - C η) * P) ≠ n := by apply ne_of_gt; linarith
          rw [if_neg this]
          rw [← self_sub_monomial_natDegree_leadingCoeff, mul_sub, coeff_sub]
          --dunno the name of the right cancellation lemma here
          suffices coeff ((X - C η) * (monomial (natDegree P)) (leadingCoeff P)) n = 0 by linarith
          cases hn2 : n
          case zero =>
            rw [mul_coeff_zero]
            apply mul_eq_zero_of_right
            rw [coeff_monomial]
            split; by_contra; linarith
            rfl
          case succ n2 =>
            have : (natDegree P) ≠ n2.succ := hn2 ▸ ne_of_gt hn
            rw [mul_comm, coeff_mul_X_sub_C, coeff_monomial, coeff_monomial, if_neg this, zero_mul]
            split; by_contra; linarith
            exact sub_zero 0
        }
        case _ => { --n ≥ natDegree P
          have h₄ : natDegree (eraseLead (eraseLead ((X - C η) * P))) < n := by
            calc natDegree (eraseLead (eraseLead ((X - C η) * P)))
              _ ≤ natDegree (eraseLead ((X - C η) * P)) - 1 := eraseLead_natDegree_le (eraseLead ((X - C η) * P))
              _ ≤ (natDegree ((X - C η) * P) - 1) - 1 := Nat.sub_le_sub_right (eraseLead_natDegree_le ((X - C η) * P)) 1
              _ = (natDegree P + 1) - 2 := by rw [h₁]; norm_num
              _ < natDegree P := by rw [hdP]; norm_num
              _ ≤ n := hn
          have h₅ : natDegree ((X - C η) * (eraseLead P)) < n := by calc
            natDegree ((X - C η) * (eraseLead P)) = 1 + natDegree (eraseLead P) := by
                rw [natDegree_mul (X_sub_C_ne_zero η), natDegree_X_sub_C]; rwa [ne_eq]
            _ ≤ 1 + (natDegree P - 2) := (add_le_add_iff_left 1).mpr (eraseLead_natDegree_of_zero_nextCoeff h)
            _ < natDegree P := by rw [hdP, add_comm]; norm_num;
            _ ≤ n := hn
          rw [coeff_eq_zero_of_natDegree_lt h₄, coeff_eq_zero_of_natDegree_lt h₅]
        }
      }
    }

end DesRoS
