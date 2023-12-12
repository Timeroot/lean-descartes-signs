-- Copyright Alex Meiburg --
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Sign
import Mathlib.Data.List.Range
import Mathlib.Data.List.Destutter

import DesRoS.auxiliary_defs

--Defines "sign_variations", which counts how many times signs change in a polynomial's coefficients.
--This is used in Descarte's Rule of Signs.

namespace DesRoS

open Polynomial

section semiring
variable {α : Type*} [LinearOrderedSemiring α] (P : Polynomial α) {η : α} [DecidableEq α]

noncomputable def sign_variations : ℕ :=
    let coeff_signs := (coeffList P).map SignType.sign;
    let nonzero_signs := coeff_signs.filter (·≠0);
    (nonzero_signs.destutter (·≠·)).length - 1

theorem sign_var_zero (α : Type*) [LinearOrderedSemiring α] [DecidableEq α] : sign_variations (0:α[X]) = 0 :=
  by simp [sign_variations]

/-- Sign variations of a monomial are always zero. -/
theorem sign_var_monomial {d} {c : α} : sign_variations (monomial d c) = 0 := by
  by_cases hcz : c = 0
  case pos => simp [hcz, sign_variations]
  obtain ⟨c1, hc1⟩ := coeffList_eraseLead (mt (monomial_eq_zero_iff c d).mp hcz)
  simp only [hc1, sign_variations, List.filter, eraseLead_monomial, coeffList_zero,
    List.append_nil, List.map_replicate, List.filter_replicate]
  split <;> simp

end semiring
section field

-- many things we want to prove will actually require being over a DivisionSemiring, and/or Ring,
-- so we're going to upgrade the LinearOrderedSemiring to LinearOrderedField.
variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) {η : α} [DecidableEq α]

/-- The number of sign changes does not change if we multiply by a positive scalar -/
lemma sign_var_eq_sign_var_mul_pos (hη : η > 0) : sign_variations (C η * P) = sign_variations P := by
    -- sign_variations are the same ← the signs are the same
    dsimp [sign_variations]
    congr 3
    rw [coeffList_mul_C _ (lt_or_lt_iff_ne.mp (Or.inr hη))]
    rw [← List.comp_map]
    congr 2; funext; simp [hη, sign_mul]

/-- The number of sign changes does not change if we negate -/
theorem sign_var_eq_sign_var_neg : sign_variations (-P) = sign_variations P := by
    dsimp [sign_variations]
    rw [coeffList_neg]
    congr 1
    simp only [List.map_filter, ← List.comp_map]
    have hsc : ⇑SignType.sign ∘ (fun x:α => -x) = (fun x => -x)∘⇑SignType.sign := by {
      funext n
      simp [Left.sign_neg]
    }
    rw [← Function.comp.assoc, hsc, Function.comp.assoc, List.comp_map]
    have h_neg_destutter (l : List SignType) : (List.destutter (·≠·) l).map (λx↦-x) = List.destutter (·≠·) (l.map λx↦-x) := by
      apply List.destutter_map_of_iff ; simp
    rw [← h_neg_destutter, List.length_map]
    congr; funext x; simp

/-- The number of sign changes does not change if we multiply by any nonzero scalar -/
theorem sign_var_eq_sign_var_mul (hη : η ≠ 0) :
  sign_variations (C η * P) = sign_variations P := by
    by_cases hη2 : (η > 0)
    case pos =>
      exact sign_var_eq_sign_var_mul_pos P hη2
    case neg =>
      have hnegneg : (C (-η) * (-P)) = (C η * P) := by
        simp
      have h_neg_η_pos : ((-η) > 0) := by
        linarith (config := {splitNe := true})
      rw [← sign_var_eq_sign_var_neg P, ← hnegneg]
      exact sign_var_eq_sign_var_mul_pos (-P) h_neg_η_pos

/-- If the first two signs are the same, then sign_variations is unchanged by eraseLead -/
theorem sign_var_eq_eraseLead_of_eq_sign (h : SignType.sign (leadingCoeff P) = SignType.sign (nextCoeff P)) :
  sign_variations P = sign_variations P.eraseLead := by
  by_cases hpz : (P = 0)
  case pos => simp_all
  have : leadingCoeff P ≠ 0 := by simp_all
  have : nextCoeff P ≠ 0 := by intro; simp_all
  dsimp [sign_variations]
  rcases coeffList_eq_cons_leadingCoeff (ne_zero_eraseLead_of_nz_nextCoeff this) with ⟨ls, hls⟩
  rw [coeffList_eraseLead_nz this, hls, ← leadingCoeff_eraseLead_eq_nextCoeff this]
  simp_all [h, List.destutter]

/-- If we drop the leading coefficient, the sign changes by 0 or 1 depending on whether it matches
    leading coefficient of eraseLead. -/
theorem sign_var_eq_eraseLead_ite {P : Polynomial α} (h : P ≠ 0) : sign_variations P = sign_variations P.eraseLead +
  if SignType.sign (leadingCoeff P) = -SignType.sign (leadingCoeff P.eraseLead) then 1 else 0
 := by
  by_cases hpz : P = 0
  case pos => simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  dsimp [sign_variations]
  obtain ⟨nz, hc⟩ := coeffList_eraseLead hpz
  rw [hc, List.map_cons, List.map_append, List.map_replicate, List.filter, decide_eq_true hsl]
  simp only [decide_not, lt_self_iff_false, sign_zero, List.filter_append, List.filter_replicate]
  simp only [decide_True, Bool.not_true, ite_false, List.nil_append]
  cases hcep : (coeffList P.eraseLead)
  case neg.intro.nil =>
    have : eraseLead P = 0 := coeffList_nil hcep
    simp_all
  case neg.intro.cons c cs =>
    rw [List.map_cons, List.filter]
    by_cases hc2 : SignType.sign c = 0
    case pos =>
      have : eraseLead P = 0 := by
        by_contra h
        obtain ⟨l, hl⟩ := coeffList_eq_cons_leadingCoeff h
        rw [hcep] at hl
        simp [List.cons_inj] at hl
        rcases hl with ⟨ha, _⟩
        rw [sign_eq_zero_iff.mp hc2] at ha
        exact h (leadingCoeff_eq_zero.mp ha.symm)
      simp_all
    simp only [List.destutter, decide_eq_false hc2, Bool.not_false, List.destutter']
    have hel : eraseLead P ≠ 0 := by
      by_contra h; revert hcep
      rw [h, coeffList_zero]
      simp
    have hc4 : c = leadingCoeff P.eraseLead := by
      obtain ⟨ls,hls⟩ := coeffList_eq_cons_leadingCoeff hel
      cases (hcep ▸ hls); rfl
    by_cases hc3 : SignType.sign (leadingCoeff P) = SignType.sign c
    case pos =>
      cases hc6 : SignType.sign c <;> cases hl2 : SignType.sign (leadingCoeff P) <;> rw [hc6] at hc2 <;> simp_all
    case neg =>
      have hc5 : SignType.sign (leadingCoeff P) = -SignType.sign c := by
        cases hc6 : SignType.sign c <;> cases hl2 : SignType.sign (leadingCoeff P) <;> simp_all
      rw [if_pos hc3, ← hc4, if_pos hc5]
      rw [Nat.sub_add_cancel (List.destutter'_length_pos _ _)]
      simp

/-- We can only lose, not gain, sign changes if we drop the leading coefficient -/
theorem sign_var_ge_eraseLead : sign_variations P ≥ sign_variations P.eraseLead := by
  by_cases hpz : P = 0
  case pos => simp_all
  have := sign_var_eq_eraseLead_ite hpz
  by_cases SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff <;> simp_all

/-- We can only lose at most one sign changes if we drop the leading coefficient -/
theorem sign_var_le_eraseLead_succ : sign_variations P ≤ sign_variations P.eraseLead + 1 := by
  by_cases hpz : P = 0
  case pos => simp_all
  have := sign_var_eq_eraseLead_ite hpz
  by_cases SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff <;> simp_all

end field

end DesRoS
