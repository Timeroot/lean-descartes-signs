-- Copyright Alex Meiburg --
import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Sign
import Mathlib.Data.List.Range
import Mathlib.Data.List.Destutter

import DesRoS.auxiliary_defs

--Here starts stuff more specific to Descartes' Rule of Signs
open Polynomial

namespace DesRoS

variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) {η : α} [DecidableEq α]

noncomputable def sign_variations : ℕ :=
    let coeff_signs := (coeffList P).map SignType.sign;
    let nonzero_signs := coeff_signs.filter (·≠0);
    (nonzero_signs.destutter (·≠·)).length - 1

/-- The number of sign changes does not change if we multiply by a positive scalar -/
lemma sign_var_eq_sign_var_mul_pos (hη : η > 0) : sign_variations (C η * P) = sign_variations P := by
    -- sign_variations are the same ← the signs are the same
    dsimp [sign_variations]
    congr 3
    rw [coeffList_mul_C _ (lt_or_lt_iff_ne.mp (Or.inr hη))]
    rw [← List.comp_map]
    congr 2; funext; simp [hη, sign_mul]

/-- The number of sign changes does not change if we negate -/
lemma sign_var_eq_sign_var_neg : sign_variations (-P) = sign_variations P := by
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
lemma sign_var_eq_sign_var_mul (hη : η ≠ 0) :
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
  sign_variations P = sign_variations (eraseLead P) := by
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
theorem sign_var_le_eraseLead_ite (h : P ≠ 0) : sign_variations P = sign_variations (eraseLead P) +
  if SignType.sign (leadingCoeff P) = -SignType.sign (leadingCoeff (eraseLead P)) then 1 else 0
 := by
  by_cases hpz : P = 0
  case pos => simp_all
  have hsl : SignType.sign (leadingCoeff P) ≠ 0 := by simp_all
  dsimp [sign_variations]
  obtain ⟨nz, hc⟩ := coeffList_eraseLead hpz
  rw [hc, List.map_cons, List.map_append, List.map_replicate, List.filter, decide_eq_true hsl]
  simp only [decide_not, lt_self_iff_false, sign_zero, List.filter_append, List.filter_replicate]
  simp only [decide_True, Bool.not_true, ite_false, List.nil_append]
  cases hcep : (coeffList (eraseLead P))
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
    have hc4 : c = leadingCoeff (eraseLead P) := by
      obtain ⟨ls,hls⟩ := coeffList_eq_cons_leadingCoeff hel
      cases (hcep ▸ hls); rfl
    by_cases hc3 : SignType.sign (leadingCoeff P) = SignType.sign c
    case pos =>
      cases hc6 : SignType.sign c <;> cases hl2 : SignType.sign (leadingCoeff P) <;> rw [hc6] at hc2 <;> simp_all
    case neg =>
      have hc5 : SignType.sign (leadingCoeff P) = -SignType.sign c := by
        cases hc6 : SignType.sign c <;> cases hl2 : SignType.sign (leadingCoeff P) <;> simp_all
      rw [if_pos hc3, ← hc4, if_pos hc5]
      rw [← Nat.sub_add_of_ge (List.destutter'_length_pos _ _)]
      simp

/-- We can only lose, not gain, sign changes if we drop the leading coefficient -/
theorem sign_var_ge_eraseLead : sign_variations P ≥ sign_variations (eraseLead P) := by
  by_cases hpz : P = 0
  case pos => simp_all
  have := sign_var_le_eraseLead_ite P
  by_cases SignType.sign (leadingCoeff P) = -SignType.sign (leadingCoeff (eraseLead P)) <;> simp_all

/-- We can only lose at most one sign changes if we drop the leading coefficient -/
theorem sign_var_le_eraseLead_succ : sign_variations P ≤ sign_variations (eraseLead P) + 1 := by
  by_cases hpz : P = 0
  case pos => simp_all
  have := sign_var_le_eraseLead_ite P
  by_cases SignType.sign (leadingCoeff P) = -SignType.sign (leadingCoeff (eraseLead P)) <;> simp_all

/-- Multiplying by (X-η) adds at least one sign change -/
theorem succ_sign_lin_mul (hη : η > 0) {d : ℕ} (hq : Q ≠ 0) (hd : d = Q.natDegree):
  sign_variations ((X - C η) * Q) >= sign_variations Q + 1 := by
    --do induction on the degree
    induction' d using Nat.strong_induction_on with d ih generalizing Q
    --we can assume Q's highest coefficient is positive
    suffices h : ∀ Q, (Q ≠ 0) → (d = Q.natDegree) → (leadingCoeff Q > 0) →
      (sign_variations ((X - C η) * Q) >= sign_variations Q + 1) by
      by_cases hsq : leadingCoeff Q > 0
      case pos => exact h Q hq hd hsq
      have hsqn0 : leadingCoeff Q ≠ 0 := mt leadingCoeff_eq_zero.mp hq
      have nsqneg : leadingCoeff Q < 0 := by clear hq; linarith (config := {splitNe := true})
      have hnq0 : (-Q)≠0 := by simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, neg_eq_zero, hd]
      have hndQ : d = (-Q).natDegree := by simpa only [natDegree_neg]
      have : leadingCoeff (-Q) > 0 := by simpa only [leadingCoeff_neg, gt_iff_lt, Left.neg_pos_iff]
      have := h (-Q) hnq0 hndQ this
      simp only [mul_neg, sign_var_eq_sign_var_neg] at this
      exact this
    --clear the old hypotheses and use our fresh stronger ones from suffices
    clear Q hq hd
    intro Q hq hd hqpos
    --the new polynomial isn't zero
    have hnzηQ : (X - C η) * Q ≠ 0 := mul_ne_zero (X_sub_C_ne_zero η) hq
    --LHS is one degree higher than RHS
    have hdQ : natDegree ((X - C η) * Q) = natDegree Q + 1 := by
      rw [natDegree_mul, natDegree_X_sub_C, add_comm]
      exact X_sub_C_ne_zero η
      assumption
    by_cases hd0 : (d=0)
    case pos --zero degree
    {
      simp only [hd0] at *
      have hQ : Q = C (coeff Q 0) := by
        exact eq_C_of_degree_le_zero (natDegree_eq_zero_iff_degree_le_zero.mp hd.symm)
      have hcQ : coeff Q 0 ≠ 0 := by
        by_contra'
        rw [this, map_zero] at hQ
        exact hq hQ
      have hxcQ : coeff ((X - C η) * Q) 1 = coeff Q 0 := by
        have : coeff Q 1 = 0 := by
          apply coeff_eq_zero_of_natDegree_lt
          rw [← hd]
          exact zero_lt_one
        rw [mul_comm, coeff_mul_X_sub_C, sub_eq_self, this, zero_mul]
      simp only [sign_variations, coeffList, if_neg hq, if_neg hnzηQ,
        decide_not, hdQ, ← hd, List.range_succ, sign_eq_zero_iff, List.filter]
      simp [hcQ, hxcQ, ne_of_gt hη, Left.sign_neg, sign_mul, sign_pos hη]
    }
    case neg --positive degree
    {
      --clean up the messy state from the strong induction -- eugh!
      have : ∃ d0, d = d0 + 1 := by
        cases d; tauto; case succ n => use n
      rcases this with ⟨d,hn⟩
      rw [hn] at hd0 hd ih
      clear hn

      -- simp [sign_variations, coeffList]
      -- rw [hdQ, ←hd]
      -- rw [List.range_succ, List.range_succ, List.range_succ, List.range_succ] -- exactly 4 times, not 5
      -- simp only [List.append_assoc, List.singleton_append, List.reverse_append, List.reverse_cons,
      --   List.reverse_nil, List.nil_append, List.cons_append, List.map_cons, Function.comp_apply]

      set sq0 := SignType.sign (leadingCoeff Q) with hsq0
      set sq1 := SignType.sign (nextCoeff Q) with hsq1
      set sηq0 := SignType.sign (leadingCoeff ((X - C η) * Q)) with hsηq0
      set sηq1 := SignType.sign (nextCoeff ((X - C η) * Q)) with hsηq1

      have h_sq0_pos : sq0 = 1 := by
        -- rw [hsq0, hd, ← leadingCoeff]
        -- exact sign_pos hqpos
        sorry

      have h_sq0_sηq0 : sq0 = sηq0 := by
        -- have : coeff Q (d + 1 + 1) = 0 := by
        --   rw [hd]
        --   apply coeff_natDegree_succ_eq_zero
        -- rw [hsq0, hsηq0, mul_comm, coeff_mul_X_sub_C, this, zero_mul, sub_zero]
        sorry

      have hnDeQ : natDegree (eraseLead Q) < d + 1 :=
        Nat.succ_le_succ (add_tsub_cancel_right d 1 ▸ hd ▸ (eraseLead_natDegree_le Q))

      -- rw [← h_sq0_sηq0, h_sq0_pos]

      by_cases hcsq1 : (sq1 = 0)
      case pos => {
        -- Q starts with [+,0,...] so LQ starts with [+,-,...].
        have hcsηq1 : sηq1 = -1 := by
          sorry

        --TODO this isn't actually true, could have Q = C * X^n, gotta handle that separately.
        have h_eQ_nz : eraseLead Q ≠ 0 := by
          sorry

        -- rw [hcsq1, hcsηq1]
        -- simp only [gt_iff_lt, one_ne_zero, decide_False, Bool.not_false, List.filter_cons_of_pos,
        --   sign_eq_zero_iff, Bool.not_eq_true', decide_eq_false_iff_not, not_not]

        -- Dropping the lead of Q exactly drops the first two of LQ.
        -- This decreases the sign variations of LQ by at least one, and Q by at most one, so we can induct.
        have h_elMul : eraseLead (eraseLead ((X - C η) * Q)) = (X - C η) * (eraseLead Q) := by
          sorry
        have h_e2Q : sign_variations (eraseLead Q) + 1 ≥ sign_variations Q := by
          exact sign_var_le_eraseLead_succ Q
        have h_e2LQ : sign_variations (eraseLead (eraseLead ((X - C η) * Q))) + 1 ≤ sign_variations ((X - C η) * Q) := by
          sorry
        have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
          exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl
        rw [h_elMul] at h_e2LQ
        linarith
      }
      case neg => {
        have h_eQ_nz : eraseLead Q ≠ 0 := by
          sorry

        by_cases hcsq1' : (sq1 > 0)
        case pos => {
          -- Q starts with [+,+,...]. LQ starts with [+,?,...].
          -- After dropping the lead of Q, this becomes [+,...] and [+,...].
          -- So the sign variations on Q are unchanged when we induct, while LQ can only lose a sign change.
          have h_eQ : sign_variations (eraseLead Q) = sign_variations (Q) := by
            sorry
          have h_eLQ : sign_variations ((X - C η) * (eraseLead Q)) ≤ sign_variations ((X - C η) * Q) := by
            sorry
          have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
            exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl
          linarith
        }
        case neg => {
          -- Q starts with [+,-,...], so LQ starts with [+,-,...].
          -- After dropping the lead of Q, this becomes [-,...] and [-,...].
          -- Dropping the first one of each decreases LQ by one and Q by one, so we can induct.
          have h_eQ : sign_variations (eraseLead Q) = sign_variations (Q) + 1 := by
            sorry
          have h_eLQ : sign_variations (eraseLead ((X - C η) * Q)) = sign_variations ((X - C η) * Q) + 1:= by
            sorry
          have h_eLQ2 : sign_variations ((X - C η) * (eraseLead Q)) = sign_variations (eraseLead ((X - C η) * Q)):= by
            sorry
          have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
            exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl
          linarith
        }
      }
    }

/-- Descartes' Rule of Signs: the number of positive roots is at most the number of sign variations. -/
theorem descartes_rule_of_signs (num_pos_roots : ℕ) (h : num_pos_roots = P.roots.countP (λ x ↦ x > 0)) :
  num_pos_roots ≤ sign_variations P := by
    induction num_pos_roots generalizing P
    case zero --zero roots: it's trivial that zero roots is at most the number of variations.
    {
      rw [Nat.zero_eq]; exact zero_le (sign_variations P)
    }
    case succ--otherwise induction on number of roots.
    num_roots_m1 hnroots => {
      -- P is nonzero
      have hp : P ≠ 0 := by
        intro hpz
        rw [hpz] at h
        simp at h
      -- we can take a positive root, η, because the number of roots is > 0
      have hx : ∃ x, x ∈ P.roots ∧ (λ x ↦ x > 0) x := by
        simp only [← Multiset.countP_pos, ← h, Nat.zero_lt_succ]
      rcases hx with ⟨η, ⟨η_root, η_pos⟩⟩
      -- (X - α) divies P(X), so write P(X) = (X - α) * Q(X)
      have hd : (X - C η ∣ P) := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
      rcases hd with ⟨Q, hq⟩
      -- Q is nonzero
      have hq_nz : Q ≠ 0 := by
        intro hq2; rw [hq2, mul_zero] at hq
        exact hp hq
      -- Q has one less positive root than P
      have q_roots_m1 : num_roots_m1 = Q.roots.countP (λ x ↦ x > 0) := by {
        --roots of P is the root of X-η together with Q
        have hpηq : P.roots = (X - C η).roots + Q.roots := by {
          rw [hq]
          apply roots_mul
          rw [← hq]
          exact ne_zero_of_mem_roots η_root
        }
        rw [← Nat.succ.injEq]
        rw [h, hpηq, Multiset.countP_add, roots_X_sub_C]
        rw [← Multiset.cons_zero, Multiset.countP_cons, if_pos η_pos]
        rw [Multiset.countP_zero, zero_add, add_comm]
      }
      -- by inductive hypothesis, Q has at least num_roots - 1 sign changes
      have q_signvar : num_roots_m1 ≤ sign_variations Q := hnroots Q q_roots_m1
      -- P has at least num_roots sign variations
      rw [hq]
      calc
        Nat.succ num_roots_m1 = num_roots_m1 + 1 := by rfl
        _ ≤ sign_variations Q + 1 := by simp only [add_le_add_iff_right, q_signvar]
        _ ≤ sign_variations ((X - C η) * Q) := succ_sign_lin_mul η_pos hq_nz rfl
    }
