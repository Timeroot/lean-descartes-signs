import DesRoS.signvar_mul

namespace DesRoS

open Polynomial
variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) {η : α} [DecidableEq α]

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

      set sq0 := SignType.sign (leadingCoeff Q) with hsq0
      set sq1 := SignType.sign (nextCoeff Q) with hsq1
      set sηq0 := SignType.sign (leadingCoeff ((X - C η) * Q)) with hsηq0
      set sηq1 := SignType.sign (nextCoeff ((X - C η) * Q)) with hsηq1

      have h_sq0_pos : sq0 = 1 := hsq0 ▸ sign_pos hqpos

      have h_sq0_sηq0 : sq0 = sηq0 := by
        rw [hsq0, hsηq0, leadingCoeff, leadingCoeff, hdQ, mul_comm,
            coeff_mul_X_sub_C, coeff_natDegree_succ_eq_zero, zero_mul, sub_zero]

      have hnDeQ : natDegree (eraseLead Q) < d + 1 :=
        Nat.succ_le_succ (add_tsub_cancel_right d 1 ▸ hd ▸ (eraseLead_natDegree_le Q))

      have : coeff Q (d + 1) * η > 0 := by
        apply mul_pos _ hη
        rw [hd]
        rw [leadingCoeff, h_sq0_pos] at hsq0
        exact sign_eq_one_iff.mp hsq0.symm

      cases hcsq1 : sq1
      case _ => { --zero
        -- Q starts with [+,0,...] so LQ starts with [+,-,...].
        have hcsηq1 : sηq1 = -1 := by
          have : coeff Q d = 0 := by
            rw [(Nat.sub_eq_of_eq_add hd.symm).symm]
            simp [nextCoeff, hcsq1, hd ▸ hd0] at hsq1
            exact sign_eq_zero_iff.mp hsq1.symm
          apply sign_eq_neg_one_iff.mpr
          rw [nextCoeff, natDegree_mul (X_sub_C_ne_zero η) hq, natDegree_X_sub_C]
          simp only [add_eq_zero, one_ne_zero, false_and, add_tsub_cancel_left, ite_false]
          rw [mul_comm, ← hd, coeff_mul_X_sub_C]
          linarith

        have h_nc_nz : nextCoeff ((X - C η) * Q) ≠ 0 := by
          apply sign_ne_zero.mp
          rw [← hsηq1, hcsηq1]
          simp

        have h_nc_le : nextCoeff ((X - C η) * Q) = leadingCoeff (eraseLead ((X - C η) * Q)) :=
          leadingCoeff_eraseLead_eq_nextCoeff h_nc_nz

        -- Dropping the lead of Q exactly drops the first two of LQ.
        -- This decreases the sign variations of LQ by at least one, and Q by at most one, so we can induct.
        have h_elMul : eraseLead (eraseLead ((X - C η) * Q)) = (X - C η) * (eraseLead Q) := by
          apply eraseLead_two_mul_eq_mul_eraseLead_of_nextCoeff_zero
          exact ne_of_gt hη
          exact sign_eq_zero_iff.mp (SignType.zero_eq_zero ▸ hcsq1 ▸ hsq1)

        have h_e2Q : sign_variations (eraseLead Q) + 1 ≥ sign_variations Q := by
          exact sign_var_le_eraseLead_succ Q

        have h_e2LQ : sign_variations (eraseLead (eraseLead ((X - C η) * Q))) ≤ sign_variations (eraseLead ((X - C η) * Q)) :=
          sign_var_ge_eraseLead (eraseLead ((X - C η) * Q))

        have h_e3LQ : sign_variations (eraseLead ((X - C η) * Q)) + 1 = sign_variations ((X - C η) * Q) := by
          rw [sign_var_eq_eraseLead_ite hnzηQ, ← h_nc_le, ← hsηq1, ← hsηq0, hcsηq1, ← h_sq0_sηq0, h_sq0_pos]
          simp

        --we would like to just `have : eraseLead Q ≠ 0`, so that we can use the inductive hypothesis on eraseLead Q.
        --but that isn't actually true: we could have Q = C * X^n, and then eraseLead Q = 0, and then the inductive hypothesis
        --doesn't hold. (It's only true as written for Q ≠ 0.) So we need to do a case-split and handle this separately.
        by_cases h_eQ_nz : eraseLead Q = 0
        case neg =>
          have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
            exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl

          rw [h_elMul] at h_e2LQ
          linarith

        case pos =>
          --this is the edge case where eraseLead Q = 0. Therefore, Q is a monomial.
          have hq_mono : Q = monomial (Q.natDegree) (leadingCoeff Q) := by
            have := (eraseLead_add_monomial_natDegree_leadingCoeff Q).symm
            rwa [h_eQ_nz, zero_add] at this
          exact succ_sign_lin_mul_monomial hq hη hq_mono
      }
      case _ => {--neg
        -- Q starts with [+,-,...], so LQ starts with [+,-,...].
        -- After dropping the lead of Q, this becomes [-,...] and [-,...].
        -- Dropping the first one of each decreases LQ by one and Q by one, so we can induct.

        have h_nc_nz : nextCoeff Q ≠ 0 := by
          apply sign_ne_zero.mp
          rw [← hsq1, hcsq1]
          simp

        have h_eQ_nz : eraseLead Q ≠ 0 :=
          ne_zero_eraseLead_of_nz_nextCoeff h_nc_nz

        have h_nc_eq : nextCoeff Q = leadingCoeff (eraseLead Q) :=
          leadingCoeff_eraseLead_eq_nextCoeff h_nc_nz

        have hcsηq1 : sηq1 = -1 := by
          have : coeff Q d < 0 := by
            rw [(Nat.sub_eq_of_eq_add hd.symm).symm]
            simp [nextCoeff, hcsq1, hd ▸ hd0] at hsq1
            exact sign_eq_neg_one_iff.mp hsq1.symm
          apply sign_eq_neg_one_iff.mpr
          rw [nextCoeff, natDegree_mul (X_sub_C_ne_zero η) hq, natDegree_X_sub_C]
          simp only [add_eq_zero, one_ne_zero, false_and, add_tsub_cancel_left, ite_false]
          rw [mul_comm, ← hd, coeff_mul_X_sub_C]
          linarith

        have h_ncη_lz : nextCoeff ((X - C η) * Q) = leadingCoeff (eraseLead ((X - C η) * Q)) := by
          apply leadingCoeff_eraseLead_eq_nextCoeff
          intro h
          have := (h ▸ hsηq1) ▸ hcsηq1
          simpa

        have h_eLQ : sign_variations ((X - C η) * Q) = sign_variations (eraseLead ((X - C η) * Q)) + 1:= by
          rw [sign_var_eq_eraseLead_ite hnzηQ]
          rw [← hsηq0, ← h_sq0_sηq0, ← h_ncη_lz, ← hsηq1, hcsηq1, h_sq0_pos]
          simp

        have h_eLQ2 : sign_variations (eraseLead ((X - C η) * Q)) = sign_variations ((X - C η) * (eraseLead Q)):= by
          apply signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead Q hη hqpos
          exact sign_eq_neg_one_iff.mp (SignType.neg_eq_neg_one ▸ hcsq1 ▸ hsq1)
          exact sign_eq_one_iff.mp (h_sq0_pos ▸ h_sq0_sηq0 ▸ hsηq0)

        have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
          exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl

        have h_eQ : sign_variations (eraseLead Q) + 1 = sign_variations (Q) := by
          rw [sign_var_eq_eraseLead_ite hq]
          rw [← h_nc_eq, ← hsq0, ← hsq1, h_sq0_pos, hcsq1]
          simp

        linarith
      }
      case _ => {--pos
        -- Q starts with [+,+,...]. LQ starts with [+,?,...].
        -- After dropping the lead of Q, this becomes [+,...] and [+,...].
        -- So the sign variations on Q are unchanged when we induct, while LQ can only lose a sign change.

        have h_nc_nz : nextCoeff Q ≠ 0 := by
          apply sign_ne_zero.mp
          rw [← hsq1, hcsq1]
          simp

        have h_eQ_nz : eraseLead Q ≠ 0 :=
          ne_zero_eraseLead_of_nz_nextCoeff h_nc_nz

        have h_nc_eq : nextCoeff Q = leadingCoeff (eraseLead Q) :=
          leadingCoeff_eraseLead_eq_nextCoeff h_nc_nz

        have h_eLQ : sign_variations ((X - C η) * Q) ≥ sign_variations ((X - C η) * (eraseLead Q)) := by
          apply signvar_X_sub_C_ge_eraseLead_of_nextCoeff_nz Q h_nc_nz hη hqpos
          apply sign_eq_one_iff.mp
          rw [← hsq1, hcsq1]
          exact SignType.pos_eq_one

        have h_ind : sign_variations ((X - C η) * (eraseLead Q)) ≥ sign_variations (eraseLead Q) + 1 := by
          exact ih (natDegree (eraseLead Q)) hnDeQ h_eQ_nz rfl

        have h_eQ : sign_variations (eraseLead Q) = sign_variations (Q) := by
          rw [sign_var_eq_eraseLead_ite hq]
          rw [← h_nc_eq, ← hsq0, ← hsq1, h_sq0_pos, hcsq1]
          simp

        linarith
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

end DesRoS
