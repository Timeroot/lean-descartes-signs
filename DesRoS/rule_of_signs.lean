import DesRoS.signvar_mul

namespace DesRoS

open Polynomial
variable {α : Type*} [LinearOrderedField α] (P : Polynomial α) {η : α} [DecidableEq α]

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

--Technically this is true as long as sign(P.leadingCoeff) = sign(P.nextCoeff)
lemma signvar_X_sub_C_ge_eraseLead_of_nextCoeff_nz (h₁ : leadingCoeff P > 0) (h₂ : nextCoeff P > 0) :
  sign_variations ((X - C η) * P) ≥ sign_variations ((X - C η) * (eraseLead P)) := by
    --basic facts
    have hpne0 : P ≠ 0 :=
      (leadingCoeff_ne_zero.mp (ne_of_gt h₁))
    have hxpn0 : (X - C η) * P ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero η) hpne0
    have hndxp : natDegree ((X - C η) * P) = natDegree P + 1 := by
      rw [natDegree_mul (X_sub_C_ne_zero η) hpne0, natDegree_X_sub_C, add_comm]
    have hndep : natDegree P = natDegree (eraseLead P) + 1 :=
      eraseLead_natDegree_of_nextCoeff (ne_of_gt h₂)
    have hxepn0 : (X - C η) * (eraseLead P) ≠ 0 :=
      mul_ne_zero (X_sub_C_ne_zero η) (ne_zero_eraseLead_of_nz_nextCoeff (ne_of_gt h₂))
    have hndxep : natDegree ((X - C η) * eraseLead P) = natDegree (eraseLead P) + 1 := by
      rw [natDegree_mul (mul_ne_zero_iff.mp hxepn0).1 (mul_ne_zero_iff.mp hxepn0).2, natDegree_X_sub_C, add_comm]

    have heqc : ∃(c₀ : α) (cs : List α),
      coeffList ((X - C η) * P) = (leadingCoeff P)::c₀::cs ∧
      coeffList ((X - C η) * (eraseLead P)) = (nextCoeff P)::cs := by
        obtain ⟨dp1, hdp1⟩ := Nat.exists_eq_add_of_lt (natDegree_pos_of_nz_nextCoeff (ne_of_gt h₂))
        obtain ⟨n0, hn0⟩ := coeffList_eraseLead hxepn0
        use nextCoeff ((X - C η) * P)
        use (List.replicate n0 0 ++ coeffList (eraseLead ((X - C η) * eraseLead P)))
        constructor
        case left =>
          have hl0 := calc natDegree P.eraseLead + 2
            _ = (coeffList ((X - C η) * P.eraseLead)).length := by
              simp only [length_coeffList, hxepn0, ite_false, hndxep]
            _ = (leadingCoeff ((X - C η) * eraseLead P) :: (List.replicate n0 0 ++ coeffList (eraseLead ((X - C η) * eraseLead P)))).length := by
              rw [hn0]
            _ = n0 + (coeffList (eraseLead ((X - C η) * P.eraseLead))).length + 1 := by
              rw [List.length_cons, List.length_append, List.length_replicate]
          by_cases hnxp : nextCoeff ((X - C η) * P) = 0
          case pos =>
            suffices eraseLead ((X - C η) * P) = eraseLead ((X - C η) * (eraseLead P)) by
              obtain ⟨n1, hn1⟩ := coeffList_eraseLead hxpn0
              have hn0n1 : n1 = n0 + 1 := by
                have hl1 := calc natDegree P + 2
                  _ = (coeffList ((X - C η) * P)).length := by
                    simp only [length_coeffList, mul_eq_zero, X_sub_C_ne_zero η, hpne0, or_self, ite_false, hndxp]
                  _ = (leadingCoeff ((X - C η) * P) :: (List.replicate n1 0 ++ coeffList (eraseLead ((X - C η) * P)))).length := by
                    rw [hn1]
                  _ = n1 + (coeffList (eraseLead ((X - C η) * P))).length + 1 := by
                    rw [List.length_cons, List.length_append, List.length_replicate]
                rw [this, hndep] at hl1
                linarith
              rw [hn1, this, hnxp, hn0n1]
              rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul, List.replicate_succ, List.cons_append]
            rw [← self_sub_monomial_natDegree_leadingCoeff, hndxp, leadingCoeff_monic_mul (monic_X_sub_C η)]
            rw [← self_sub_monomial_natDegree_leadingCoeff, hndxep, ← hndep, leadingCoeff_monic_mul (monic_X_sub_C η)]
            rw [← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_gt h₂)]
            rw [← self_sub_monomial_natDegree_leadingCoeff]
            rw [mul_sub, sub_mul, sub_mul, ← sub_add, X_mul_monomial]
            suffices C η * monomial P.natDegree P.leadingCoeff = monomial P.natDegree P.nextCoeff by
              rw [this]
              ring
            rw [nextCoeff_of_pos_natDegree _ (hndxp ▸ P.natDegree.succ_pos), hndxp, mul_comm,
              Nat.add_sub_cancel, hdp1, coeff_mul_X_sub_C] at hnxp
            rw [leadingCoeff, nextCoeff_of_pos_natDegree _ (hndep ▸ P.eraseLead.natDegree.succ_pos),
              hdp1, C_mul_monomial, mul_comm η, ← eq_of_sub_eq_zero hnxp, Nat.add_sub_cancel]
          case neg =>
            suffices eraseLead (eraseLead ((X - C η) * P)) = eraseLead ((X - C η) * (eraseLead P)) by
              obtain hn1 := coeffList_eraseLead_nz hnxp
              obtain ⟨n2, hn2⟩ := coeffList_eraseLead (ne_zero_eraseLead_of_nz_nextCoeff hnxp)
              have hndep2 : natDegree P = natDegree (eraseLead P) + 1 :=
                eraseLead_natDegree_of_nextCoeff (ne_of_gt h₂)
              have hn0n2 : n2 = n0 := by
                have hl2 := calc natDegree P + 2
                  _ = (coeffList ((X - C η) * P)).length := by
                    simp only [length_coeffList, mul_eq_zero, X_sub_C_ne_zero η, hpne0, or_self, ite_false, hndxp]
                  _ = _ := by rw [hn1, hn2]
                  _ = n2 + (coeffList (eraseLead (eraseLead ((X - C η) * P)))).length + 2 := by
                    rw [List.length_cons, List.length_cons, List.length_append, List.length_replicate]
                rw [this, hndep] at hl2
                linarith
              rw [hn1, hn2, this, hn0n2]
              rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
              rw [leadingCoeff_eraseLead_eq_nextCoeff hnxp]
            have hndexp : natDegree (eraseLead ((X - C η) * P)) = natDegree P :=
              Nat.add_right_cancel (eraseLead_natDegree_of_nextCoeff hnxp ▸ hndxp)
            rw [← self_sub_monomial_natDegree_leadingCoeff, hndexp, ← leadingCoeff_eraseLead_eq_nextCoeff hnxp,
                ]
            rw [← self_sub_monomial_natDegree_leadingCoeff, hndxp, leadingCoeff_monic_mul (monic_X_sub_C η)]
            rw [← self_sub_monomial_natDegree_leadingCoeff, hndxep, ← hndep, leadingCoeff_monic_mul (monic_X_sub_C η)]
            rw [← leadingCoeff_eraseLead_eq_nextCoeff (ne_of_gt h₂)]
            rw [← self_sub_monomial_natDegree_leadingCoeff]
            rw [mul_sub, sub_mul _ _ (monomial _ _), X_mul_monomial]
            suffices monomial P.natDegree ((X - C η)*P).nextCoeff =
              monomial P.natDegree P.nextCoeff - C η * monomial P.natDegree P.leadingCoeff by
              rw [this]
              ring
            rw [C_mul_monomial]
            rw [← monomial_sub]
            congr
            rw [nextCoeff_of_pos_natDegree _ (hndxp ▸ P.natDegree.succ_pos)]
            rw [leadingCoeff, nextCoeff_of_pos_natDegree _ (hndep ▸ P.eraseLead.natDegree.succ_pos)]
            rw [hndxp, mul_comm, Nat.add_sub_cancel, hdp1, Nat.add_sub_cancel, coeff_mul_X_sub_C]
            ring
        case right =>
          rw [hn0]
          congr
          rw [leadingCoeff_mul, leadingCoeff_X_sub_C, one_mul]
          exact (leadingCoeff_eraseLead_eq_nextCoeff (ne_of_gt h₂)).symm
    rcases heqc with ⟨c₀,cs,⟨hcs,hecs⟩⟩
    dsimp [sign_variations]
    rw [hcs, hecs]
    simp only [List.destutter, decide_not, List.map_cons, h₁, sign_pos,
      decide_False, List.filter_cons_of_pos, sign_eq_zero_iff, Bool.not_eq_true',
      not_not, h₂, tsub_le_iff_right]
    have : ((List.filter (fun x => !decide (x = 0)) (SignType.sign c₀ :: List.map SignType.sign cs)
        ).destutter' (·≠·) 1).length  ≥ 1 := List.destutter'_length_pos _ (·≠·)
    rw [Nat.sub_add_cancel this]
    rw [List.filter]; split --split on whether c₀ = 0 or not.
    swap; next => rfl --if c₀ = 0, the trailing nonzero coefficient lists are identical.
    next hc₀0 =>
      rw [List.destutter']; split --split on whether SignType.sign c₀ = 1 or not.
      swap; next => rfl --if sign c₀ = 1, the destutter doesn't care about it.
      next hc₀1 =>
        have hc₀2 : SignType.sign c₀ = -1 := by cases h : SignType.sign c₀ <;> simp_all
        apply ge_iff_le.mp
        simp only [← ne_eq]
        rw [← List.destutter_cons' , ← List.destutter_cons']
        cases hr : List.filter (fun x => !decide (x = 0)) (List.map (⇑SignType.sign) cs)
        case nil => simp [Nat.le_succ 1]
        case cons r rs =>
          rw [List.destutter_cons_cons, List.destutter_cons_cons]
          split
          next h₃ =>
            have h₃ : r = 1 := by
              cases r
              case pos => trivial
              case zero =>
                have : SignType.zero ∈ SignType.zero :: rs := List.mem_cons.mpr (Or.inl rfl)
                rw [← hr] at this
                replace this := List.of_mem_filter this
                simp at this
              case neg =>
                rw [hc₀2] at h₃
                simp at h₃
            simp only [ne_eq, h₃, List.length_cons, not_true_eq_false, ite_false]
            exact Nat.le_trans (Nat.le_succ _) (Nat.le_succ _)
          next h₃ =>
            have h₄ : 1 ≠ r := by cases h : r <;> simp_all
            simp only [List.length_cons, if_pos h₄]
            apply (not_not.mp h₃).symm |> not_not.mpr |> List.length_destutter'_eq _ _ Ne.Coequivalence |> Nat.le_of_eq |> Nat.succ_le_succ

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
          apply signvar_X_sub_C_ge_eraseLead_of_nextCoeff_nz Q hqpos
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
