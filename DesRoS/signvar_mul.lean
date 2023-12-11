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

lemma signvar_ereaseLead_mul_XC_eq_XC_mul_eraseLead
  (hη : η > 0) (hP₀ : leadingCoeff P > 0) (hP₁ : nextCoeff P < 0) (hQ₀ : leadingCoeff ((X-C η)*P) > 0) :
  sign_variations (eraseLead ((X - C η) * P)) = sign_variations ((X - C η) * (eraseLead P)) := by
    sorry

end DesRoS
