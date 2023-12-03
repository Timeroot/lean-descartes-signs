import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.RingDivision
import Mathlib.Data.Polynomial.Degree.Definitions
import Mathlib.Data.Sign
import Mathlib.Data.List.Range
import Mathlib.Data.List.Destutter

--after Logic.lean
section Relation

variable {β : Sort v} (r : β → β → Prop)

/-- Local notation for an arbitrary binary relation `r`. -/
local infix:50 " ≺ " => r

/-- A relation is cotransitive if it is the logical negation of a transitive relation -/
def Cotransitive := ∀ ⦃x y z⦄, x ≺ z → (x ≺ y) ∨ (y ≺ z)

variable {β : Sort v} {r : β → β → Prop}

theorem cotransitive_neg (ht : Transitive r) : Cotransitive (fun a b => ¬(r a b)) := by tauto

theorem transitive_neg (hc : Cotransitive r) : Transitive (fun a b => ¬(r a b)) := by
  intro x y z x_ne_z y_ne_z; by_contra x_eq_z
  have : r x y ∨ r y z := hc x_eq_z
  tauto

lemma Ne.Cotransitive : Cotransitive (fun (a:β) (b:β) => a≠b) := by
  intro x y z x_ne_z; by_contra h
  obtain ⟨x_eq_y, y_eq_z⟩ : (x = y) ∧ (y = z) := by tauto
  simp_all

theorem cotransitive_pos_of_neg_pos (hc : Cotransitive r) (hxy : ¬r x y) (hxz: r x z) : r y z := by
  have : (r x y) ∨ (r y z) := hc hxz
  tauto

theorem cotransitive_neg_of_neg_neg (hc : Cotransitive r) (hxy : ¬r x y) (hxz: ¬r y z) : ¬r x z := by
  have := transitive_neg hc
  tauto


/-- A relation is a coequivalence if it is the logical negation of an equivalence relation -/
structure Coequivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- An coequivalence relation is irreflexive: `x ≁ x` -/
  irrefl  : ∀ x, ¬r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ∼ x` -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is cotransitive: `x ~ z` implies `x ~ y` or `y ~ z` -/
  cotrans : ∀ {x y z}, r x z → r x y ∨ r y z

lemma Coequivalence.irreflexive {r : β → β → Prop} (h : Coequivalence r) : Irreflexive r := h.irrefl

lemma Coequivalence.symmetric {r : β → β → Prop} (h : Coequivalence r) : Symmetric r := λ _ _ => h.symm

lemma Coequivalence.cotransitive {r : β → β → Prop} (h : Coequivalence r) : Cotransitive r :=
  λ _ _ _ => h.cotrans

theorem equivalence_neg (hc : Coequivalence r) : Equivalence (fun a b => ¬(r a b)) :=
  { refl := hc.irrefl, symm := mt hc.symm, trans := λ xz => transitive_neg hc.cotransitive xz}

lemma Ne.Coequivalence : Coequivalence (fun (a:β) (b:β) => a≠b) :=
  { irrefl := λ _ => Ne.irrefl, symm := Ne.symm, cotrans := λ xz => Ne.Cotransitive xz}

theorem coequiv_pos_of_neg_pos (hc : Coequivalence r) (hxy : ¬r y x) (hxz: r x z) : r y z := by
  have : (r x y) ∨ (r y z) := hc.cotrans hxz
  cases this
  case inr => assumption
  exact cotransitive_pos_of_neg_pos hc.cotransitive (mt hc.symm hxy) hxz

end Relation



-- Surely this is somewhere else and I'm just missing it, TODO
namespace Nat
theorem sub_add_of_ge {n : ℕ} (hn : n > 0) : n = (n - 1) + 1 := by cases n <;> simp_all
end Nat



namespace List

variable {α β : Type*} (l l₂ : List α) (Rα : α → α → Prop) (Rβ : β → β → Prop) (f : α → β) [DecidableRel Rα] [DecidableRel Rβ] {a b : α}

/--If the first element of two lists are different, then a sublist relation can be reduced -/
theorem sublist_cons_neq [DecidableEq α] {l l₂ : List α} (h₁: ¬a = b) (h₂ : a :: l <+ b :: l₂) : a :: l <+ l₂ := by
  apply isSublist_iff_sublist.mp
  have := isSublist_iff_sublist.mpr h₂
  rwa [isSublist, if_neg h₁] at this

/--Destutter of a map is the same as the map of the destutter, as long as the map preserves the relation. -/
theorem destutter_map_of_iff (h : ∀ a b, Rα a b ↔ Rβ (f a) (f b)):
  (l.destutter Rα).map f = (l.map f).destutter Rβ := by
    cases h2 : l with
    | nil => simp -- l = []
    | cons a as =>
      clear h2
      induction as generalizing a with
      -- l = a :: []
      | nil => simp
      -- l = a :: a2 :: bs
      | cons a2 bs ih =>
        repeat rw [map_cons, destutter_cons_cons]
        simp_rw [← h a a2]
        by_cases hr : (Rα a a2) <;>
          simp [hr, ← destutter_cons', ih]

/-- Destutter' always has length at least 1. -/
theorem destutter'_length_pos : (destutter' Rα a l).length ≥ 1 := by
  induction l with
  | nil => simp
  | cons b bs ih => dsimp [destutter']; by_cases hR : Rα a b <;> simp [hR] <;> linarith

/-- Destutter' on a relation like ≠, whose negation is an equivalence, gives the same length if
    the first elements are not related (¬Rα a b). --/
theorem length_destutter'_eq (hr : Coequivalence Rα) (hab : ¬Rα a b) : (List.destutter' Rα a l).length = (List.destutter' Rα b l).length := by
    induction l with
    | nil => simp
    | cons c cs ih =>
      dsimp [destutter']
      by_cases hac : (Rα a c)
      case pos =>
        have hbc : Rα b c := cotransitive_pos_of_neg_pos hr.cotransitive hab hac
        simp [if_pos hac, if_pos hbc]
      case neg =>
        have hbc : ¬Rα b c := cotransitive_neg_of_neg_neg hr.cotransitive (mt hr.symm hab) hac
        simpa [if_neg hac, if_neg hbc]

/-- Destutter' on a relation like ≠, whose negation is an equivalence, has length
    monotonic under List.cons --/
theorem length_destutter'_ge_length_destutter'_cons (hr : Coequivalence Rα) :
  (List.destutter' Rα a (b::l)).length ≥ (List.destutter' Rα b l).length := by
    cases l with
    | nil => by_cases hab : (Rα a b) <;> simp_all [Nat.le_succ]
    | cons c cs =>
      by_cases hab : (Rα a b)
      case pos => simp [destutter', if_pos hab, Nat.le_succ]
      by_cases hac : (Rα a c)
      case pos =>
        have hbc : Rα b c := coequiv_pos_of_neg_pos hr (mt hr.symm hab) hac
        simp [destutter', if_pos hbc, if_pos hac, if_neg hab]
      case neg =>
        have hbc : ¬Rα b c := cotransitive_neg_of_neg_neg hr.cotransitive (mt hr.symm hab) hac
        apply le_of_eq;
        simp only [destutter', if_neg hbc, if_neg hac, if_neg hab]
        exact (length_destutter'_eq cs Rα hr hab).symm

/-- Destutter on a relation like ≠, whose negation is an equivalence, has length
    monotonic under List.cons --/
theorem length_destutter_cons_ge_length_destutter (hr : Coequivalence Rα) :
  ((a::l).destutter Rα).length ≥ (l.destutter Rα).length := by
    cases l <;> simp [destutter]; exact length_destutter'_ge_length_destutter'_cons _ Rα hr

/-- `destutter ≠` has length monotonic under List.cons --/
theorem length_destutter_ne_cons_ge_length_destutter [DecidableEq α]:
  ((a::l).destutter (·≠·)).length ≥ (l.destutter (·≠·)).length :=
    length_destutter_cons_ge_length_destutter _ _ Ne.Coequivalence

/-- Destutter' on a relation like ≠ or <, whose negation is transitive, has length monotonic
    under a ¬R changing of the first element. -/
theorem length_destutter'_cotrans_ge (hc : Cotransitive Rα) (hab : ¬Rα b a) :
  (List.destutter' Rα a l).length ≥ (List.destutter' Rα b l).length := by
    induction l generalizing a with
    | nil => simp
    | cons c cs ih =>
      dsimp [destutter']
      by_cases hbc : Rα b c
      case pos =>
        have hac : Rα a c := cotransitive_pos_of_neg_pos hc hab hbc
        simp only [if_pos hac, if_pos hbc, length_cons, le_refl]
      case neg =>
        simp only [if_neg hbc]
        by_cases hac : Rα a c
        case pos =>
          simp only [if_pos hac, length_cons]
          exact Nat.le_succ_of_le (ih hbc)
        case neg =>
          simp only [if_neg hac]
          exact ih hab

/-- Destuttering a relation like ≠, whose negation is a transitive property,
    gives a list of maximal length over any chain.
    In other words: (l.destutter R) is an R-chain sublist of l;
    it is at least as long as any other R-chain sublist.

Proof sketch:
 * Do induction on the length of l. The case of zero length is easy.
 * l.dedup always starts with the first element of l.
 * If l₂ doesn't start with the first element,
  * Write l = a::as. Then l.dedup.length ≥ as.dedup.length ≥ l₂.length, by monotonicity of destutter length
    and induction respectively.
 * If l₂ does start with the first element, write l₂ = a::os.
  * Write l = a::as = a::b::bs. If a≠b, then l.dedup starts with [a,b...] and we can write
    l.dedup.length = 1 + as.dedup.length ≥ 1 + os.length = l2.length, where ≥ is the inductive hypothesis.
  * If a=b, then l.dedup does not contain b, and l₂ doesn't either. So we can define l₃ = a::bs, we know
    that l.dedup = l₃.dedup, and l₂ is a chain sublist of l₃ just like l. So we can apply the inductive hypothesis.
-/
theorem length_destutter_maximal_chain_neg_trans [DecidableEq α] {n : ℕ} (h₁ : l₂ <+ l) (h₂ : l₂.Chain' (·≠·)) {hn : n = l.length} :
  (l.destutter (·≠·)).length ≥ l₂.length := by
    induction n generalizing l l₂ with
    | zero => -- if l is length zero, l₂ is too, done.
      rw [Nat.zero_eq] at hn
      rw [length_eq_zero.mp hn.symm] at h₁ ⊢
      simp [sublist_nil.mp h₁]
    | succ n ih => -- otherwise induction on lists l of length at most n1...
      cases hl₂ : l₂ with
      | nil => simp only [length_nil, zero_le] -- if l2 is length zero, done.
      | cons o os => -- otherwise write l₂ = o::os
        cases l with -- deconstruct l = a::as
        | nil => simp at hn -- l can't be [], contradiction with 'succ n1 ih', a nonzero length
        | cons a as =>
          by_cases hao : (o=a) --split on whether l₂ starts with a or not
          case neg =>
            rw [← hl₂]
            calc length ((a :: as).destutter (·≠·))
              _ ≥ length (as.destutter (·≠·)) := length_destutter_ne_cons_ge_length_destutter as
              _ ≥ length l₂ := by
                apply ih as l₂
                case h₂ => assumption
                case hn => simp at hn; exact hn
                rw [hl₂, ← isSublist_iff_sublist] at h₁ ⊢
                rwa [isSublist, if_neg hao] at h₁
          case pos =>
            rw [hao] at hl₂ ⊢
            have hlos : l₂.length = Nat.succ os.length := by
              rw [hl₂]
              exact length_cons o os
            cases as with -- deconstruct as = b::bs
            | nil => -- stupid case if l₂ = [a]
              have hlen2 : l₂.length ≤ [a].length := Sublist.length_le h₁
              rw [length_singleton] at hlen2
              simp only [destutter_singleton, length_singleton, length_cons]
              linarith
            | cons b bs => -- Okay! l₂ = a::os, l = a::b::bs.
              cases hos : os with -- deconstruct os=p::ps
              | nil =>
                simp only [destutter, length_singleton]
                exact ge_iff_le.mpr (destutter'_length_pos _ _)
              | cons p ps =>
                rw [hos] at hl₂
                -- One more split needed: does a=b or not?
                by_cases hab : (a=b)
                case pos =>
                  simp only [destutter, destutter', ite_not, length_cons,
                            ge_iff_le, hab, not_true_eq_false, ite_false]
                  have : destutter' (·≠·) b bs = destutter (·≠·) (a::bs) := by
                    dsimp [destutter]
                    rw [hab]
                  have hlp := hos.symm ▸ (length_cons p ps)
                  rw [this, ← hlp, ← hlos]
                  apply ih (a::bs) l₂
                  case h₂ => exact h₂
                  case hn => simp_all
                  rw [← hab] at h₁
                  have hneqap := ne_comm.mp (rel_of_chain_cons (hl₂ ▸ h₂))
                  rw [hl₂] at h₁ ⊢
                  apply cons_sublist_cons.mpr
                  exact sublist_cons_neq hneqap (cons_sublist_cons.mp h₁)
                case neg =>
                  rw [← hl₂]
                  calc length ((a::b::bs).destutter (·≠·))
                    _ = length ((b::bs).destutter (·≠·)) + 1 := ?_
                    _ ≥ length os + 1 := ?_
                    _ = length l₂ := by simp [hl₂, hos];
                  case calc_1 => {
                    dsimp [destutter, destutter']
                    rw [if_pos hab, length_cons]
                  }
                  case calc_2 => {
                    rw [ge_iff_le, add_le_add_iff_right, ge_iff_le.symm]
                    apply ih (b::bs) os
                    case h₂ => simp_all
                    case hn => rw [length_cons] at hn; linarith
                    case h₁ => exact hos ▸ sublist_of_cons_sublist_cons (hl₂ ▸ h₁)
                  }

-- /-- Destuttering a relation like ≠, whose negation is a transitive property, effectively breaks
-- the original list into several chunks with the following properties:
--  * Each chunk is pairwise = (or ¬R)
--  * The concatenation of the chunks is the original list
--  * Each chunk is nonempty
--  * The destutter takes the first element of each
-- -/
-- theorem destutter'_neg_is_chunks [DecidableEq α] : ℕ := sorry
--   ∃c:List (List α), (destutter (·≠·) l = (c.map (λls↦List.get ls 1))) := by
--   sorry

/-- (a::l).get n = l.get (n-1), as long as n≠0. -/
theorem get_cons_pos {l : List α} {n : Nat} (hp : n ≠ 0) (hl : n ≤ l.length) :
  (a :: l).get ⟨n, by rw [length_cons]; exact Nat.lt_succ.2 hl⟩
  = l.get ⟨n-1, Nat.lt_of_lt_of_le (Nat.pred_lt hp) hl⟩ := by
    suffices get ([a]++l) ⟨n, by simp; exact Nat.lt_succ.2 hl⟩ =
      get l ⟨n-1, Nat.lt_of_lt_of_le (Nat.pred_lt hp) hl⟩ by
      simp at this
      exact this
    rw [List.get_append_right]; rfl
    rw [length_singleton]
    intro hn
    have := Nat.le_sub_one_of_lt hn
    simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, nonpos_iff_eq_zero] at this
    exact hp this

end List

namespace Polynomial
variable {α : Type*} [Semiring α] {P : Polynomial α}

theorem natDegree_nz_of_nz_nextCoeff (h : nextCoeff P ≠ 0) : natDegree P ≠ 0 := by
  rw [nextCoeff] at h
  by_cases hpz : (natDegree P = 0) <;> simp_all only [ne_eq, zero_le, ite_true, ite_false, not_true_eq_false]
  simp

theorem natDegree_ge_one_of_nz_nextCoeff (h : nextCoeff P ≠ 0) : natDegree P ≥ 1 :=
  Nat.zero_lt_of_ne_zero (natDegree_nz_of_nz_nextCoeff h)

theorem ne_zero_of_nz_nextCoeff (h : nextCoeff P ≠ 0) : P ≠ 0 :=
  ne_zero_of_natDegree_gt (natDegree_ge_one_of_nz_nextCoeff h)

theorem eraseLead_natDegree_of_nextCoeff (h : nextCoeff P ≠ 0) : natDegree P = natDegree (eraseLead P) + 1 := by
  have hpos := natDegree_ge_one_of_nz_nextCoeff h
  suffices natDegree P - 1 ≤ natDegree (eraseLead P) by
    have := (add_le_add_iff_right 1).mpr this
    rw [← Nat.sub_add_of_ge hpos] at this
    have : natDegree P ≥ natDegree (eraseLead P) + 1 := by
      have := eraseLead_natDegree_le P;
      have : natDegree (eraseLead P) + 1 ≤ (natDegree P - 1) + 1 := (add_le_add_iff_right 1).mpr this
      rwa [← Nat.sub_add_of_ge hpos] at this
    linarith
  have : coeff P (natDegree P - 1) = coeff (eraseLead P) (natDegree P - 1) := by
    apply Eq.symm
    apply eraseLead_coeff_of_ne
    exact Nat.pred_ne_self (Nat.ne_zero_iff_zero_lt.mpr hpos)
  rw [nextCoeff, if_neg (natDegree_nz_of_nz_nextCoeff h), this] at h
  apply le_natDegree_of_ne_zero h

theorem leadingCoeff_eraseLead_eq_nextCoeff (h : nextCoeff P ≠ 0) : nextCoeff P = leadingCoeff (eraseLead P) := by
  have hd : natDegree P = natDegree (eraseLead P) + 1 := eraseLead_natDegree_of_nextCoeff h
  rw [leadingCoeff, nextCoeff]
  rw [ne_eq] at h
  simp only [ge_iff_le, coeff_natDegree, if_neg (natDegree_nz_of_nz_nextCoeff h)]
  rw [leadingCoeff]
  rw [eraseLead_natDegree_of_nextCoeff h]
  apply Eq.symm
  apply Polynomial.eraseLead_coeff_of_ne
  linarith

theorem ne_zero_eraseLead_of_nz_nextCoeff (h : nextCoeff P ≠ 0) : eraseLead P ≠ 0 :=
  leadingCoeff_ne_zero.mp (leadingCoeff_eraseLead_eq_nextCoeff h ▸ h)

variable {α : Type*} [Semiring α] {P : Polynomial α} [DecidableEq α]

/-- A list of coefficients starting from the leading term down to the constant term. -/
noncomputable def coeffList (P : Polynomial α) : List α := if P=0 then [] else (List.range (P.natDegree+1)).reverse.map P.coeff

/-- coeffList 0 = [] -/
@[simp]
theorem coeffList_zero  : coeffList (0:α[X]) = [] := by simp [coeffList, ite_true]

/-- coeffList always starts with leadingCoeff -/
theorem coeffList_eq_cons_leadingCoeff (h : P ≠ 0) : ∃(ls : List α), coeffList P = (leadingCoeff P)::ls := by
  by_cases P = 0 <;> simp_all [coeffList, List.range_succ]

/-- The length of the coefficient list is the degree. -/
@[simp]
theorem length_coeffList (P : Polynomial α) : (coeffList P).length = if (P=0) then 0 else P.natDegree+1 := by
  by_cases P = 0 <;> simp_all [coeffList]

theorem coeffList_eraseLead_nz (h : nextCoeff P ≠ 0) : coeffList P = (leadingCoeff P)::(coeffList (eraseLead P)) := by
  have hd : natDegree P = natDegree (eraseLead P) + 1 := eraseLead_natDegree_of_nextCoeff h
  have hpz : P ≠ 0 := ne_zero_of_nz_nextCoeff h
  simp [coeffList, hd, hpz, ne_zero_eraseLead_of_nz_nextCoeff h, List.range_succ]
  constructor
  { rw [← hd]; exact coeff_natDegree }
  constructor
  { rw [leadingCoeff]
    apply Eq.symm
    apply Polynomial.eraseLead_coeff_of_ne
    linarith }
  rw [List.map_reverse, List.map_reverse];
  congr 1
  rw [List.map_eq_map_iff]
  intro n hn
  rw [List.mem_range] at hn
  apply Eq.symm
  apply Polynomial.eraseLead_coeff_of_ne
  linarith

-- theorem coeffList_eraseLead (h : P≠0): ∃(n:ℕ), coeffList P = (leadingCoeff P)::((List.replicate n 0)++(coeffList (eraseLead P))) := by
--   -- have : natDegree P >
--   have : natDegree P ≥ natDegree (eraseLead P) + 1 := by
--     have := eraseLead_natDegree_le P
--     have : natDegree (eraseLead P) + 1 ≤ (natDegree P - 1) + 1 := (add_le_add_iff_right 1).mpr this
--     rwa [← Nat.sub_add_of_ge h] at this
--   use natDegree P - (natDegree (eraseLead P) + 1)
--   apply List.ext_get
--   simp
--   -- obtain ⟨ls, hls⟩ := coeffList_eq_cons_leadingCoeff P
--   -- rw [hls]
--   -- simp only [List.cons.injEq, true_and]
--   sorry

variable {α : Type*} [Ring α] (P : Polynomial α) [DecidableEq α]

/-- The coefficient list is negated if the polynomial is negated. --/
theorem coeffList_neg : (coeffList (-P)) = (coeffList P).map (λx↦-x) := by
  by_cases hp : (P = 0) <;> simp only [
    coeffList, hp, natDegree_neg, natDegree_zero, ite_false, ite_true,
    neg_zero, neg_eq_zero, zero_add, List.map_nil, List.map_map]
  congr; funext; simp

variable {α : Type*} [DivisionSemiring α] (P : Polynomial α) [DecidableEq α]

/-- Over a division semiring, multiplying a polynomial by a nonzero constant leaves the degree unchanged. -/
@[simp]
theorem natDegree_mul_of_nonzero {η : α} (hη : η ≠ 0) : natDegree (C η * P) = natDegree P := by
  by_cases h : (P = 0)
  next P0 => simp only [h, mul_zero, natDegree_zero]
  next Pn0 =>
    rw [← zero_add P.natDegree, ← natDegree_C η]
    apply natDegree_mul'
    simp only [leadingCoeff_C, ne_eq, mul_eq_zero, leadingCoeff_eq_zero]
    intro hPη0; cases hPη0
    next η0 => exact hη η0
    next h0 => exact h h0

/-- Over a division semiring, multiplying a polynomial by a nonzero constant multiplies the coefficients. -/
@[simp]
theorem coeffList_C {η : α} (hη : η ≠ 0) : coeffList (C η) = [η] := by
    simp only [coeffList, natDegree_C, zero_add]
    dsimp [List.range]
    simpa [List.range.loop]

/-- Over a division semiring, multiplying a polynomial by a nonzero constant multiplies the coefficients. -/
theorem coeffList_mul_C {η : α} (hη : η ≠ 0) :
  coeffList (C η * P) = (coeffList P).map (λx↦η*x) := by
    by_cases hp : P = 0
    case pos => simp only [hp, mul_zero, coeffList_zero, List.map_nil]
    have hcη : C η * P ≠ 0 := mul_ne_zero (mt (map_eq_zero _).mp hη) hp
    rw [coeffList, coeffList]
    rw [natDegree_mul_of_nonzero, if_neg hcη, if_neg hp, List.map_map]
    congr
    funext n
    simp
    exact hη

-- @[simp]
-- theorem coeffList_mul_X (hP : P ≠ 0) : coeffList (X * P) = (coeffList P) ++ [0] := by
--   rw [coeffList, coeffList]
--   rw [natDegree_X_mul hP]
--   rw [List.range_succ]
--   rw [List.map_append]
--   apply List.ext_get
--   case hl =>
--     simp only [List.length_append, List.length_map, List.length_range, List.length_singleton, add_comm]
--   simp
--   intro n h1 _
--   by_cases h2 : n = (P.natDegree+1)
--   case pos => rw [List.get_append_right] <;> simp [h2]
--   case neg =>
--     rw [List.get_append]
--     case h =>
--       simp
--       clear hP
--       linarith (config := {splitNe := true})
--     by_cases h3 : n = 0
--     case pos => simp [h3]
--     case neg =>
--       rw [List.get_cons_pos]
--       case hp => exact h3
--       case hl => simp [h1]; exact Nat.le_of_lt_succ h1
--       have h4 : n = (n - 1) + 1 := Nat.sub_add_of_ge (pos_iff_ne_zero.mpr h3)
--       simp only [List.get_map, List.get_range, ge_iff_le]
--       rw [h4]
--       simp

variable {α : Type*} [Ring α] (P : Polynomial α)

-- @[simp]
-- theorem coeffList_mul_linear {η : α} (hp : P ≠ 0) : coeffList ((X - C η) * P) = sorry := by
--   conv =>
--     lhs
--     simp only [coeffList, coeff_mul]

--   sorry

end Polynomial
