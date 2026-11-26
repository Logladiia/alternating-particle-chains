import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Minimax quadrature after erasures: the cyclic gap theorem

A design is specified by its positive cyclic gaps, of total length one.
An erasure is represented by an initial retained point and a list of positive run
lengths summing to the original number of points. Each run joins that many original
gaps; their intervening nodes are erased. Costs here are divided by the common
positive factor of the uniform quadrature error in the paper.
-/

namespace PeriodicQuadrature

open Finset
open scoped BigOperators

variable {n : ℕ} [NeZero n]

/-- The length of the run of `b` gaps starting at `i`. -/
def window (g : Fin n → ℝ) (i : Fin n) (b : ℕ) : ℝ :=
  ∑ j ∈ range b, g (i + Fin.ofNat n j)

/-- The sum of the powers of the retained gap lengths. -/
noncomputable def cost (p : ℝ) (g : Fin n → ℝ) (i : Fin n) : List ℕ → ℝ
  | [] => 0
  | b :: bs => window g i b ^ p + cost p g (i + Fin.ofNat n b) bs

def Design (g : Fin n → ℝ) : Prop :=
  (∀ i, 0 < g i) ∧ (∑ i, g i) = 1

/-- `k` retained points delimit `k` runs. -/
def ValidRuns (n k : ℕ) (bs : List ℕ) : Prop :=
  bs.length = k ∧ bs.sum = n ∧ ∀ b ∈ bs, 0 < b

/-- All erasures with `k` retained points have cost at most `B`. -/
def UpperBound (p : ℝ) (g : Fin n → ℝ) (k : ℕ) (B : ℝ) : Prop :=
  ∀ i bs, ValidRuns n k bs → cost p g i bs ≤ B

noncomputable def uniform (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- Formula for `s - 1` erased points and `m + 1` retained points, where `s + m = n`. -/
noncomputable def optimum (p : ℝ) (n s m : ℕ) : ℝ :=
  ((s : ℝ) / n) ^ p + (m : ℝ) * (1 / (n : ℝ)) ^ p

private theorem sum_shift (f : Fin n → ℝ) (c : Fin n) :
    (∑ i, f (i + c)) = ∑ i, f i := by
  exact Equiv.sum_comp (Equiv.addRight c) f

private theorem sum_window (g : Fin n → ℝ) (b : ℕ) :
    (∑ i, window g i b) = (b : ℝ) * ∑ i, g i := by
  unfold window
  rw [Finset.sum_comm]
  simp [sum_shift, nsmul_eq_mul]

private theorem sum_window_full (g : Fin n → ℝ) (i : Fin n) :
    window g i n = ∑ j, g j := by
  unfold window
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [add_comm] using sum_shift g i

private theorem cost_singletons (p : ℝ) (g : Fin n → ℝ) (i : Fin n) (m : ℕ) :
    cost p g i (List.replicate m 1) = window (fun j => g j ^ p) i m := by
  induction m generalizing i with
  | zero => simp [cost, window]
  | succ m ih =>
    simp only [List.replicate_succ, cost, ih]
    rw [show window g i 1 = g i by simp [window]]
    unfold window
    rw [Finset.sum_range_succ']
    simp only [Fin.ofNat_zero, add_zero]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    rw [add_assoc]
    congr 1
    apply Fin.eq_of_val_eq
    simp [Fin.ofNat, Fin.add_def, Nat.add_comm 1 j]

omit [NeZero n] in
private theorem run_valid (s m : ℕ) (hs : 0 < s) (hn : s + m = n) :
    ValidRuns n (m + 1) (s :: List.replicate m 1) := by
  refine ⟨by simp, by simpa using hn, ?_⟩
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact hs
  · have := List.eq_of_mem_replicate hb
    omega

private theorem constant_weight_sum :
    (∑ _ : Fin n, (1 / (n : ℝ))) = 1 := by
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp [nsmul_eq_mul, hn]

omit [NeZero n] in
private theorem weighted_sum_eq (f : Fin n → ℝ) :
    (∑ i, (1 / (n : ℝ)) • f i) = (∑ i, f i) / (n : ℝ) := by
  simp only [smul_eq_mul, div_eq_mul_inv, one_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

private theorem jensen (p : ℝ) (hp : 1 < p) (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) :
    ((∑ i, f i) / (n : ℝ)) ^ p ≤ (∑ i, f i ^ p) / (n : ℝ) := by
  simpa only [weighted_sum_eq] using
    (strictConvexOn_rpow hp).convexOn.map_sum_le
      (t := (univ : Finset (Fin n))) (w := fun _ => 1 / (n : ℝ)) (p := f)
      (fun _ _ => by positivity) constant_weight_sum (fun i _ => hf i)

private theorem jensen_eq (p : ℝ) (hp : 1 < p) (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i)
    (h : ((∑ i, f i) / (n : ℝ)) ^ p = (∑ i, f i ^ p) / (n : ℝ)) :
    ∀ i, f i = (∑ j, f j) / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have he := (strictConvexOn_rpow hp).map_sum_eq_iff
      (t := (univ : Finset (Fin n))) (w := fun _ => 1 / (n : ℝ)) (p := f)
      (fun _ _ => by positivity) constant_weight_sum (fun i _ => hf i)
  intro i
  simpa only [weighted_sum_eq] using (he.mp (by simpa only [weighted_sum_eq] using h)) i (mem_univ i)

private theorem uniform_design : Design (uniform n) :=
  ⟨fun _ => by have : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
               exact one_div_pos.mpr this, constant_weight_sum⟩

private theorem uniform_window (i : Fin n) (b : ℕ) :
    window (uniform n) i b = (b : ℝ) / n := by
  simp [window, uniform, nsmul_eq_mul, div_eq_mul_inv]

/-- Merging two positive erased runs strictly increases the sum of powers. -/
private theorem merge_powers_strict (p a b : ℝ) (hp : 1 < p) (ha : 1 < a) (hb : 1 < b) :
    a ^ p + b ^ p < (a + b - 1) ^ p + 1 := by
  let v := a + b - 1
  let u := (a - 1) / (v - 1)
  let t := (b - 1) / (v - 1)
  have hv : 1 < v := by dsimp [v]; linarith
  have hden : v - 1 > 0 := by linarith
  have hu : 0 < u := div_pos (by linarith) hden
  have ht : 0 < t := div_pos (by linarith) hden
  have hut : u + t = 1 := by
    dsimp [u, t]
    rw [← add_div, div_eq_iff (ne_of_gt hden)]
    dsimp [v]; ring
  have hx : t * 1 + u * v = a := by
    dsimp [u, t]
    field_simp
    dsimp [v]
    ring
  have hy : u * 1 + t * v = b := by
    dsimp [u, t]
    field_simp
    dsimp [v]
    ring
  have hmem : v ∈ Set.Ici (0 : ℝ) := le_trans zero_le_one hv.le
  have hne : (1 : ℝ) ≠ v := ne_of_lt hv
  have hone : (1 : ℝ) ∈ Set.Ici 0 := by simp
  have h₁ := (strictConvexOn_rpow hp).2 hone
    hmem hne ht hu (by linarith : t + u = 1)
  have h₂ := (strictConvexOn_rpow hp).2 hone
    hmem hne hu ht hut
  simp only [smul_eq_mul, Real.one_rpow, mul_one] at h₁ h₂
  have hx' : t + u * v = a := by simpa using hx
  have hy' : u + t * v = b := by simpa using hy
  rw [hx'] at h₁
  rw [hy'] at h₂
  have hvp := congrArg (fun x : ℝ => x * v ^ p) hut
  simp only [add_mul, one_mul] at hvp
  linarith

private theorem merge_powers (p : ℝ) (hp : 1 < p) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (a : ℝ) ^ p + (b : ℝ) ^ p ≤ ((a : ℝ) + b - 1) ^ p + 1 := by
  by_cases ha' : a = 1
  · subst a
    simp [Real.one_rpow, add_comm]
  by_cases hb' : b = 1
  · subst b
    simp
  exact (merge_powers_strict p a b hp (by exact_mod_cast (show 1 < a by omega))
    (by exact_mod_cast (show 1 < b by omega))).le

private theorem length_le_sum (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b) :
    bs.length ≤ bs.sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb := hpos b (by simp)
    have h := ih (fun c hc => hpos c (List.mem_cons_of_mem _ hc))
    simp only [List.length_cons, List.sum_cons]
    omega

private theorem list_bound (p : ℝ) (hp : 1 < p) (bs : List ℕ) (hne : bs ≠ [])
    (hpos : ∀ b ∈ bs, 0 < b) :
    (bs.map (fun b : ℕ => (b : ℝ) ^ p)).sum ≤
      ((bs.sum : ℝ) - bs.length + 1) ^ p + bs.length - 1 := by
  induction bs with
  | nil => contradiction
  | cons a bs ih =>
    by_cases ht : bs = []
    · subst bs
      simp
    have htail := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have hn := length_le_sum bs htail
    let b := bs.sum - bs.length + 1
    have hbc : (b : ℝ) = (bs.sum : ℝ) - bs.length + 1 := by
      simp [b, Nat.cast_sub hn]
    have h := ih ht htail
    rw [← hbc] at h
    have hm := merge_powers p hp a b (hpos a (by simp)) (by omega : 0 < b)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [show (a : ℝ) + (bs.sum : ℝ) - ((bs.length : ℝ) + 1) + 1 =
      (a : ℝ) + b - 1 by rw [hbc]; ring]
    linarith

private def nontrivialRuns (bs : List ℕ) := bs.filter (fun b => decide (1 < b))

private theorem nontrivial_if_length_lt_sum (bs : List ℕ) (hpos : ∀ b ∈ bs, 0 < b)
    (h : 0 < (nontrivialRuns bs).length) : bs.length < bs.sum := by
  induction bs with
  | nil => simp [nontrivialRuns] at h
  | cons a bs ih =>
    have ha := hpos a (by simp)
    have htail : ∀ b ∈ bs, 0 < b := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have hle := length_le_sum bs htail
    by_cases ha' : 1 < a
    · simp only [List.length_cons, List.sum_cons]
      omega
    · have h' : 0 < (nontrivialRuns bs).length := by simpa [nontrivialRuns, ha'] using h
      have ht := ih htail h'
      simp only [List.length_cons, List.sum_cons]
      omega

private theorem list_eq_or_lt (p : ℝ) (hp : 1 < p) (bs : List ℕ) (hne : bs ≠ [])
    (hpos : ∀ b ∈ bs, 0 < b) :
    if (nontrivialRuns bs).length ≤ 1 then
      (bs.map (fun b : ℕ => (b : ℝ) ^ p)).sum =
        ((bs.sum : ℝ) - bs.length + 1) ^ p + bs.length - 1
    else
      (bs.map (fun b : ℕ => (b : ℝ) ^ p)).sum <
        ((bs.sum : ℝ) - bs.length + 1) ^ p + bs.length - 1 := by
  induction bs with
  | nil => contradiction
  | cons a bs ih =>
    by_cases ht : bs = []
    · subst bs
      by_cases ha' : 1 < a <;> simp [nontrivialRuns, ha']
    have ha := hpos a (by simp)
    have htail : ∀ b ∈ bs, 0 < b := fun b hb => hpos b (List.mem_cons_of_mem _ hb)
    have hn := length_le_sum bs htail
    have hcs : ((a :: bs).sum : ℝ) - (a :: bs).length + 1 =
        (a : ℝ) + ((bs.sum : ℝ) - bs.length + 1) - 1 := by
      simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      ring
    by_cases ha' : 1 < a
    · by_cases hzero : (nontrivialRuns bs).length = 0
      · have hall : ∀ b ∈ bs, b = 1 := by
          intro b hb
          have := htail b hb
          by_contra hne
          have hmem : b ∈ nontrivialRuns bs := by
            simp [nontrivialRuns, hb, show 1 < b by omega]
          have hempty := List.length_eq_zero_iff.mp hzero
          simp [hempty] at hmem
        have hrep : bs = List.replicate bs.length 1 := by
          exact List.eq_replicate_of_mem (fun b hb => hall b hb)
        have hs : bs.sum = bs.length := by
          conv_lhs => rw [hrep]
          simp
        have hpow : (bs.map (fun b : ℕ => (b : ℝ) ^ p)).sum = bs.length := by
          conv_lhs => rw [hrep]
          simp
        have hc : (nontrivialRuns (a :: bs)).length ≤ 1 := by
          simpa [nontrivialRuns, ha'] using (show (nontrivialRuns bs).length + 1 ≤ 1 by omega)
        rw [if_pos hc, hcs]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        rw [hs, hpow]
        simp
        ring
      · have hlt := nontrivial_if_length_lt_sum bs htail (Nat.pos_of_ne_zero hzero)
        have hcount : ¬ (nontrivialRuns (a :: bs)).length ≤ 1 := by
          simpa [nontrivialRuns, ha'] using
            (show ¬ (nontrivialRuns bs).length + 1 ≤ 1 by omega)
        have hb : 1 < (bs.sum : ℝ) - bs.length + 1 := by
          have : (bs.length : ℝ) < bs.sum := by exact_mod_cast hlt
          linarith
        have hm := merge_powers_strict p a ((bs.sum : ℝ) - bs.length + 1)
          hp (by exact_mod_cast ha') hb
        have h := list_bound p hp bs ht htail
        rw [if_neg hcount, hcs]
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        linarith
    · have ha₁ : a = 1 := by omega
      subst a
      have hcount : nontrivialRuns (1 :: bs) = nontrivialRuns bs := by simp [nontrivialRuns]
      rw [hcount, hcs]
      have hsum := ih ht htail
      split_ifs at hsum ⊢ <;>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
          Nat.cast_one, Real.one_rpow, add_sub_cancel_left] <;>
        linarith

private theorem uniform_cost (p : ℝ) (i : Fin n) (bs : List ℕ) :
    cost p (uniform n) i bs = (1 / (n : ℝ)) ^ p * (bs.map (fun b : ℕ => (b : ℝ) ^ p)).sum := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  induction bs generalizing i with
  | nil => simp [cost]
  | cons b bs ih =>
    rw [cost, uniform_window, ih]
    simp only [List.map_cons, List.sum_cons, mul_add]
    rw [show (b : ℝ) / n = (1 / (n : ℝ)) * b by ring]
    rw [Real.mul_rpow (by positivity : 0 ≤ 1 / (n : ℝ)) (Nat.cast_nonneg b)]

/-- Equality on the regular design occurs precisely when at most one retained
gap contains erased nodes. -/
theorem uniform_worst_iff (p : ℝ) (hp : 1 < p) (s m : ℕ) (hn : s + m = n)
    (i : Fin n) (bs : List ℕ) (hv : ValidRuns n (m + 1) bs) :
    cost p (uniform n) i bs = optimum p n s m ↔
      (bs.filter (fun b => decide (1 < b))).length ≤ 1 := by
  have hne : bs ≠ [] := by
    intro h
    simpa [h] using hv.1
  have h := list_eq_or_lt p hp bs hne hv.2.2
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hfactor : 0 < (1 / (n : ℝ)) ^ p := Real.rpow_pos_of_pos (one_div_pos.mpr hn') _
  have he : (n : ℝ) - (bs.length : ℝ) + 1 = s := by
    rw [hv.1, ← hn]
    push_cast
    ring
  rw [hv.2.1, he, hv.1] at h
  have hcount : (↑(m + 1) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  rw [hcount] at h
  have hadd : (s : ℝ) ^ p + ((m : ℝ) + 1) - 1 = (s : ℝ) ^ p + m := by ring
  rw [hadd] at h
  rw [uniform_cost]
  unfold optimum
  rw [show (s : ℝ) / n = (1 / (n : ℝ)) * s by ring,
    Real.mul_rpow (by positivity : 0 ≤ 1 / (n : ℝ)) (Nat.cast_nonneg s),
    mul_comm (m : ℝ), ← mul_add]
  change _ ↔ (nontrivialRuns bs).length ≤ 1
  split_ifs at h with hm
  · simp [h, hm]
  · exact iff_of_false
      (ne_of_lt (mul_lt_mul_of_pos_left h hfactor)) hm

theorem consecutive_worst (p : ℝ) (hp : 1 < p) (s m : ℕ) (hs : 0 < s) (hn : s + m = n)
    (i : Fin n) :
    cost p (uniform n) i (s :: List.replicate m 1) = optimum p n s m := by
  apply (uniform_worst_iff p hp s m hn i _ (run_valid s m hs hn)).2
  by_cases h : 1 < s <;> simp [h]

/-- The regular design attains the proposed bound for every erasure. -/
theorem uniform_upper (p : ℝ) (hp : 1 < p) (s m : ℕ) (hn : s + m = n) :
    UpperBound p (uniform n) (m + 1) (optimum p n s m) := by
  intro i bs hv
  have hne : bs ≠ [] := by
    intro h
    simpa [h] using hv.1
  have h := list_bound p hp bs hne hv.2.2
  rw [uniform_cost]
  have npos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have he : (n : ℝ) - (bs.length : ℝ) + 1 = s := by
    rw [hv.1, ← hn]; push_cast; ring
  rw [hv.2.1, he, hv.1] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  unfold optimum
  rw [show (s : ℝ) / n = (1 / (n : ℝ)) * s by ring,
    Real.mul_rpow (by positivity : 0 ≤ 1 / (n : ℝ)) (Nat.cast_nonneg s)]
  rw [mul_comm (m : ℝ), ← mul_add]
  exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg (by positivity) _)

private theorem circular_average_lower (p : ℝ) (g : Fin n → ℝ) (s m : ℕ)
    {B : ℝ} (hs : 0 < s) (hn : s + m = n)
    (hB : UpperBound p g (m + 1) B) :
    (∑ i, window g i s ^ p) / n +
      (m : ℝ) * ((∑ i, g i ^ p) / n) ≤ B := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h : ∀ i : Fin n, cost p g i (s :: List.replicate m 1) ≤ B :=
    fun i => hB i _ (run_valid s m hs hn)
  have hv := Finset.sum_le_sum (s := (univ : Finset (Fin n))) (fun i _ => h i)
  simp only [cost, cost_singletons, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hv
  rw [sum_shift (fun i => window (fun j => g j ^ p) i m) (Fin.ofNat n s), sum_window] at hv
  have hdiv := div_le_div_of_nonneg_right hv hn'.le
  rw [show (n : ℝ) * B / n = B by field_simp] at hdiv
  simpa only [add_div, mul_div_assoc] using hdiv

/-- Every design has a worst-case cost at least the proposed optimum. -/
theorem lower_bound (p : ℝ) (hp : 1 < p) (g : Fin n → ℝ) (hg : Design g)
    (s m : ℕ) (hs : 0 < s) (hn : s + m = n) {B : ℝ}
    (hB : UpperBound p g (m + 1) B) :
    optimum p n s m ≤ B := by
  have hw := jensen p hp (fun i => window g i s) (fun i =>
    Finset.sum_nonneg (fun j _ => (hg.1 (i + Fin.ofNat n j)).le))
  rw [sum_window, hg.2, mul_one] at hw
  have hg' := jensen p hp g (fun i => (hg.1 i).le)
  rw [hg.2] at hg'
  exact (add_le_add hw (mul_le_mul_of_nonneg_left hg' (Nat.cast_nonneg m))).trans
    (circular_average_lower p g s m hs hn hB)

/-- The infimum over all design bounds is attained and has the claimed value. -/
theorem minimax (p : ℝ) (hp : 1 < p) (s m : ℕ) (hs : 0 < s) (hn : s + m = n) :
    IsLeast {B : ℝ | ∃ g : Fin n → ℝ, Design g ∧ UpperBound p g (m + 1) B}
      (optimum p n s m) := by
  refine ⟨⟨uniform n, uniform_design, uniform_upper p hp s m hn⟩, ?_⟩
  intro B h
  obtain ⟨g, hg, hB⟩ := h
  exact lower_bound p hp g hg s m hs hn hB

/-- With two or more retained points, only the uniform gap vector is optimal. -/
theorem unique_of_two_survivors (p : ℝ) (hp : 1 < p) (g : Fin n → ℝ) (hg : Design g)
    (s m : ℕ) (hs : 0 < s) (hm : 0 < m) (hn : s + m = n)
    (hB : UpperBound p g (m + 1) (optimum p n s m)) : g = uniform n := by
  have hw := jensen p hp (fun i => window g i s) (fun i =>
    Finset.sum_nonneg (fun j _ => (hg.1 (i + Fin.ofNat n j)).le))
  rw [sum_window, hg.2, mul_one] at hw
  have hg' := jensen p hp g (fun i => (hg.1 i).le)
  rw [hg.2] at hg'
  have hav := circular_average_lower p g s m hs hn hB
  unfold optimum at hav
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have he : ((1 : ℝ) / n) ^ p = (∑ i, g i ^ p) / n := by
    by_contra h
    have hlt := lt_of_le_of_ne hg' h
    have hmul := mul_lt_mul_of_pos_left hlt hmp
    linarith
  funext i
  have hf := jensen_eq p hp g (fun i => (hg.1 i).le) (by simpa only [hg.2] using he) i
  simpa only [hg.2, uniform] using hf

/-- With a single survivor the power sum is one, for every design. -/
theorem sole_survivor (p : ℝ) (g : Fin n → ℝ) (hg : Design g) (i : Fin n)
    (bs : List ℕ) (h : ValidRuns n 1 bs) : cost p g i bs = 1 := by
  match bs with
  | [b] =>
    have hbn : b = n := by simpa using h.2.1
    subst b
    simp [cost, sum_window_full, hg.2]
  | [] => simp [ValidRuns] at h
  | _ :: _ :: _ => simp [ValidRuns] at h

/-- The exact uniform-measure contribution of a single retained gap. -/
theorem gap_integral (α h : ℝ) (hα : 0 < α) (hh : 0 ≤ h) :
    (∫ t in (0 : ℝ)..h, (min t (h - t)) ^ α) =
      h ^ (α + 1) / (2 ^ α * (α + 1)) := by
  have hc : Continuous (fun t : ℝ => (min t (h - t)) ^ α) :=
    (Real.continuous_rpow_const hα.le).comp (continuous_id.min (continuous_const.sub continuous_id))
  have hl : (∫ t in (0 : ℝ)..(h / 2), (min t (h - t)) ^ α) =
      ∫ t in (0 : ℝ)..(h / 2), t ^ α := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : 0 ≤ h / 2)] at ht
    simp only [min_eq_left (by linarith [ht.2] : t ≤ h - t)]
  have hr : (∫ t in (h / 2)..h, (min t (h - t)) ^ α) =
      ∫ t in (h / 2)..h, (h - t) ^ α := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : h / 2 ≤ h)] at ht
    simp only [min_eq_right (by linarith [ht.1] : h - t ≤ t)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 (h / 2)) (hc.intervalIntegrable (h / 2) h), hl, hr]
  rw [intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t ^ α) h]
  rw [sub_self, show h - h / 2 = h / 2 by ring]
  rw [integral_rpow (Or.inl (by linarith : -1 < α)),
    Real.zero_rpow (by linarith : α + 1 ≠ 0), sub_zero]
  rw [Real.div_rpow hh (by norm_num : 0 ≤ (2 : ℝ)),
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have htwo : (2 : ℝ) ^ α ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  field_simp
  ring

/-- The indistinguishable extremal profiles for the fixed-survivor lower bound. -/
theorem distance_power_holder {X : Type*} [PseudoMetricSpace X] (S : Set X)
    {α : ℝ} (hα : 0 < α) (hα₁ : α ≤ 1) :
    (∀ x ∈ S, Metric.infDist x S ^ α = 0) ∧
      ∀ x y, |Metric.infDist x S ^ α - Metric.infDist y S ^ α| ≤ dist x y ^ α := by
  constructor
  · intro x hx
    rw [Metric.infDist_zero_of_mem hx, Real.zero_rpow hα.ne']
  · intro x y
    have step (a b : X) : Metric.infDist a S ^ α - Metric.infDist b S ^ α ≤ dist a b ^ α := by
      have hu := Real.rpow_le_rpow Metric.infDist_nonneg
        (Metric.infDist_le_infDist_add_dist (x := a) (y := b) (s := S)) hα.le
      have hv := Real.rpow_add_le_add_rpow (a := Metric.infDist b S) (b := dist a b)
        Metric.infDist_nonneg dist_nonneg hα.le hα₁
      linarith
    exact abs_le.mpr ⟨by simpa [dist_comm y x] using (neg_le_neg (step y x)), step x y⟩

/-- Between consecutive points in the periodic lift, only the two endpoints
are needed to compute the nearest-sample distance. -/
theorem distance_in_lifted_gap (S : Set ℝ) {a b x : ℝ}
    (ha : a ∈ S) (hb : b ∈ S) (hx₁ : a ≤ x) (hx₂ : x ≤ b)
    (hempty : ∀ y ∈ S, y ≤ a ∨ b ≤ y) :
    Metric.infDist x S = min (x - a) (b - x) := by
  apply le_antisymm
  · apply le_min
    · simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx₁)] using
        (Metric.infDist_le_dist_of_mem (x := x) ha)
    · simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx₂), neg_sub] using
        (Metric.infDist_le_dist_of_mem (x := x) hb)
  · apply (Metric.le_infDist ⟨a, ha⟩).2
    intro y hy
    rcases hempty y hy with h | h
    · rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ x - y)]
      exact (min_le_left _ _).trans (by linarith)
    · rw [Real.dist_eq, abs_of_nonpos (by linarith : x - y ≤ 0), neg_sub]
      exact (min_le_right _ _).trans (by linarith)

section FixedSamples

open MeasureTheory

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The defining Hölder inequality for a continuous function on the sample space. -/
def HolderBall (α : ℝ) (f : C(X, ℝ)) : Prop :=
  ∀ x y, |f x - f y| ≤ dist x y ^ α

private def readings (S : Set X) (f : C(X, ℝ)) (x : S) : ℝ := f x

private noncomputable def integralValue (μ : Measure X) (f : C(X, ℝ)) : ℝ :=
  ∫ x, f x ∂μ

/-- An unrestricted deterministic rule may use only the readings on the fixed set. -/
def Achievable (μ : Measure X) (S : Set X) (α B : ℝ) : Prop :=
  ∃ rule : (S → ℝ) → ℝ, ∀ f : C(X, ℝ), HolderBall α f →
    |integralValue μ f - rule (readings S f)| ≤ B

/-- Exact minimax recovery from a nonempty compact set of samples, with respect
to any finite positive measure. A positive integration weight can be included
in the measure. The upper bound uses the diameter of the set of compatible
integral values, avoiding any measurability assumption on the rule itself. -/
theorem fixed_sample_minimax (μ : Measure X) [IsFiniteMeasure μ] (S : Set X)
    (hS : IsCompact S) (hne : S.Nonempty) (α : ℝ) (hα : 0 < α) (hα₁ : α ≤ 1) :
    IsLeast {B : ℝ | Achievable μ S α B} (∫ x, Metric.infDist x S ^ α ∂μ) := by
  let D : C(X, ℝ) :=
    ⟨fun x => Metric.infDist x S ^ α,
      (Real.continuous_rpow_const hα.le).comp (Metric.lipschitz_infDist_pt S).continuous⟩
  let R := integralValue μ D
  change IsLeast _ R
  have hInt (f : C(X, ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hzero (x : S) : D x = 0 := (distance_power_holder S hα hα₁).1 x x.property
  have hD : HolderBall α D := (distance_power_holder S hα hα₁).2
  constructor
  · let values (data : S → ℝ) : Set ℝ := {z | ∃ f : C(X, ℝ),
        HolderBall α f ∧ readings S f = data ∧ integralValue μ f = z}
    refine ⟨fun data => sSup (values data) - R, ?_⟩
    intro f hf
    have hm : integralValue μ f ∈ values (readings S f) := ⟨f, hf, rfl, rfl⟩
    have hUpper : ∀ z ∈ values (readings S f), z ≤ integralValue μ f + 2 * R := by
      rintro z ⟨g, hg, hdata, rfl⟩
      have hpoint (x : X) : g x - f x ≤ 2 * D x := by
        obtain ⟨y, hy, he⟩ := hS.exists_infDist_eq_dist hne x
        have hfg : g y = f y := congrFun hdata (⟨y, hy⟩ : S)
        have h₁ := (abs_le.mp (hg x y)).2
        have h₂ := (abs_le.mp (hf x y)).1
        change g x - f x ≤ 2 * Metric.infDist x S ^ α
        rw [he]
        linarith
      have hb := integral_mono ((hInt g).sub (hInt f)) ((hInt D).const_mul 2) hpoint
      change (∫ x, g x - f x ∂μ) ≤ ∫ x, 2 * D x ∂μ at hb
      rw [integral_sub (hInt g) (hInt f), integral_const_mul] at hb
      change integralValue μ g - integralValue μ f ≤ 2 * R at hb
      linarith
    have hl := le_csSup ⟨_, hUpper⟩ hm
    have hu := csSup_le ⟨_, hm⟩ hUpper
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro B hB
    obtain ⟨rule, hRule⟩ := hB
    have hNeg : HolderBall α (-D) := by
      intro x y
      change |-D x - -D y| ≤ _
      simpa only [neg_sub_neg, abs_sub_comm] using hD x y
    have hEqual : readings S (-D) = readings S D := by
      funext x
      change -D x = D x
      simp [hzero x]
    have hMinus : integralValue μ (-D) = -R := by
      exact integral_neg (fun x => D x)
    have h₁ := (abs_le.mp (hRule D hD)).2
    have h₂ := (abs_le.mp (hRule (-D) hNeg)).1
    rw [hEqual, hMinus] at h₂
    change R - rule (readings S D) ≤ B at h₁
    linarith

end FixedSamples

/-- Each retained arc is integrated in its own arc-length coordinate. -/
noncomputable def integratedCost (α : ℝ) (g : Fin n → ℝ) (i : Fin n) :
    List ℕ → ℝ
  | [] => 0
  | b :: bs =>
    (∫ t in (0 : ℝ)..(window g i b), (min t (window g i b - t)) ^ α) +
      integratedCost α g (i + Fin.ofNat n b) bs

theorem integratedCost_eq (α : ℝ) (hα : 0 < α) (g : Fin n → ℝ)
    (hg : Design g) (i : Fin n) (bs : List ℕ) :
    integratedCost α g i bs = cost (α + 1) g i bs / (2 ^ α * (α + 1)) := by
  induction bs generalizing i with
  | nil => simp [integratedCost, cost]
  | cons b bs ih =>
    have hw : 0 ≤ window g i b :=
      Finset.sum_nonneg (fun j _ => (hg.1 (i + Fin.ofNat n j)).le)
    rw [integratedCost, gap_integral α _ hα hw, ih, cost, add_div]

/-- The paper's exact minimax error in the arc-length formulation, including
the normalizing factor from the analytic integral. -/
theorem uniform_quadrature_minimax (α : ℝ) (hα : 0 < α) (s m : ℕ)
    (hs : 0 < s) (hn : s + m = n) :
    IsLeast {B : ℝ | ∃ g : Fin n → ℝ, Design g ∧ ∀ i bs,
      ValidRuns n (m + 1) bs → integratedCost α g i bs ≤ B}
      (((s : ℝ) ^ (α + 1) + m) / ((2 ^ α * (α + 1)) * (n : ℝ) ^ (α + 1))) := by
  let d : ℝ := 2 ^ α * (α + 1)
  let v := optimum (α + 1) n s m
  have hd : 0 < d := by
    dsimp [d]
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)
  have hv : v / d = ((s : ℝ) ^ (α + 1) + m) / (d * (n : ℝ) ^ (α + 1)) := by
    simp only [v, optimum, Real.div_rpow (Nat.cast_nonneg s) (Nat.cast_nonneg n),
      Real.div_rpow zero_le_one (Nat.cast_nonneg n), Real.one_rpow]
    rw [mul_one_div, ← add_div, div_div, mul_comm d]
  change IsLeast _ (((s : ℝ) ^ (α + 1) + m) / (d * (n : ℝ) ^ (α + 1)))
  rw [← hv]
  constructor
  · refine ⟨uniform n, uniform_design, ?_⟩
    intro i bs h
    rw [integratedCost_eq α hα _ uniform_design]
    exact div_le_div_of_nonneg_right (uniform_upper (α + 1) (by linarith) s m hn i bs h) hd.le
  · intro B hB
    obtain ⟨g, hg, hbound⟩ := hB
    have hnormalized : UpperBound (α + 1) g (m + 1) (B * d) := by
      intro i bs h
      have hb := hbound i bs h
      rw [integratedCost_eq α hα g hg] at hb
      exact (div_le_iff₀ hd).mp hb
    exact (div_le_iff₀ hd).mpr
      (lower_bound (α + 1) (by linarith) g hg s m hs hn hnormalized)

end PeriodicQuadrature

#print axioms PeriodicQuadrature.fixed_sample_minimax
#print axioms PeriodicQuadrature.distance_in_lifted_gap
#print axioms PeriodicQuadrature.uniform_quadrature_minimax
#print axioms PeriodicQuadrature.uniform_worst_iff
#print axioms PeriodicQuadrature.unique_of_two_survivors
#print axioms PeriodicQuadrature.sole_survivor
