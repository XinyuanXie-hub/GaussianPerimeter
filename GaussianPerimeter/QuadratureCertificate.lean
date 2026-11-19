module

public import GaussianPerimeter.Quadrature

import GaussianPerimeter.Prefactor
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

public section

open Finset

namespace GaussianPerimeter

local notation "A" => (6131 / 5000)
local notation "B" => (2387 / 1000)
local notation "F" => lowerBoundIntegrand A B

/-- The interior grid points of a mesh of width \(1/2048\) on \([-15/4,5/4]\). -/
private def gridPoint (i : ℕ) : ℚ := -(15 / 4) + ((i : ℚ) + 1) / 2048

/-- A lower enclosure of one integrand value in units of \(10^{-9}\).
A final zero pads the list to a multiple of the block size. -/
private def sample (i : ℕ) : ℤ :=
  if i < 10239 then
    let x := gridPoint i
    ⌊1000000000 * expLower (-x ^ 2 - B * expUpper (A ^ 2 * x))⌋
  else 0

private theorem sample_le (i : ℕ) (hi : i < 10239) :
    (sample i : ℝ) / 1000000000 ≤ F (-(15 / 4) + ((i : ℝ) + 1) / 2048) := by
  have hiRat : (i : ℚ) ≤ 10239 := by exact_mod_cast hi.le
  have hiRat₀ : (0 : ℚ) ≤ i := by positivity
  have harg : |(A : ℚ) ^ 2 * gridPoint i| ≤ 32 := by
    unfold gridPoint
    rw [abs_le]
    norm_num
    constructor <;> linarith only [hiRat, hiRat₀]
  have hUpper := exp_le_expUpper harg
  let x := gridPoint i
  have hx : (x : ℝ) = -(15 / 4) + ((i : ℝ) + 1) / 2048 := by
    dsimp [x, gridPoint]
    push_cast
    rfl
  have hFloor := Int.floor_le (1000000000 * expLower (-x ^ 2 - B * expUpper (A ^ 2 * x)))
  have hFloor' : (sample i : ℝ) ≤
      (1000000000 : ℝ) * (expLower (-x ^ 2 - B * expUpper (A ^ 2 * x)) : ℝ) := by
    rw [sample, ite_eq_left hi]
    exact_mod_cast hFloor
  have hOuter := expLower_le_exp (-x ^ 2 - B * expUpper (A ^ 2 * x))
  rw [← hx, lowerBoundIntegrand]
  refine ((div_le_iff₀ (by norm_num : (0 : ℝ) < 1000000000)).2 (by
    simpa [mul_comm] using hFloor')).trans (hOuter.trans (Real.exp_le_exp.mpr ?_))
  push_cast at hUpper ⊢
  gcongr

private def sumSamples (start : ℕ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumSamples start n + sample (start + n)

private theorem sumSamples_eq (start n : ℕ) :
    sumSamples start n = ∑ i ∈ range n, sample (start + i) := by
  induction n with
  | zero => simp [sumSamples]
  | succ n ih => rw [sumSamples, sum_range_succ, ih]

/-- Blockwise summation keeps the reduction depth independent of the full mesh size. -/
private def sumBuckets : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumBuckets n + sumSamples (320 * n) 320

private theorem sumBuckets_eq (n : ℕ) :
    sumBuckets n = ∑ i ∈ range (320 * n), sample i := by
  induction n with
  | zero => simp [sumBuckets]
  | succ n ih =>
    rw [sumBuckets, ih, sumSamples_eq, Nat.mul_succ, sum_range_add]

/-- Integer lower bounds for each block of 320 samples. -/
private def bucketLower (k : ℕ) : ℤ :=
  (#[446366, 1403850, 4117277, 11420510, 30080485, 75311966, 179250084, 405452268,
    871122108, 1776519042, 3435704486, 6293798777, 10904935774, 17837760934,
    27481863818, 39760773904, 53819945108, 67836503856, 79146597553, 84838492080,
    82764148561, 72612956187, 56443046614, 38147572977, 21894730030, 10360852799,
    3895703951, 1111409668, 227126040, 30936050, 2552680, 96424] : Array ℤ)[k]!

set_option maxRecDepth 15000 in
set_option maxHeartbeats 0 in
private theorem bucketLower_le (k : ℕ) (hk : k < 32) :
    bucketLower k ≤ sumSamples (320 * k) 320 := by
  interval_cases k <;> decide +kernel

private def sumBounds : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumBounds n + bucketLower n

private theorem sumBounds_le (n : ℕ) (hn : n ≤ 32) : sumBounds n ≤ sumBuckets n := by
  induction n with
  | zero => simp [sumBounds, sumBuckets]
  | succ n ih =>
    rw [sumBounds, sumBuckets]
    exact add_le_add (ih (Nat.le_of_succ_le hn)) (bucketLower_le n hn)

-- 682202112000 is 0.3331065 × 2048 × 10^9.
private theorem sumSamples_bound : (682202112000 : ℤ) ≤ sumBuckets 32 :=
  (show (682202112000 : ℤ) ≤ sumBounds 32 by decide +kernel).trans
    (sumBounds_le 32 (by decide))

/-- Certified numerical lower bound for the integral in Theorem 1, equation (14). -/
theorem lowerBound_integral :
    (0.333104 : ℝ) ≤ ∫ x in (-6 : ℝ)..6, F x := by
  apply lowerBound_integral_of_trapezoidal
  have hSum := sumSamples_bound
  rw [sumBuckets_eq, show (320 * 32 : ℕ) = 10239 + 1 by rfl, sum_range_succ,
    show sample 10239 = 0 by rfl, add_zero] at hSum
  have hSum' : (682202112000 : ℝ) ≤ ∑ i ∈ range 10239, (sample i : ℝ) := by
    exact_mod_cast hSum
  have hf : ∀ i ∈ range 10239,
      (sample i : ℝ) / 1000000000 ≤
      F (-(15 / 4) + ((i : ℝ) + 1) / 2048) :=
    fun i hi => sample_le i (mem_range.mp hi)
  have hm : (∑ i ∈ range 10239, (sample i : ℝ)) / 1000000000 ≤
      ∑ i ∈ range 10239, F (-(15 / 4) + ((i : ℝ) + 1) / 2048) := by
    rw [div_eq_mul_inv, sum_mul]
    exact sum_le_sum fun i hi => by
      rw [← div_eq_mul_inv]
      exact hf i hi
  rw [trapezoidal_integral]
  change (0.3331065 : ℝ) ≤
    ((5 / 4 - -(15 / 4)) / 10240) *
      ((F (-(15 / 4)) + F (5 / 4)) / 2 +
        ∑ i ∈ range 10239, F (-(15 / 4) + ((i : ℝ) + 1) * (5 / 4 - -(15 / 4)) / 10240))
  have hgrid (i : ℕ) :
      ((i : ℝ) + 1) * (5 / 4 - -(15 / 4)) / 10240 = ((i : ℝ) + 1) / 2048 := by ring
  simp_rw [hgrid]
  have hEnds : 0 ≤ (F (-(15 / 4)) + F (5 / 4)) / 2 := by
    unfold lowerBoundIntegrand
    positivity
  linarith only [hSum', hm, hEnds]

/-- The numerical lower bound in Theorem 1 for the parameters in equation (14). -/
theorem gaussianLowerBound_numeric :
    (0.31258 : ℝ) ≤ (B * A * Real.exp (-A ^ 4 / 4) / Real.sqrt Real.pi) *
      (∫ x in (-6 : ℝ)..6, Real.exp (-x ^ 2 - B * Real.exp (A ^ 2 * x))) := by
  calc
    _ ≤ (0.938393 : ℝ) * (0.333104 : ℝ) := by norm_num
    _ ≤ _ := mul_le_mul gaussianPrefactor_lower lowerBound_integral (by norm_num)
      ((show (0 : ℝ) ≤ 0.938393 by norm_num).trans gaussianPrefactor_lower)

end GaussianPerimeter
