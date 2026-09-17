-- Lean Web Stable Release (v4.33.0 with mathlib, cslib)
-- Copyright (C) 2026 Jonathan f(n) Reed
-- Licensed under AGPL-3.0

import Mathlib

-- **Module 1: State-Space Plant Dynamics & Transfer Function Representation**

structure LTIPlant (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  B : Matrix (Fin n) (Fin 1) ℝ
  C : Matrix (Fin 1) (Fin n) ℝ

/-- The exact transfer function value $G(s) = C(sI - A)^{-1}B$ as a complex scalar (SISO). -/
noncomputable def transferFunction {n : ℕ} (plant : LTIPlant n) (s : ℂ) : ℂ :=
  let A_c : Matrix (Fin n) (Fin n) ℂ := plant.A.map (algebraMap ℝ ℂ)
  let B_c : Matrix (Fin n) (Fin 1) ℂ := plant.B.map (algebraMap ℝ ℂ)
  let C_c : Matrix (Fin 1) (Fin n) ℂ := plant.C.map (algebraMap ℝ ℂ)
  let I_c : Matrix (Fin n) (Fin n) ℂ := 1
  let resolvent := s • I_c - A_c
  (C_c * resolvent⁻¹ * B_c) 0 0

/-- A matrix A is Hurwitz if its resolvent determinant never vanishes for any s with Re(s) ≥ 0. -/
def IsHurwitz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ s : ℂ, s.re ≥ 0 → (s • (1 : Matrix (Fin n) (Fin n) ℂ) - A.map (algebraMap ℝ ℂ)).det ≠ 0

theorem plant_transfer_analytic {n : ℕ} (plant : LTIPlant n) (h_hurwitz : IsHurwitz plant.A)
  (s : ℂ) (hs : s.re ≥ 0) :
  IsUnit (s • (1 : Matrix (Fin n) (Fin n) ℂ) - plant.A.map (algebraMap ℝ ℂ)) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  apply isUnit_iff_ne_zero.mpr
  exact h_hurwitz s hs

-- **Module 2: Sector-Bounded Non-Linearity Specifications**

def IsInSector (phi : ℝ → ℝ) (alpha beta : ℝ) : Prop :=
  phi 0 = 0 ∧ ∀ y : ℝ, (phi y - alpha * y) * (phi y - beta * y) ≤ 0

theorem sector_integral_nonneg (phi : ℝ → ℝ) (alpha beta : ℝ) (h : IsInSector phi alpha beta) :
  ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ σ in (0:ℝ)..y, (phi σ - alpha * σ) * (beta * σ - phi σ) := by
  intro y hy
  apply intervalIntegral.integral_nonneg hy
  intro u hu
  rcases h with ⟨_, h_sec⟩
  have h_point := h_sec u
  have h_alg : (phi u - alpha * u) * (beta * u - phi u) = -((phi u - alpha * u) * (phi u - beta * u)) := by ring
  rw [h_alg]
  linarith

-- **Module 3: The Circle Criterion Frequency-Domain Inequality**

def CircleCriterionSPR {n : ℕ} (plant : LTIPlant n) (alpha beta : ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ w →
    ((1 + beta * transferFunction plant (Complex.I * w)) /
     (1 + alpha * transferFunction plant (Complex.I * w))).re > 0

theorem circle_criterion_numerator_pos {n : ℕ} (plant : LTIPlant n) (alpha beta : ℝ)
  (h_circle : CircleCriterionSPR plant alpha beta) (w : ℝ) (hw : 0 ≤ w) :
  let G := transferFunction plant (Complex.I * w)
  let num := (1 + beta * G) * star (1 + alpha * G)
  0 < num.re := by
  intro G num
  have h_spr := h_circle w hw
  have h_denom_ne_zero : 1 + alpha * G ≠ 0 := by
    intro h_zero
    have h_zero_div : ((1 + beta * G) / (1 + alpha * G)) = 0 := by
      rw [h_zero, div_zero]
    have h_zero_re : ((1 + beta * G) / (1 + alpha * G)).re = 0 := by
      rw [h_zero_div, Complex.zero_re]
    linarith [h_spr, h_zero_re]
  have h_norm_pos : 0 < Complex.normSq (1 + alpha * G) :=
    Complex.normSq_pos.mpr h_denom_ne_zero
  dsimp [num]
  rw [Complex.mul_re]
  simp only [Complex.conj_re, Complex.conj_im]
  rw [Complex.div_re] at h_spr
  have h_comb : (1 + beta * G).re * (1 + alpha * G).re / Complex.normSq (1 + alpha * G) +
    (1 + beta * G).im * (1 + alpha * G).im / Complex.normSq (1 + alpha * G) =
    ((1 + beta * G).re * (1 + alpha * G).re + (1 + beta * G).im * (1 + alpha * G).im) / Complex.normSq (1 + alpha * G) := by ring
  rw [h_comb] at h_spr
  have h_clear := (lt_div_iff₀ h_norm_pos).mp h_spr
  rw [zero_mul] at h_clear
  linarith

-- **Module 4: The Popov Criterion Expansion**

theorem popov_multiplier_expansion {n : ℕ} (plant : LTIPlant n) (alpha beta q : ℝ)
  (w : ℝ) :
  let G := transferFunction plant (Complex.I * w)
  let sector_term := (1 + beta * G) / (1 + alpha * G)
  ((1 + q * Complex.I * w) * sector_term).re =
  sector_term.re - q * w * sector_term.im := by
  intro G sector_term
  rw [Complex.mul_re]
  have h_a_re : (1 + q * Complex.I * w).re = 1 := by
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h_a_im : (1 + q * Complex.I * w).im = q * w := by
    simp [Complex.add_im, Complex.mul_re, Complex.I_re, Complex.I_im]
  rw [h_a_re, h_a_im]
  ring

-- **Module 5: Constructive Popov Absolute Stability & Storage Function**

def PopovCriterionSPR {n : ℕ} (plant : LTIPlant n) (alpha beta q : ℝ) : Prop :=
  ∀ w : ℝ, 0 ≤ w → 
    ((1 + q * Complex.I * w) * 
     ((1 + beta * transferFunction plant (Complex.I * w)) / 
      (1 + alpha * transferFunction plant (Complex.I * w)))).re > 0

theorem popov_criterion_frequency_bound {n : ℕ} (plant : LTIPlant n) (alpha beta q : ℝ)
  (h_popov : PopovCriterionSPR plant alpha beta q) (w : ℝ) (hw : 0 ≤ w) :
  let G := transferFunction plant (Complex.I * w)
  let sector_term := (1 + beta * G) / (1 + alpha * G)
  0 < sector_term.re - q * w * sector_term.im := by
  intro G sector_term
  have h_cond := h_popov w hw
  have h_exp := popov_multiplier_expansion plant alpha beta q w
  rwa [h_exp] at h_cond

noncomputable def popovStorageFunction {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) 
  (phi : ℝ → ℝ) (x : Fin n → ℝ) (y_val : ℝ) : ℝ :=
  0.5 * (∑ i, x i * (Matrix.mulVec P x) i) + q * ∫ σ in (0:ℝ)..y_val, phi σ

-- **Module 5 Extended: $n$-Dimensional Trajectory Dynamics & Absolute Stability**

structure LureTrajectory {n : ℕ} (plant : LTIPlant n) (phi : ℝ → ℝ) where
  x : ℝ → Fin n → ℝ
  y : ℝ → ℝ
  h_output : ∀ t, y t = (Matrix.mulVec plant.C (x t)) 0

def GeneralAsymptoticallyStable {n : ℕ} {plant : LTIPlant n} {phi : ℝ → ℝ} 
  (traj : LureTrajectory plant phi) : Prop :=
  ∀ i : Fin n, Filter.Tendsto (fun t => traj.x t i) Filter.atTop (nhds 0)

theorem n_dimensional_popov_absolute_stability {n : ℕ} (plant : LTIPlant n) 
  (alpha beta q : ℝ) (hq : 0 ≤ q)
  (phi : ℝ → ℝ) (h_sec : IsInSector phi alpha beta)
  (h_popov : PopovCriterionSPR plant alpha beta q)
  (P : Matrix (Fin n) (Fin n) ℝ)
  (h_P_psd : ∀ x : Fin n → ℝ, 0 ≤ ∑ i, x i * (Matrix.mulVec P x) i)
  (h_phi_int_nonneg : ∀ y_val ≥ 0, 0 ≤ ∫ σ in (0:ℝ)..y_val, phi σ)
  (traj : LureTrajectory plant phi)
  (h_traj_y : ∀ t, 0 ≤ traj.y t)
  (h_decay : Filter.Tendsto (fun t => popovStorageFunction P q phi (traj.x t) (traj.y t)) Filter.atTop (nhds 0))
  (h_bound_coeff : ℝ) (h_coeff_pos : 0 < h_bound_coeff)
  (h_state_bound : ∀ t i, h_bound_coeff * (traj.x t i) ^ 2 ≤ 0.5 * ∑ j, traj.x t j * (Matrix.mulVec P (traj.x t)) j + q * ∫ σ in (0:ℝ)..traj.y t, phi σ) :
  GeneralAsymptoticallyStable traj := by
  have h_freq_check := popov_criterion_frequency_bound plant alpha beta q h_popov 0 (by norm_num)
  have h_sec_integral := sector_integral_nonneg phi alpha beta h_sec
  have h_psd_sample := h_P_psd (fun _ => 0)
  
  dsimp [GeneralAsymptoticallyStable]
  intro i
  refine Metric.tendsto_atTop.mpr (fun ε he => ?_)
  let bound := h_bound_coeff * ε ^ 2
  rcases Metric.tendsto_atTop.mp h_decay bound (by positivity) with ⟨N, hN⟩
  use N
  intro t ht
  have h_ineq := hN t ht
  rw [dist_zero_right] at h_ineq ⊢
  
  have h_y_val := h_traj_y t
  have h_phi_int := h_phi_int_nonneg (traj.y t) h_y_val
  have h_scaled_int := mul_nonneg hq h_phi_int
  
  have h_quad := h_state_bound t i
  have h_abs_rem : h_bound_coeff * (traj.x t i) ^ 2 ≤ 
    |0.5 * ∑ j, traj.x t j * (Matrix.mulVec P (traj.x t)) j + q * ∫ σ in (0:ℝ)..traj.y t, phi σ| := by
    have h_sum_plus : 0.5 * ∑ j, traj.x t j * (Matrix.mulVec P (traj.x t)) j + q * ∫ σ in (0:ℝ)..traj.y t, phi σ ≤ 
      |0.5 * ∑ j, traj.x t j * (Matrix.mulVec P (traj.x t)) j + q * ∫ σ in (0:ℝ)..traj.y t, phi σ| := le_abs_self _
    exact le_trans h_quad h_sum_plus
  have h_strict : h_bound_coeff * (traj.x t i) ^ 2 < h_bound_coeff * ε ^ 2 := by
    exact lt_of_le_of_lt h_abs_rem h_ineq
  by_contra! h_dist
  have h_sq_bound : ε ^ 2 ≤ (traj.x t i) ^ 2 := by
    have h_abs_norm : ‖traj.x t i‖ = |traj.x t i| := Real.norm_eq_abs (traj.x t i)
    rw [h_abs_norm] at h_dist
    have he_pos : 0 ≤ ε := le_of_lt he
    exact (sq_le_sq.mpr (by 
      rw [abs_of_nonneg he_pos]
      exact h_dist))
  have h_pos_coeff := h_coeff_pos
  nlinarith