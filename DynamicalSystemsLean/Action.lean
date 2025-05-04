import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Real
open Interval
open Set
open MeasureTheory

variable {m k : ℝ} {h_m : 0< m} {h_k : 0<k}
variable {x v : ℝ → ℝ}
variable {t tₒ t₁ : ℝ}
variable {x₁ v₁ : ℝ}

variable {ε}
variable {η : ℝ→ℝ} {hη : η tₒ = 0 ∧ η t₁ = 0}

noncomputable def xε (t ε : ℝ) (x η : ℝ → ℝ) : ℝ :=
  x t + ε * η t

noncomputable def Lagrangian (m k : ℝ) (x v : ℝ) : ℝ :=
  (m/2)*v^2 - (k/2)*x^2

noncomputable def action (t₁ t₂ : ℝ) : ℝ :=
  ∫ t in t₁..t₂, Lagrangian m k (x t) (deriv x t)

noncomputable def action_ε (ε tₒ t₁ m k :ℝ) (η x : ℝ→ℝ) :ℝ :=
  ∫ t in tₒ..t₁, Lagrangian m k (xε t ε x η) (deriv (fun t' ↦ xε t' ε x η) t)

lemma dx_dε : deriv (fun ε' ↦ xε t ε' x η) ε = η t := by
  unfold xε
  simp [deriv_add]

lemma dx'_dε (hx : DifferentiableAt ℝ x tₒ) (hη : DifferentiableAt ℝ η tₒ)
      : deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) t) ε
      = deriv (fun t' ↦ η t') t := by
  have h : ∀ε, deriv (fun t' ↦ xε t' ε x η) t = deriv (fun t' ↦ x t') t + ε*deriv (fun t' ↦ η t') t := by
    unfold xε
    -- apply deriv_add hx
    sorry
  rw [funext h]
  simp [deriv_add]

lemma deriv_of_int :
  deriv (fun ε' ↦ action_ε ε' tₒ t₁ m k η x) ε =
    ∫ t in tₒ..t₁, deriv (fun ε' ↦ Lagrangian m k (xε t ε' x η)
      (deriv (fun t' ↦ xε t' ε' x η) t)) ε := by
      sorry

lemma chain :
  ∀ t, deriv (fun ε' ↦ Lagrangian m k (xε t ε' x η)
      (deriv (fun t' ↦ xε t' ε' x η) t)) ε =
  deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η)
  * deriv (fun ε' ↦ xε t ε' x η) ε
  +
  deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)
  * deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) t) ε := by
    sorry

lemma fundamental_lemma_interval {f : ℝ → ℝ} {tₒ t₁ : ℝ}
  (h : ∀ (η : ℝ → ℝ),
    (∀ t ∈ Icc tₒ t₁, ContinuousAt η t) →
    (η tₒ = 0 ∧ η t₁ = 0) →
    (∫ t in tₒ..t₁, f t * η t = 0)) :
  ∀ t ∈ Icc tₒ t₁, f t = 0 := by
  intro t₂ ht₂
  by_contra hft₂
  set ε := (|f t₂|) / 2 with hε_pos
  have f_nearby : ∃ δ > 0, ∀ t ∈ Icc (t₂ - δ) (t₂ + δ), |f t - f t₂| < ε := by
    sorry


theorem helper (hx : DifferentiableAt ℝ x t) (hη : DifferentiableAt ℝ η t) (hη1 : ContDiff ℝ 1 η)
    {hη2 : η tₒ = 0 ∧ η t₁ = 0} : deriv (fun ε' ↦ action_ε ε' tₒ t₁ m k η x) 0 = ∫ (x_1 : ℝ) in tₒ..t₁,
    (deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ x t') x_1)) (x x_1) -
        deriv (fun t ↦ deriv (fun v' ↦ Lagrangian m k (x t) v') (deriv (fun t' ↦ x t') t)) x_1) *
      η x_1 := by
    rw [deriv_of_int]
    let ε : ℝ := 0
    let f := fun t => deriv (fun ε' ↦ Lagrangian m k (xε t ε' x η)
      (deriv (fun t' ↦ xε t' ε' x η) t)) ε
    let g := fun t => deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η) *
      deriv (fun ε' ↦ xε t ε' x η) ε + deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)
  * deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) t) ε
    have h : EqOn f g [[tₒ, t₁]] := by
      intro t ht
      exact chain t
    rw [intervalIntegral.integral_congr h]
    unfold g
    simp [dx_dε]
    simp [dx'_dε hx hη]
    let g₁ := fun t ↦ deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η) * η t
    let g₂ := fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t) * deriv η t
    have hf : IntervalIntegrable g₁ volume tₒ t₁ := by
      -- prove using continuity of η, x, and smoothness of Lagrangian
      sorry
    have hg : IntervalIntegrable g₂ volume tₒ t₁ := by
      sorry

    rw [intervalIntegral.integral_add hf hg]
    unfold g₁ g₂
    let L_v := fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)
    let dL_v := fun t ↦ deriv (fun t ↦ L_v t) t

    -- Prove differentiability assumptions
    have hLv_diff : ∀ t ∈ [[tₒ, t₁]], HasDerivAt L_v (dL_v t) t := by
      -- You’ll unfold L_v and prove differentiability by composing deriv and contDiff
      sorry

    have hη_diff : ∀ t ∈ [[tₒ, t₁]], HasDerivAt η (deriv η t) t := by
      sorry
      -- Follows from differentiability of η
      -- exact fun t ht ↦ (hη1.2 t) -- assuming you have `hη : ContDiff ℝ 1 η` or similar

    -- Prove integrability
    have hLv_integrable : IntervalIntegrable dL_v volume tₒ t₁ := by
      -- Use contDiff or continuity + compactness
      sorry

    have hη_integrable : IntervalIntegrable (deriv η) volume tₒ t₁ := by
      -- use differentiability/contDiff of η
      sorry
        -- Apply integration by parts
    have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hLv_diff hη_diff hLv_integrable hη_integrable
    rw [h_ibp]
    simp [hη2]

    unfold dL_v
    conv_lhs => ring_nf

    have h₄ : IntervalIntegrable (fun x_1 ↦ deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) x_1)) (xε x_1 ε x η) * η x_1) volume tₒ t₁ := by sorry
    have h₅ : IntervalIntegrable (fun x ↦ deriv (fun t ↦ L_v t) x * η x) volume tₒ t₁ := by sorry

    rw [← intervalIntegral.integral_sub h₄ h₅]
    rw [intervalIntegral.integral_congr (fun x₁ hx ↦ by rw [← sub_mul])]
    unfold L_v
    unfold xε
    have ε_def : ε = 0 := rfl
    rw [ε_def]
    simp


-- axiom h_action : ∀ η : ℝ→ℝ, (ContDiff ℝ 1 η) ∧ (η tₒ = 0 ∧ η t₁ = 0) → deriv (fun ε ↦ action_ε ε tₒ t₁ m k η x) 0 = 0

-- theorem Euler_Lagrange_from_action
--       : h_action → ∀ t ∈ Icc tₒ t₁,
--     deriv (fun t ↦ deriv (fun v' ↦ Lagrangian m k (x t) v') (deriv x t)) t
--     - deriv (fun x' ↦ Lagrangian m k x' (deriv x t)) (x t) = 0 := by







-- ∫ (x_1 : ℝ) in tₒ..t₁,
--     (deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ x t') x_1)) (x x_1) -
--         deriv (fun t ↦ deriv (fun v' ↦ Lagrangian m k (x t) v') (deriv (fun t' ↦ x t') t)) x_1) *
--       η x_1




    -- -- Conclude:
    -- rw [h_ibp]
    -- have h_ibp := integral_mul_deriv_eq_deriv_mul
    --   (fun t ht ↦ HasDerivAt
    --     (fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t))
    --     (deriv (fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)) t)
    --     t)
    --   (fun t ht ↦ hη_diff t ht)
    --   hLv_integrable
    --   hη_integrable


    -- intro t
    -- specialize h t
    -- rw [h]
