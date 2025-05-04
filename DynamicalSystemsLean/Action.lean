import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open Real
open Interval
open Set
open MeasureTheory intervalIntegral

/-!
# Lagrangian Mechanics: Harmonic Oscillator
Proving the Euler-Lagrange equation from the principle of least action
-/

variable {m k : ℝ} {h_m : 0< m} {h_k : 0<k}
variable {x v : ℝ → ℝ}
variable {t tₒ t₁ : ℝ}

variable {ε}
variable {η : ℝ→ℝ}

noncomputable def xε (t ε : ℝ) (x η : ℝ → ℝ) : ℝ :=
  x t + ε * η t

noncomputable def Lagrangian (m k : ℝ) (x v : ℝ) : ℝ :=
  (m/2)*v^2 - (k/2)*x^2

/-!
Defining the action as a function of ε from Lagrangian
-/
noncomputable def action_ε (ε tₒ t₁ m k :ℝ) (η x : ℝ→ℝ) :ℝ :=
  ∫ t in tₒ..t₁, Lagrangian m k (xε t ε x η) (deriv (fun t' ↦ xε t' ε x η) t)

/-!
Derivative of parameterizerd curve x(ε) with respect to ε
-/
lemma dx_dε : deriv (fun ε' ↦ xε t ε' x η) ε = η t := by
  unfold xε
  simp [deriv_add]

/-!
Derivative of x'(ε) with respect to ε
-/
lemma dx'_dε (hx : DifferentiableAt ℝ x tₒ)
                      (hη : DifferentiableAt ℝ η tₒ) :
    deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) tₒ) ε
    = deriv η tₒ := by
  unfold xε
  have h : ∀ ε', deriv (fun t' ↦ x t' + ε' * η t') tₒ = deriv x tₒ + ε' * deriv η tₒ := by
    intro ε'
    have h₁ := hx
    have h₂ := hη.const_mul ε'
    have : deriv (fun y ↦ ε' * η y) tₒ = ε' * deriv η tₒ := by simp [deriv_const_mul, hη]
    rw [deriv_add h₁ h₂, this]
  simp [h]

/-!
Changing the order of derivative and integral (yet to be proven)
-/
lemma deriv_of_int :
  deriv (fun ε' ↦ action_ε ε' tₒ t₁ m k η x) ε =
    ∫ t in tₒ..t₁, deriv (fun ε' ↦ Lagrangian m k (xε t ε' x η)
      (deriv (fun t' ↦ xε t' ε' x η) t)) ε := by
      sorry

/-!
Chain rule (yet to be proven)
-/
lemma chain :
  ∀ t, deriv (fun ε' ↦ Lagrangian m k (xε t ε' x η)
      (deriv (fun t' ↦ xε t' ε' x η) t)) ε =
  deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η)
  * deriv (fun ε' ↦ xε t ε' x η) ε
  +
  deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)
  * deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) t) ε := by
    sorry


theorem helper
    (hx' : ∀ t ∈ Icc tₒ t₁, DifferentiableAt ℝ x t)
    (hη' : ∀ t ∈ Icc tₒ t₁, DifferentiableAt ℝ η t)
    (h_order : tₒ ≤ t₁)
    (hL : ContDiff ℝ 2 (fun p : ℝ × ℝ => Lagrangian m k p.1 p.2))
    (ht' : t ∈ Icc tₒ t₁)
    (hη2 : η tₒ = 0 ∧ η t₁ = 0) : deriv (fun ε' ↦ action_ε ε' tₒ t₁ m k η x) 0 = ∫ (x_1 : ℝ) in tₒ..t₁,
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
    let f' := fun t =>  deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η) * η t +
      deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t) * deriv (fun ε' ↦ deriv (fun t' ↦ xε t' ε' x η) t) ε
    let g' := fun t =>  deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η) * η t +
      deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t) * deriv η t
    have h' : EqOn f' g' [[tₒ, t₁]] := by
      intro x₁ hx₁
      have h'' : [[tₒ, t₁]] = Icc tₒ t₁ := by rw [Set.uIcc_of_le h_order]
      rw [h''] at hx₁
      unfold f' g'
      simp [dx'_dε (hx' x₁ hx₁) (hη' x₁ hx₁)]
    rw [intervalIntegral.integral_congr h']

    let g₁ := fun t ↦ deriv (fun x' ↦ Lagrangian m k x' (deriv (fun t' ↦ xε t' ε x η) t)) (xε t ε x η) * η t
    let g₂ := fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t) * deriv η t
    have hf : IntervalIntegrable g₁ volume tₒ t₁ := by sorry
    have hg : IntervalIntegrable g₂ volume tₒ t₁ := by sorry

    rw [intervalIntegral.integral_add hf hg]
    unfold g₁ g₂
    let L_v := fun t ↦ deriv (fun v' ↦ Lagrangian m k (xε t ε x η) v') (deriv (fun t' ↦ xε t' ε x η) t)
    let dL_v := fun t ↦ deriv (fun t ↦ L_v t) t

    -- Hypothesis for differentiability
    have hLv_diff : ∀ t ∈ [[tₒ, t₁]], HasDerivAt L_v (dL_v t) t := by sorry
    have hη_diff : ∀ t ∈ [[tₒ, t₁]], HasDerivAt η (deriv η t) t := by sorry

    -- Hypothesis for integrability
    have hLv_integrable : IntervalIntegrable dL_v volume tₒ t₁ := by sorry
    have hη_integrable : IntervalIntegrable (deriv η) volume tₒ t₁ := by sorry

    -- Applying integration by parts
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

-- Only part left is using the helper theorem to prove the lagrange's equation
