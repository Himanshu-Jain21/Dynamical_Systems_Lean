import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Lagrangian Mechanics: Harmonic Oscillator
Defining the variables for the harmoninc oscillator
-/
variable {m k : ℝ} (h_m : 0 < m) (h_k : 0 < k) -- mass and spring cosntant
variable (x v : ℝ → ℝ) -- position, velocity as a function of time
variable (t : ℝ) -- time

/-!
Lagrangian of the system is L = 1/2 mv^2 - 1/2 kx^2
-/
noncomputable def Lagrangian (m k : ℝ) (x v : ℝ) : ℝ :=
  (1 / 2) * m * v ^ 2 - (1 / 2) * k * x ^ 2

/-!
Proving ∂L/∂v = mv
-/
theorem dL_dv (m k : ℝ) (x v : ℝ) :
    deriv (fun v' => Lagrangian m k x v') v = m * v := by
  unfold Lagrangian

  have h₁ : DifferentiableAt ℝ (fun v' => (1 / 2) * m * v' ^ 2) v :=
    DifferentiableAt.const_mul (differentiableAt_id.pow 2) ((1 / 2) * m)

  have h₂ : DifferentiableAt ℝ (fun _ => (1 / 2) * k * x ^ 2) v :=
    differentiableAt_const _

  rw [deriv_sub h₁ h₂]
  simp [mul_assoc]
  simp [mul_comm]
  simp [mul_assoc]

/-!
Proving ∂L/∂x = -kx
-/
theorem dL_dx (m k : ℝ) (x v : ℝ) :
    deriv (fun x' => Lagrangian m k x' v) x = -k * x := by
  unfold Lagrangian

  have h₁ : DifferentiableAt ℝ (fun _ => (1 / 2) * m * v ^ 2) x :=
    differentiableAt_const _

  have h₂ : DifferentiableAt ℝ (fun x' => (1 / 2) * k * x' ^ 2) x :=
    DifferentiableAt.const_mul (differentiableAt_id.pow 2) ((1 / 2) * k)

  rw [deriv_sub h₁ h₂]
  simp [mul_assoc]
  simp [mul_comm]
  simp [mul_assoc]

/-
Proving d(∂L/∂v)/dt = mdv/dt
-/
theorem d_dt_dL_dv :
    deriv (fun t => deriv (fun v' => Lagrangian m k (x t) v') (v t)) t = m * deriv v t := by
  have h₁ : ∀ t, deriv (fun v' => Lagrangian m k (x t) v') (v t) = m * v t := fun t ↦ dL_dv m k (x t) (v t)
  rw [funext h₁]
  simp [deriv_const_mul]

/-!
Proving Lagrange's equation (assuming Newton's Laws)
d(∂L/∂v)/dt = ∂L/∂x
-/
theorem lagrange_equation
    (h_dv : DifferentiableAt ℝ (deriv x) t)
    (h_newton : m * deriv (deriv x) t = -k * x t) :
    deriv (fun t' => deriv (fun v' => Lagrangian m k (x t') v') (deriv x t')) t -
    deriv (fun x' => Lagrangian m k x' (deriv x t)) (x t) = 0 := by

  let f := fun t' => deriv (fun v' => Lagrangian m k (x t') v') (deriv x t')
  let g := fun t' => m * deriv x t'

  have h_eq : f = g := by
    apply funext
    intro t'
    exact dL_dv m k (x t') (deriv x t')
  have h1 : deriv f t = deriv g t := by rw [h_eq]

  have h1' : deriv g t = m * deriv (deriv x) t := by
    simp [g, deriv_const_mul, h_dv]

  have h_dLdv_dt : deriv f t = m * deriv (deriv x) t := by
    rw [h1, h1']

  have h_dLdx : deriv (fun x' => Lagrangian m k x' (deriv x t)) (x t)
              = -k * x t := dL_dx m k (x t) (deriv x t)

  rw [h_dLdv_dt, h_dLdx, h_newton]
  simp
