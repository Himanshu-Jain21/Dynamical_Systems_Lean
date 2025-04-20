import Mathlib
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Hamiltonian mechanics: Harmonic Oscillator
-/

variable {m k : ℝ} (h_m : 0 < m) (h_k : 0 < k)
variable (x p : ℝ → ℝ) -- position, momentum as a function of time
variable (t : ℝ) -- time

/-!
Hamiltonian of the system is H = p² / (2m) + (1/2) k x²
-/
noncomputable def Hamiltonian (m k : ℝ) (x p : ℝ) : ℝ :=
  (1/(2*m))*p^2 + (1/2)*k*x^2

/-!
Proving ∂H/∂p = p/m
-/
theorem dH_dp (m k : ℝ) (x p : ℝ) :
    deriv (fun p' => Hamiltonian m k x p') p = (1/m)*p := by
  unfold Hamiltonian
  have h₁ : DifferentiableAt ℝ (fun p' => (1/(2*m))* p'^2) p :=
    DifferentiableAt.const_mul (differentiableAt_id.pow 2) (1/(2*m))

  have h₂ : DifferentiableAt ℝ (fun _ => (1 / 2) * k * x ^ 2) p :=
    differentiableAt_const _

  rw [deriv_add h₁ h₂]
  simp [mul_assoc]

/-!
Proving ∂H/∂x = kx
-/
theorem dH_dx (m k : ℝ) (x p : ℝ) :
    deriv (fun x' => Hamiltonian m k x' p) x = k*x := by
  unfold Hamiltonian
  have h₁ : DifferentiableAt ℝ (fun _ => (1/(2*m))* p^2) x :=
    differentiableAt_const _

  have h₂ : DifferentiableAt ℝ (fun x' => (1/2)*k*x'^2) x :=
    DifferentiableAt.const_mul (differentiableAt_id.pow 2) ((1/2)*k)

  rw [deriv_add h₁ h₂]
  simp [mul_assoc]
  simp [mul_comm]
  simp [mul_assoc]

/-!
Proving Hamilton's equation (assuming Newton's Laws)
dx/dt = ∂H/∂p
dp/dt = -∂H/∂x
-/
theorem hamiltons_equations
    (x p : ℝ → ℝ) (t : ℝ)
    (h_eq1 : deriv x t = (1/m)* p t)  -- Assuming Newton's Laws
    (h_eq2 : deriv p t = -k * x t) :  -- Assuming Newton's Laws
    deriv x t = deriv (fun p' => Hamiltonian m k (x t) p') (p t)
    ∧ deriv p t = -deriv (fun x' => Hamiltonian m k x' (p t)) (x t) := by

  have h1 : deriv (fun p' => Hamiltonian m k (x t) p') (p t) = (1/m) * p t :=
    dH_dp m k (x t) (p t)
  have h2 : deriv (fun x' => Hamiltonian m k x' (p t)) (x t) = k * x t :=
    dH_dx m k (x t) (p t)

  rw [h1, h2]
  constructor
  · exact h_eq1
  · rw [h_eq2]
    simp
