import DynamicalSystemsLean.Lagrangian
import DynamicalSystemsLean.Hamiltonian

variable {m k : ℝ}

/-
dL_dv (m k x v : ℝ) : deriv (fun v' ↦ Lagrangian m k x v') v = m * v
-/
#check Lagrangian

/-
dL_dv (m k x v : ℝ) : deriv (fun v' ↦ Lagrangian m k x v') v = m * v
-/
#check Hamiltonian

/-
dL_dv (m k x v : ℝ) : deriv (fun v' ↦ Lagrangian m k x v') v = m * v
-/
#check dL_dv

noncomputable def v_p (m p : ℝ) : ℝ := (1/m) * p

noncomputable def p_v (m v : ℝ) : ℝ := m*v

/-!
Hamiltonian from Lagrangian
-/
theorem L2H
    (x p : ℝ) (h_m : 0 < m) :
    Hamiltonian m k x p = p * (v_p m p) - Lagrangian m k x (v_p m p) := by
  unfold Hamiltonian Lagrangian v_p
  symm
  simp [add_sub_assoc]
  simp [mul_assoc]
  simp [mul_pow]
  have h1 : p * (m⁻¹ * p) = m⁻¹ * p ^ 2 := by
    simp [←mul_assoc, mul_comm]
    ring
  have h2 : 2⁻¹ * (m * ((m ^ 2)⁻¹ * p ^ 2)) = 2⁻¹ * (m⁻¹ * p ^ 2) := by
    rw [←mul_assoc]
    field_simp [h_m]
    ring
  rw [h1, h2]
  ring

/-!
Lagrangian from Hamiltonian
-/
theorem H2L
    (x v : ℝ) (h_m : 0 < m) :
    Lagrangian m k x v = (p_v m v)*v - Hamiltonian m k x (p_v m v):= by
  unfold Lagrangian Hamiltonian p_v
  symm
  rw [sub_add_eq_sub_sub]
  rw [mul_pow]
  have h1 : 1 / (2 * m) * (m ^ 2 * v ^ 2) = (1/2)* m*v^2 := by
    simp [mul_comm]
    simp [←mul_assoc]
    simp [mul_comm]
    ring_nf
    field_simp [h_m]
    ring
  rw [h1]
  ring
