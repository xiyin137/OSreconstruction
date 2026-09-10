import OSReconstruction.Wightman.Reconstruction.WickRotation.OSIIQuantitativeDecay
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Uniform arithmetic for OS II seminorm conventions

Dimension factors of the form `(D*n+1)^(n*s)` are absorbed by exponential and
factorial constants uniformly in arity. No asymptotic norm-equivalence choice
is made separately for each `n`.
-/

noncomputable section

open scoped Classical

namespace OSReconstruction

theorem nat_pow_self_le_factorial_sq (n : Nat) : n ^ n <= n.factorial ^ 2 := by
  have hp : (∏ j : Fin n, (j.val + 1)) = n.factorial := by
    exact (Fin.prod_univ_eq_prod_range (fun j : Nat => j + 1) n).trans
      (Finset.prod_range_add_one_eq_factorial n)
  have hrev : (∏ j : Fin n, ((Fin.rev j).val + 1)) = n.factorial := by
    rw [← hp]
    exact Equiv.prod_comp (Fin.revPerm (n := n)) (fun j : Fin n => j.val + 1)
  calc
    n ^ n = ∏ _ : Fin n, n := by simp
    _ <= ∏ j : Fin n, (j.val + 1) * ((Fin.rev j).val + 1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro j _
      have hj : j.val + (Fin.rev j).val + 1 = n := by simp [Fin.val_rev]; omega
      nlinarith
    _ = n.factorial ^ 2 := by rw [Finset.prod_mul_distrib, hp, hrev, pow_two]

theorem osiiDimensionPower_le_factorial (D n s : Nat) :
    (n * D + 1 : Real) ^ (n * s) <=
      ((D + 1 : Real) ^ s) ^ n * (n.factorial : Real) ^ (2 * s) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn1 : 1 <= n := Nat.pos_of_ne_zero hn
  have hbase : n * D + 1 <= (D + 1) * n := by nlinarith
  have hnat : (n * D + 1) ^ (n * s) <= ((D + 1) ^ s) ^ n * n.factorial ^ (2 * s) := by
    calc
      _ <= ((D + 1) * n) ^ (n * s) := by gcongr
      _ = ((D + 1) ^ s) ^ n * (n ^ n) ^ s := by
        simp only [mul_pow, ← pow_mul]
        rw [Nat.mul_comm s n]
      _ <= ((D + 1) ^ s) ^ n * (n.factorial ^ 2) ^ s := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.zero_le _) (nat_pow_self_le_factorial_sq n) s) (Nat.zero_le _)
      _ = _ := by simp only [← pow_mul]
  exact_mod_cast hnat

theorem three_pow_le_three_mul_factorial_sq (n : Nat) :
    (3 : Nat) ^ n <= 3 * n.factorial ^ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num
    have hn1 : 1 <= n := Nat.pos_of_ne_zero hn
    have hfactor : 3 <= (n + 1) ^ 2 := by nlinarith
    rw [pow_succ, Nat.factorial_succ]
    calc
      _ <= (3 * n.factorial ^ 2) * 3 := Nat.mul_le_mul_right _ ih
      _ <= (3 * n.factorial ^ 2) * (n + 1) ^ 2 := Nat.mul_le_mul_left _ hfactor
      _ = _ := by ring

theorem exponential_le_factorial_power (b : Real) (hb : 0 <= b) :
    ∃ (C : Real) (q : Nat), 0 < C ∧ ∀ n : Nat,
      b ^ n <= C * (n.factorial : Real) ^ (2 * q) := by
  let q := Nat.ceil b
  have hbq : b <= (3 : Real) ^ q := (Nat.le_ceil b).trans (natCast_le_three_pow q)
  refine ⟨3 ^ q, q, by positivity, ?_⟩
  intro n
  have h3 : (3 : Real) ^ n <= 3 * (n.factorial : Real) ^ 2 := by
    exact_mod_cast three_pow_le_three_mul_factorial_sq n
  calc
    _ <= ((3 : Real) ^ q) ^ n := pow_le_pow_left₀ hb hbq n
    _ = ((3 : Real) ^ n) ^ q := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ <= (3 * (n.factorial : Real) ^ 2) ^ q := pow_le_pow_left₀ (by positivity) h3 q
    _ = _ := by rw [mul_pow, ← pow_mul]

theorem exponential_dimensionPower_le_factorial (D s : Nat) (b gamma : Real)
    (hb : 0 <= b) :
    ∃ (C Gamma : Real), 0 < C ∧ ∀ n : Nat,
      b ^ n * (n.factorial : Real) ^ gamma * (n * D + 1 : Real) ^ (n * s) <=
        C * (n.factorial : Real) ^ Gamma := by
  obtain ⟨C, q, hC, hpow⟩ := exponential_le_factorial_power
    (b * (D + 1 : Real) ^ s) (by positivity)
  refine ⟨C, gamma + ((2 * s + 2 * q : Nat) : Real), hC, ?_⟩
  intro n
  have hf : 0 < (n.factorial : Real) := by exact_mod_cast Nat.factorial_pos n
  rw [Real.rpow_add hf, Real.rpow_natCast]
  calc
    _ <= (b ^ n * (n.factorial : Real) ^ gamma) *
        (((D + 1 : Real) ^ s) ^ n * (n.factorial : Real) ^ (2 * s)) :=
      mul_le_mul_of_nonneg_left (osiiDimensionPower_le_factorial D n s) (by positivity)
    _ = (b * (D + 1 : Real) ^ s) ^ n *
        ((n.factorial : Real) ^ gamma * (n.factorial : Real) ^ (2 * s)) := by
      rw [mul_pow]
      ring
    _ <= (C * (n.factorial : Real) ^ (2 * q)) *
        ((n.factorial : Real) ^ gamma * (n.factorial : Real) ^ (2 * s)) :=
      mul_le_mul_of_nonneg_right (hpow n) (by positivity)
    _ = _ := by rw [pow_add]; ring

end OSReconstruction
