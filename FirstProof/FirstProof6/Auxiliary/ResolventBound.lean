/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import FirstProof.FirstProof6.Auxiliary.BarrierPotential

/-!
# Problem 6: Large epsilon-light vertex subsets -- Resolvent Bound

The main lemma `psd_resolvent_trace_bound` establishing:
`tr((U^{-1} - B)^{-1}) <= tr(U) + tr(B*U^2) / (1 - tr(B*U))`
via matrix square root and spectral decomposition.

## Main theorems

- `Problem6.psd_resolvent_trace_bound`: PSD resolvent trace bound
-/

open Finset Matrix BigOperators

noncomputable section

namespace Problem6

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PSD resolvent trace identity**: If U is PD, B is PSD, K = U^{1/2}·B·U^{1/2}
    is PSD with tr(K) = tr(B·U) < 1, then:
    tr((U⁻¹ - B)⁻¹) = tr(U) + tr(P · (I-K)⁻¹)
    where P = (K^{1/2}·U^{1/2})·(K^{1/2}·U^{1/2})ᴴ is PSD with tr(P) = tr(B·U²).
    The proof uses the conjugation identity:
    (U⁻¹ - B)⁻¹ = U^{1/2}·(I - K)⁻¹·U^{1/2}
    and the decomposition (I-K)⁻¹ = I + K·(I-K)⁻¹ with K commuting with (I-K)⁻¹. -/
lemma psd_resolvent_trace_bound
    (U B : Matrix V V ℝ)
    (hU : U.PosDef) (hB : B.PosSemidef)
    (htrBU_lt : (B * U).trace < 1)
    (_htrBU_nn : 0 ≤ (B * U).trace) :
    (U⁻¹ - B)⁻¹.trace ≤ U.trace + (B * U * U).trace / (1 - (B * U).trace) := by
  classical
  -- === Step 0: Spectral decomposition of U ===
  -- U is PD hence Hermitian; diagonalize as eigP * diag(d) * eigP*
  set hU_herm := hU.isHermitian with hU_herm_def
  set eigP := (hU_herm.eigenvectorUnitary : Matrix V V ℝ) with hP_def
  set d := hU_herm.eigenvalues with hd_def
  -- Unitary properties of eigP
  have hP_star_mul : star eigP * eigP = 1 :=
    Unitary.coe_star_mul_self hU_herm.eigenvectorUnitary
  have hP_mul_star : eigP * star eigP = 1 :=
    Unitary.coe_mul_star_self hU_herm.eigenvectorUnitary
  -- Spectral theorem: U = eigP * diag(d) * eigP*
  have hU_eq : U = eigP * Matrix.diagonal d * star eigP := by
    have h := hU_herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at h
    exact h
  -- Eigenvalues are positive (U is PD)
  have hd_pos : ∀ i, 0 < d i := hU.eigenvalues_pos
  -- === Step 1: Construct U^{1/2} = eigP * diag(√d) * eigP* ===
  set sqrtd := fun i => Real.sqrt (d i) with sqrtd_def
  set Uhalf := eigP * Matrix.diagonal sqrtd * star eigP with Uhalf_def
  -- √d_i > 0
  have hsqrtd_pos : ∀ i, 0 < sqrtd i := fun i => Real.sqrt_pos_of_pos (hd_pos i)
  have hsqrtd_ne : ∀ i, sqrtd i ≠ 0 := fun i => ne_of_gt (hsqrtd_pos i)
  -- U^{1/2} * U^{1/2} = U (since diag(√d) * diag(√d) = diag(d))
  have hUhalf_sq : Uhalf * Uhalf = U := by
    rw [Uhalf_def, hU_eq]
    calc eigP * Matrix.diagonal sqrtd * star eigP *
        (eigP * Matrix.diagonal sqrtd * star eigP)
      = eigP * Matrix.diagonal sqrtd * (star eigP * eigP) *
          Matrix.diagonal sqrtd * star eigP := by
          simp only [Matrix.mul_assoc]
      _ = eigP * (Matrix.diagonal sqrtd * Matrix.diagonal sqrtd) * star eigP := by
          rw [hP_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = eigP * Matrix.diagonal d * star eigP := by
          rw [Matrix.diagonal_mul_diagonal]
          have hsq : (fun i => sqrtd i * sqrtd i) = d := by
            ext i; exact Real.mul_self_sqrt (le_of_lt (hd_pos i))
          rw [hsq]
  -- U^{1/2} is Hermitian (since eigP * diag(real) * eigP* is Hermitian)
  have hdiag_herm : (Matrix.diagonal sqrtd).IsHermitian := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply, star_trivial]
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]
  have hUhalf_herm : Uhalf.IsHermitian := by
    rw [Uhalf_def, Matrix.IsHermitian]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose, hdiag_herm.eq,
      Matrix.mul_assoc]
  -- U^{1/2} is invertible (det is product of √d_i, each > 0)
  have hUhalf_det : IsUnit Uhalf.det := by
    rw [Uhalf_def, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (IsUnit.mul ?_ ?_) ?_
    · exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_mul_star, Matrix.det_one])
    · exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => hsqrtd_ne i)
    · exact IsUnit.of_mul_eq_one _ (by rw [← Matrix.det_mul, hP_star_mul, Matrix.det_one])
  -- U⁻¹ = Uhalf⁻¹ * Uhalf⁻¹
  have hUhalf_inv_sq : Uhalf⁻¹ * Uhalf⁻¹ = U⁻¹ := by
    -- (Uhalf * Uhalf)⁻¹ = Uhalf⁻¹ * Uhalf⁻¹ and Uhalf * Uhalf = U
    rw [← hUhalf_sq]
    symm
    exact Matrix.mul_inv_rev Uhalf Uhalf
  -- === Step 2: Define K = U^{1/2} * B * U^{1/2}, show PSD ===
  set K := Uhalf * B * Uhalf with hK_def
  -- K is PSD (conjugation of PSD B by Hermitian Uhalf)
  have hK_psd : K.PosSemidef := by
    rw [hK_def, show Uhalf * B * Uhalf = Uhalfᴴ * B * Uhalf from by
      rw [hUhalf_herm.eq]]
    exact hB.conjTranspose_mul_mul_same Uhalf
  -- === Step 3: tr(K) = tr(B * U) ===
  have htrK : K.trace = (B * U).trace := by
    -- tr(K) = tr(Uhalf * B * Uhalf) = tr(B * Uhalf * Uhalf) = tr(B * U)
    change (Uhalf * B * Uhalf).trace = (B * U).trace
    rw [show Uhalf * B * Uhalf = Uhalf * (B * Uhalf) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm Uhalf (B * Uhalf)]
    rw [Matrix.mul_assoc, hUhalf_sq]
  have htrK_lt : K.trace < 1 := htrK ▸ htrBU_lt
  -- === Step 4: Conjugation identity (U⁻¹ - B)⁻¹ = Uhalf * (I - K)⁻¹ * Uhalf ===
  -- First: U⁻¹ - B = Uhalf⁻¹ * (I - K) * Uhalf⁻¹
  have hUinv_sub_B : U⁻¹ - B = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ := by
    have hUU : Uhalf⁻¹ * Uhalf = 1 := Matrix.nonsing_inv_mul Uhalf hUhalf_det
    have hUU' : Uhalf * Uhalf⁻¹ = 1 := Matrix.mul_nonsing_inv Uhalf hUhalf_det
    -- RHS = Uhalf⁻¹ * (I - K) * Uhalf⁻¹
    --      = Uhalf⁻¹ * Uhalf⁻¹ - Uhalf⁻¹ * K * Uhalf⁻¹
    --      = U⁻¹ - Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹
    --      = U⁻¹ - (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹)
    --      = U⁻¹ - 1 * B * 1 = U⁻¹ - B
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    -- Goal: U⁻¹ - B = Uhalf⁻¹ * Uhalf⁻¹ - Uhalf⁻¹ * K * Uhalf⁻¹
    rw [hUhalf_inv_sq]
    congr 1
    -- Goal: B = Uhalf⁻¹ * K * Uhalf⁻¹
    rw [hK_def]
    symm
    calc Uhalf⁻¹ * (Uhalf * B * Uhalf) * Uhalf⁻¹
        = (Uhalf⁻¹ * Uhalf) * B * (Uhalf * Uhalf⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = 1 * B * 1 := by rw [hUU, hUU']
      _ = B := by rw [one_mul, mul_one]
  -- Inverse: (U⁻¹ - B)⁻¹ = Uhalf * (I-K)⁻¹ * Uhalf
  have hUU_cancel : Uhalf⁻¹ * Uhalf = 1 := Matrix.nonsing_inv_mul Uhalf hUhalf_det
  have hUU'_cancel : Uhalf * Uhalf⁻¹ = 1 := Matrix.mul_nonsing_inv Uhalf hUhalf_det
  have hconj_inv : (U⁻¹ - B)⁻¹ = Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
    rw [hUinv_sub_B]
    -- (Uhalf⁻¹(I-K)Uhalf⁻¹)⁻¹ = Uhalf(I-K)⁻¹Uhalf
    -- First, show (I-K) is invertible
    have hIK_pd : ((1 : Matrix V V ℝ) - K).PosDef := by
      -- Use the spectral decomposition of K
      set hK_herm := hK_psd.isHermitian
      set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ)
      set eig := hK_herm.eigenvalues
      have hQ_star_mul : star eigQ * eigQ = 1 :=
        Unitary.coe_star_mul_self hK_herm.eigenvectorUnitary
      have hQ_mul_star : eigQ * star eigQ = 1 :=
        Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
      have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := by
        have h := hK_herm.spectral_theorem
        simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
          RCLike.ofReal_real_eq_id, id] at h; exact h
      have h_eig_lt_1 : ∀ i, eig i < 1 := fun i =>
        lt_of_le_of_lt (eigenvalue_le_trace_of_posSemidef K hK_psd i) htrK_lt
      have h_1_sub_pos : ∀ i, 0 < 1 - eig i := fun i => sub_pos.mpr (h_eig_lt_1 i)
      rw [hK_eq]
      have h_one_eq : (1 : Matrix V V ℝ) = eigQ * star eigQ := hQ_mul_star.symm
      rw [h_one_eq]
      have h_sub_eq : eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
          eigQ * Matrix.diagonal (fun i => 1 - eig i) * star eigQ := by
        -- eigQ * star eigQ - eigQ * diag(eig) * star eigQ
        -- = (eigQ - eigQ * diag(eig)) * star eigQ        [← sub_mul]
        -- = (eigQ * 1 - eigQ * diag(eig)) * star eigQ    [mul_one]
        -- = eigQ * (1 - diag(eig)) * star eigQ            [← mul_sub]
        -- = eigQ * diag(1 - eig) * star eigQ
        conv_lhs =>
          rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one]]
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]
        congr 1; congr 1
        ext i j
        simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
        split_ifs <;> simp
      rw [h_sub_eq]
      -- eigQ * diag(1 - eig_i) * star eigQ is PD iff diag(1 - eig_i) is PD
      -- Use Matrix.IsUnit.posDef_star_right_conjugate_iff
      have hQ_unit : IsUnit (eigQ : Matrix V V ℝ) := by
        rw [Matrix.isUnit_iff_isUnit_det]
        exact IsUnit.of_mul_eq_one _
          (by rw [← Matrix.det_mul, hQ_mul_star, Matrix.det_one])
      rw [hQ_unit.posDef_star_right_conjugate_iff]
      exact Matrix.PosDef.diagonal h_1_sub_pos
    -- Now apply the matrix inverse property
    have h_inv_prod : (Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹)⁻¹ =
        Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
      -- Show by right inverse: (Uhalf⁻¹*(I-K)*Uhalf⁻¹) * (Uhalf*(I-K)⁻¹*Uhalf) = 1
      have hIK_det : IsUnit ((1 : Matrix V V ℝ) - K).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp hIK_pd.isUnit
      have hIK_cancel : ((1 : Matrix V V ℝ) - K) *
          ((1 : Matrix V V ℝ) - K)⁻¹ = 1 :=
        Matrix.mul_nonsing_inv _ hIK_det
      have h_prod : (Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹) *
          (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) = 1 := by
        calc Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * Uhalf⁻¹ *
              (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf)
            = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) *
                (Uhalf⁻¹ * Uhalf) * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
              simp only [Matrix.mul_assoc]
          _ = Uhalf⁻¹ * ((1 : Matrix V V ℝ) - K) * 1 *
                ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf := by
              rw [hUU_cancel]
          _ = Uhalf⁻¹ * (((1 : Matrix V V ℝ) - K) *
                ((1 : Matrix V V ℝ) - K)⁻¹) * Uhalf := by
              simp only [Matrix.mul_one, Matrix.mul_assoc]
          _ = Uhalf⁻¹ * 1 * Uhalf := by rw [hIK_cancel]
          _ = 1 := by rw [Matrix.mul_one, hUU_cancel]
      exact Matrix.inv_eq_right_inv h_prod
    exact h_inv_prod
  -- === Step 5: Trace computation and inequality proof ===
  -- tr((U⁻¹ - B)⁻¹) = tr(Uhalf * (I-K)⁻¹ * Uhalf) = tr((I-K)⁻¹ * Uhalf * Uhalf)
  --                    = tr((I-K)⁻¹ * U)
  rw [hconj_inv]
  -- Eigenvalue analysis: tr(Uhalf * (I-K)⁻¹ * Uhalf) ≤ tr(U) + tr(BUU)/(1-tr(BU))
  -- Diagonalize K, express traces in eigenbasis, then use pointwise 1/(1-λ_i) ≤ 1/(1-tr(K)).
  -- Step 5a: Rewrite LHS using trace cyclicity
  -- tr(Uhalf * (I-K)⁻¹ * Uhalf) = tr((I-K)⁻¹ * Uhalf * Uhalf) = tr((I-K)⁻¹ * U)
  have htr_rewrite : (Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf).trace =
      (((1 : Matrix V V ℝ) - K)⁻¹ * U).trace := by
    rw [show Uhalf * ((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf =
        Uhalf * (((1 : Matrix V V ℝ) - K)⁻¹ * Uhalf) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc, hUhalf_sq]
  rw [htr_rewrite]
  -- Step 5b: Spectral decomposition of K (reuse setup from neumann_loewner)
  set hK_herm := hK_psd.isHermitian with hK_herm_def
  set eigQ := (hK_herm.eigenvectorUnitary : Matrix V V ℝ) with hQ_def
  set eig := hK_herm.eigenvalues with heig_def
  have hQ_star_mul : star eigQ * eigQ = 1 :=
    Unitary.coe_star_mul_self hK_herm.eigenvectorUnitary
  have hQ_mul_star : eigQ * star eigQ = 1 :=
    Unitary.coe_mul_star_self hK_herm.eigenvectorUnitary
  have hK_eq : K = eigQ * Matrix.diagonal eig * star eigQ := by
    have h := hK_herm.spectral_theorem
    simp only [Unitary.conjStarAlgAut_apply, Function.comp_def,
      RCLike.ofReal_real_eq_id, id] at h; exact h
  -- Eigenvalue bounds
  have h_eig_nn := hK_psd.eigenvalues_nonneg
  have h_eig_lt_1 : ∀ i, eig i < 1 := fun i =>
    lt_of_le_of_lt (eigenvalue_le_trace_of_posSemidef K hK_psd i) htrK_lt
  have h_1_sub_pos : ∀ i, 0 < 1 - eig i := fun i => sub_pos.mpr (h_eig_lt_1 i)
  have h1t_pos : 0 < 1 - K.trace := sub_pos.mpr htrK_lt
  -- Step 5c: Compute (I-K)⁻¹ in eigenbasis
  set invD := Matrix.diagonal (fun i => (1 - eig i)⁻¹) with invD_def
  set D := Matrix.diagonal (fun i => 1 - eig i) with D_def
  have hD_invD : D * invD = 1 := by
    rw [D_def, invD_def, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; exact mul_inv_cancel₀ (ne_of_gt (h_1_sub_pos i))
  have hIK_eq : (1 : Matrix V V ℝ) - K =
      eigQ * D * star eigQ := by
    rw [hK_eq]
    conv_lhs => rw [show (1 : Matrix V V ℝ) = eigQ * star eigQ from hQ_mul_star.symm]
    rw [show eigQ * star eigQ - eigQ * Matrix.diagonal eig * star eigQ =
      eigQ * ((1 : Matrix V V ℝ) - Matrix.diagonal eig) * star eigQ from by
        conv_lhs =>
          rw [show eigQ * star eigQ = eigQ * 1 * star eigQ from by rw [Matrix.mul_one]]
        rw [← Matrix.sub_mul, ← Matrix.mul_sub]]
    congr 1; congr 1
    rw [D_def]
    ext i j; simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have h_diag_det : IsUnit D.det := by
    rw [D_def, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ne_of_gt (h_1_sub_pos i))
  have hIK_inv : ((1 : Matrix V V ℝ) - K)⁻¹ = eigQ * invD * star eigQ := by
    rw [hIK_eq]
    have h_prod : (eigQ * D * star eigQ) * (eigQ * invD * star eigQ) = 1 := by
      calc eigQ * D * star eigQ * (eigQ * invD * star eigQ)
          = eigQ * D * (star eigQ * eigQ) * invD * star eigQ := by
            simp only [Matrix.mul_assoc]
        _ = eigQ * (D * invD) * star eigQ := by
            rw [hQ_star_mul, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = eigQ * star eigQ := by rw [hD_invD, Matrix.mul_one]
        _ = 1 := hQ_mul_star
    exact Matrix.inv_eq_right_inv h_prod
  -- Step 5d: Define U' = eigQ* * U * eigQ (U in K's eigenbasis)
  set U' := star eigQ * U * eigQ with hU'_def
  -- U' is PSD (conjugation of PD U by invertible eigQ)
  have hU'_psd : U'.PosSemidef := by
    rw [hU'_def, show star eigQ = eigQᴴ from rfl]
    exact hU.posSemidef.conjTranspose_mul_mul_same eigQ
  -- Step 5e: tr((I-K)⁻¹ * U) = ∑ U'_{ii} / (1 - eig_i)
  -- First, expand: (I-K)⁻¹ * U = eigQ * invD * star eigQ * U
  -- tr(...) = tr(invD * star eigQ * U * eigQ) = tr(invD * U')
  -- = ∑ (invD * U')_{ii} = ∑ (1/(1-eig_i)) * U'_{ii}
  -- Helper: trace of diagonal * M = ∑ d_i * M_{ii}
  have trace_diag_mul : ∀ (f : V → ℝ) (M : Matrix V V ℝ),
      (Matrix.diagonal f * M).trace = ∑ i, f i * M i i := by
    intro f M
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    apply Finset.sum_congr rfl; intro i _
    -- Goal: ∑ j, (if i = j then f i else 0) * M j i = f i * M i i
    -- The sum has a single nonzero term when j = i
    have : ∀ j ∈ Finset.univ, j ≠ i → (if i = j then f i else 0) * M j i = 0 := by
      intro j _ hj; simp [Ne.symm hj]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _) this]
    simp
  have htr_expand : (((1 : Matrix V V ℝ) - K)⁻¹ * U).trace =
      ∑ i, U' i i / (1 - eig i) := by
    rw [hIK_inv]
    rw [show eigQ * invD * star eigQ * U =
        eigQ * (invD * (star eigQ * U)) from by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show invD * (star eigQ * U) * eigQ =
        invD * (star eigQ * U * eigQ) from by simp only [Matrix.mul_assoc]]
    rw [← hU'_def, invD_def, trace_diag_mul]
    -- Goal: ∑ i, (1 - eig i)⁻¹ * U' i i = ∑ i, U' i i / (1 - eig i)
    apply Finset.sum_congr rfl; intro i _
    rw [div_eq_inv_mul]
  -- Step 5f: tr(U) = ∑ U'_{ii}
  have htr_U : U.trace = ∑ i, U' i i := by
    -- tr(U) = tr(eigQ * star eigQ * U) = tr(star eigQ * U * eigQ) = tr(U')
    rw [show U = eigQ * star eigQ * U from by rw [hQ_mul_star, one_mul]]
    rw [show eigQ * star eigQ * U = eigQ * (star eigQ * U) from Matrix.mul_assoc _ _ _]
    rw [Matrix.trace_mul_comm]
    rw [show star eigQ * U * eigQ = star eigQ * U * eigQ from rfl]
    rfl
  -- Step 5g: tr(K * U) = ∑ eig_i * U'_{ii}
  have htr_KU : (K * U).trace = ∑ i, eig i * U' i i := by
    rw [hK_eq]
    -- K * U = eigQ * diag(eig) * star eigQ * U
    -- tr(...) = tr(diag(eig) * star eigQ * U * eigQ) = tr(diag(eig) * U')
    rw [show eigQ * Matrix.diagonal eig * star eigQ * U =
        eigQ * (Matrix.diagonal eig * (star eigQ * U)) from by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show Matrix.diagonal eig * (star eigQ * U) * eigQ =
        Matrix.diagonal eig * (star eigQ * U * eigQ) from by simp only [Matrix.mul_assoc]]
    rw [← hU'_def, trace_diag_mul]
  -- Step 5h: tr(K * U) = tr(B * U * U)
  have htr_KU_eq_BUU : (K * U).trace = (B * U * U).trace := by
    -- K * U = Uhalf * B * Uhalf * U
    -- tr(K * U) = tr(Uhalf * (B * Uhalf * U))  [assoc]
    -- = tr(B * Uhalf * U * Uhalf)              [trace cyclicity]
    -- = tr(B * (Uhalf * U) * Uhalf)            [assoc]
    -- = tr(B * (Uhalf * (Uhalf * Uhalf)) * Uhalf) [U = Uhalf²]
    -- = tr(B * (Uhalf * Uhalf) * (Uhalf * Uhalf))  [assoc]
    -- = tr(B * U * U)
    rw [hK_def]
    rw [show Uhalf * B * Uhalf * U = Uhalf * (B * Uhalf * U) from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    -- Goal: (B * Uhalf * U * Uhalf).trace = (B * U * U).trace
    rw [← hUhalf_sq]
    simp only [Matrix.mul_assoc]
  -- Step 5i: The key inequality via pointwise bound
  -- Goal: ∑ U'_{ii}/(1-eig_i) ≤ (∑ U'_{ii}) + (∑ eig_i * U'_{ii}) / (1 - tr(K))
  rw [htr_expand, htr_U, ← htr_KU_eq_BUU, htr_KU, ← htrK]
  -- Now goal: ∑ U'_{ii}/(1-eig_i) ≤ (∑ U'_{ii}) + (∑ eig_i*U'_{ii})/(1-K.trace)
  -- Decompose: U'_{ii}/(1-eig_i) = U'_{ii} + eig_i*U'_{ii}/(1-eig_i)
  -- So ∑ = ∑ U'_{ii} + ∑ eig_i*U'_{ii}/(1-eig_i)
  -- Bound: each eig_i*U'_{ii}/(1-eig_i) ≤ eig_i*U'_{ii}/(1-tr(K))
  -- Sum: ∑ eig_i*U'_{ii}/(1-eig_i) ≤ ∑ eig_i*U'_{ii}/(1-tr(K)) = (∑...)/...
  have hU'_diag_nn : ∀ i, 0 ≤ U' i i := fun i => hU'_psd.diag_nonneg
  -- Split each term: U'_{ii}/(1-eig_i) = U'_{ii} + eig_i*U'_{ii}/(1-eig_i)
  have h_split_sum : ∑ i : V, U' i i / (1 - eig i) =
      ∑ i : V, U' i i + ∑ i : V, eig i * U' i i / (1 - eig i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    have h1 : (1 - eig i) ≠ 0 := ne_of_gt (h_1_sub_pos i)
    field_simp; ring
  rw [h_split_sum]
  -- Goal: sum U'ii + sum eig_i*U'ii/(1-eig_i)
  --     <= sum U'ii + (sum eig_i*U'ii)/(1-tr(K))
  -- Suffices: ∑ eig_i*U'_{ii}/(1-eig_i) ≤ (∑ eig_i*U'_{ii})/(1-K.trace)
  gcongr
  -- Goal: ∑ eig_i * U'_{ii} / (1 - eig_i) ≤ (∑ eig_i * U'_{ii}) / (1 - K.trace)
  -- Each term: eig_i*U'_{ii}/(1-eig_i) ≤ eig_i*U'_{ii}/(1-K.trace)
  -- since 0 < 1-K.trace ≤ 1-eig_i (because eig_i ≤ K.trace)
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  -- Goal: eig_i * U'_{ii} / (1 - eig_i) ≤ eig_i * U'_{ii} / (1 - K.trace)
  -- a/(1-eig_i) ≤ a/(1-K.trace) since 0 ≤ a, 0 < 1-K.trace ≤ 1-eig_i
  apply div_le_div_of_nonneg_left (mul_nonneg (h_eig_nn i) (hU'_diag_nn i)) h1t_pos
  -- 1 - K.trace ≤ 1 - eig_i  ↔  eig_i ≤ K.trace
  linarith [eigenvalue_le_trace_of_posSemidef K hK_psd i]
end Problem6

end
