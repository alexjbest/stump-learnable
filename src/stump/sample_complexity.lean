/-
Copyright © 2019, Oracle and/or its affiliates. All rights reserved.
-/

import analysis.special_functions.exp_log
import ..lib.util

open real

noncomputable
def complexity (ε: ℝ) (δ: ℝ) : ℝ := (log(δ) / log(1 - ε)) - (1: nat)

lemma complexity_enough:
    ∀ ε: nnreal, ∀ δ: nnreal, ∀ n: ℕ, 
    ε > (0: nnreal) → ε < (1: nnreal) → δ > (0: nnreal) → δ < (1: nnreal) → 
    (n: ℝ) > (complexity ε δ) → ((1 - ε)^(n+1)) ≤ δ :=
begin
    unfold complexity, 
    intros, 
    have h0: ((1: nnreal) - ε) > 0, by change (0 < 1 - ε);rwa[← nnreal.coe_pos, nnreal.coe_sub (le_of_lt (a_1)), sub_pos, nnreal.coe_lt_coe],
    rw log_le_log_nnreal,
    {
        have h2:= log_pow_nnreal (1 - ε) h0 (n+1),
        unfold_coes at *,
        rw ← pow_coe,
        rw h2,
        apply mul_le_of_div_le_of_neg,
        {
            rw ←exp_lt_exp, simp, rw exp_log _, 
            {
                rw nnreal.coe_sub,
                cases ε, 
                exact sub_lt_self 1 a,
                apply le_of_lt, assumption,
            },
            {
                rw nnreal.coe_sub,
                cases ε, 
                exact sub_pos.mpr a_1,
                apply le_of_lt, assumption,
            },      
        },
        {
            apply le_of_lt, 
            clear h2,
            have nat_cast_1: ∀ x: ℕ, (nat.cast x) + (1:ℝ) = nat.cast(x + 1), exact nat.cast_succ,
            rw ← nat_cast_1,
            have minus_nnreal: ∀ x: nnreal, x < 1 → (1 - x).val = 1 - x.val, assume x h, exact nnreal.coe_sub (le_of_lt h),
            rw minus_nnreal, 
            swap, assumption,
            have plus_1:= add_lt_add_right a_4 1, 
            simp at plus_1,
            simp,
            conv {
                to_rhs, rw add_comm, skip,
            },
            have silly: (1: ℝ) = nat.cast 1, 
            {
                unfold nat.cast, simp,
            },
            conv {
                to_rhs, rw silly, skip,
            },
            exact sub_lt_iff_lt_add'.mp a_4,
        },
    },
    {
        refine pow_pos h0 (n + 1),
    },
    {
        assumption,
    },
end
