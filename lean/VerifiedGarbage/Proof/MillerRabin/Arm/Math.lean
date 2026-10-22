module

public import VerifiedGarbage.Proof.MillerRabin.Math

/-! # Shared Miller–Rabin arithmetic, re-exported for existing ARMv7 proofs -/

@[expose] public section
namespace VG.Proof.MillerRabin.Arm

export VG.Proof.MillerRabin.Math (rinv mm R_rinv mm_eq mm_val mm_lt tp tp_val tp_lt msq msqs mwin mrun msq_rel msqs4_rel mwin_rel mrun_rel mrA_le final_eq shl_shr28 shl4_succ32 digit_word mask_lt mask_eq mask_zero flag_bits foldR foldR_eq)

end VG.Proof.MillerRabin.Arm
