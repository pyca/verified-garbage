module

public import VerifiedGarbage.Proof.MillerRabin.Word32 -- shake: keep: re-export the shared arithmetic under the existing ARM names.

/-! # The ARMv7 round uses the shared native-word Miller–Rabin arithmetic -/

@[expose] public section
namespace VG.Proof.MillerRabin.Arm

export VG.Proof.MillerRabin.Word32 (
  rinv mm R_rinv mm_eq mm_val mm_lt
  tp tp_val tp_lt msq msqs mwin
  mrun msq_rel msqs4_rel mwin_rel mrun_rel mrA_le
  final_eq shl_shr28 shl4_succ32 digit_word mask_lt mask_eq
  mask_zero flag_bits foldR foldR_eq
)

end VG.Proof.MillerRabin.Arm
