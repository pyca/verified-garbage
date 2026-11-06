module

public import VerifiedGarbage.Proof.MillerRabin.AArch64.CallerSave
import VerifiedGarbage.Proof.Framework.Omega

/-! # The caller's saved words and untouched Montgomery-one value -/

@[expose] public section

namespace VG.Proof.MillerRabin.AArch64.Caller

open VG VG.AArch64 VG.Proof.Bignum VG.Impl.Bignum VG.Impl.Bignum.Public

theorem saved_x19 (s : State) (B : Addr) (w : Nat) (hp : pad w + 16 ≤ 2 ^ 64) :
    word (savedMem s B w) B (pad w) = s.gpr .x19 := by
  unfold savedMem
  rw [(writeW_outside _ B (s.gpr .x30) (d := pad w + 8) (by omega_arith)).word
    (Or.inl (by omega_arith)) (by omega_arith), word_writeW_self]

theorem saved_x30 (s : State) (B : Addr) (w : Nat) :
    word (savedMem s B w) B (pad w + 8) = s.gpr .x30 := by
  unfold savedMem
  exact word_writeW_self _ _ _ _

end VG.Proof.MillerRabin.AArch64.Caller
