module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The cancellation prefix saves its coefficient in the word being eliminated. -/
def cancelHead (i : Nat) : List Instr :=
  [.mul .x .x27 .x19 .x15, st .x27 .x8 (8 * i), movi .x1 0]

def cancelMid : List Instr := [.adc .x .x1 .x1 .x7]

theorem cancelHead_ok {s : State} {B : Addr} {Z eQ i : Nat}
    (hs : Scr s B Z) (h8 : s.gpr .x8 = off B eQ)
    (hQ : eQ + 8 * i + 8 ≤ Z) (hi : i < 8) :
    WP isa (.block (cancelHead i)) s fun t =>
      (t.gpr .x1 = 0 ∧ t.gpr .x27 = s.gpr .x19 * s.gpr .x15 ∧
       t.mem = s.mem.writeW (off B (eQ + 8 * i)) (s.gpr .x19 * s.gpr .x15)) ∧
      Keep [.x1, .x27] s t := by
  have enc : (8 * i) % 8 = 0 ∧ 8 * i < 32768 := ⟨by omega, by omega⟩
  refine WP.keep [.x1, .x27] ?_ rfl rfl rfl
  brun [cancelHead, h8, enc, hs.st hQ]

theorem cancelMid_ok {s : State} (h1 : s.gpr .x1 = 0) (h7 : s.gpr .x7 = 0) :
    WP isa (.block cancelMid) s fun t =>
      (t.gpr .x1 = BitVec.ofNat 64 s.c.toNat ∧ t.mem = s.mem ∧ t.c = s.c) ∧
      Keep [.x1] s t := by
  refine WP.keep [.x1] ?_ rfl rfl rfl
  brun [cancelMid, h1, h7]
  simp only [zero_add64]

end VG.Proof.Bignum.AArch64.BlockedRedc
