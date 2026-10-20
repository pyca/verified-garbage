module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowVectorWord

import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Resolve the workspace addresses and public block count for SIMD selection. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

theorem exec_dup2 (s : State) (d : VReg) (n : Reg) :
    exec (.vop (.dup .d2 d n)) s = some (s.setV d (dup2 (s.gpr n))) := rfl

def setup : List Instr :=
  [ldh .x12 sW, .addImm .x .x6 .x12 2, .lsl .x .x6 .x6 3,
   .lsr .x .x13 .x12 3, ldh .x5 Crt.sNib, .vop (.dup .d2 .v22 .x5),
   movi .x2 1, .vop (.dup .d2 .v24 .x2), ldh .x17 (sArr Crt.aT)]

theorem setup_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc v : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : w < 2 ^ 30)
    (hv : word s.mem P (8 * Crt.sNib) = BitVec.ofNat 64 v) :
    WP isa (.block setup) s fun t =>
      (t.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2)) ∧
       t.gpr .x13 = BitVec.ofNat 64 (w / 8) ∧
       t.gpr .x17 = off P (slot w Crt.aT) ∧
       t.v .v22 = dup2 (BitVec.ofNat 64 v) ∧ t.v .v24 = dup2 1 ∧ t.mem = s.mem) ∧
      Keep [.x12,.x6,.x13,.x5,.x2,.x17] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [setup, hc.good.x0, hdr_enc (show sW < 32 by decide),
    hdr_enc (show Crt.sNib < 32 by decide), hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hc.ld (i := sW) (by decide), hc.ld (i := Crt.sNib) (by decide),
    hc.ld (i := sArr Crt.aT) (by decide), hc.good.hdr.hw, hv,
    hc.good.hdr.harr Crt.aT (by decide), ofNat_add_ofNat,
    shl3_ofNat (show 8 * (w + 2) < 2 ^ 64 by omega),
    exec_dup2, dup2, RegUpd.v_setV_self, RegUpd.v_setV_of_ne,
    RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV]

  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show w < 2 ^ 64 by omega), Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show w / 8 < 2 ^ 64 by omega)]

end VG.Proof.Bignum.AArch64.WindowVector
