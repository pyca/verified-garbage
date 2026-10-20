module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Impl.Rsa.AArch64.WindowSelectVector

/-! Start each SIMD block at the same public offset in every table entry. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)
open VG.Impl.Rsa.AArch64.WindowSelectVector (accs)

def blockHead : List Instr :=
  [ldh .x16 (sArr Crt.aT), .sub .x .x16 .x17 .x16,
   ldh .x3 Crt.sTab, .add .x .x16 .x16 .x3,
   .vop (.movi0 .v23), movi .x14 32]

theorem exec_zeroVector (s : State) (r : VReg) :
    exec (.vop (.movi0 r)) s = some (s.setV r 0) := rfl

theorem blockHead_ok {s : State} {P : Addr} {w b : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hp : s.gpr .x17 = off P (slot w Crt.aT + 64 * b)) :
    WP isa (.block blockHead) s fun t =>
      (t.gpr .x16 = off P (slot w 8 + 64 * b) ∧ t.gpr .x14 = BitVec.ofNat 64 32 ∧
       t.v = (s.setV .v23 0).v ∧ t.mem = s.mem) ∧ Keep [.x16,.x3,.x14] s t := by
  have hp' : off P (slot w Crt.aT + 64 * b) - off P (slot w Crt.aT) =
      BitVec.ofNat 64 (64 * b) := by
    rw [off, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact Offset.add_sub_cancel_left _ _
  refine WP.keep _ ?_ rfl rfl rfl
  brun [blockHead, hc.good.x0, hdr_enc (sArr_lt (show Crt.aT < 8 by decide)),
    hdr_enc (show Crt.sTab < 32 by decide), hc.ld (i := sArr Crt.aT) (by decide),
    hc.ld (i := Crt.sTab) (by decide), hc.good.hdr.harr Crt.aT (by decide), ht, hp, hp',
    exec_zeroVector, RegUpd.v_write, RegUpd.gpr_setV, RegUpd.mem_setV]
  refine ⟨BitVec.add_comm _ _ |>.trans (off_add P (slot w 8) (64 * b)), ?_⟩
  simp only [State.setV, RegUpd.v_write]

end VG.Proof.Bignum.AArch64.WindowVector
