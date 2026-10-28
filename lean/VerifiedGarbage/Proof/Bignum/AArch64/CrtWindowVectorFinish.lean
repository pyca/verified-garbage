module
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable

import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

/-! Restore the scalar selector's final public header values. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowVector
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Impl.Rsa.AArch64.Crt
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Proof.Bignum.AArch64.WindowFive (TableCtx)

def finish : List Instr := [ldh .x3 Crt.sTab, .lsl .x .x4 .x6 5, .add .x .x3 .x3 .x4,
  sth .x3 Crt.sEnt, movi .x3 32, sth .x3 Crt.sJ]

theorem shl5_stride {w : Nat} (hw : w < 2 ^ 30) :
    BitVec.ofNat 64 (8 * (w + 2)) <<< 5 = BitVec.ofNat 64 (32 * (8 * (w + 2))) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (show 8 * (w + 2) < 2 ^ 64 by omega)]
  congr 1
  omega

theorem finish_ok {s : State} {P : Addr} {w : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hw : w < 2 ^ 30)
    (ht : word s.mem P (8 * Crt.sTab) = off P (slot w 8))
    (hs : s.gpr .x6 = BitVec.ofNat 64 (8 * (w + 2))) :
    WP isa (.block finish) s fun t =>
      t.mem = (s.mem.writeW (off P (8 * Crt.sEnt))
        (off P (slot w 8 + 32 * (8 * (w + 2))))).writeW
        (off P (8 * Crt.sJ)) (BitVec.ofNat 64 32) ∧ Keep [.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [finish, hc.good.x0, hdr_enc (show Crt.sTab < 32 by decide),
    hdr_enc (show Crt.sEnt < 32 by decide), hdr_enc (show Crt.sJ < 32 by decide),
    hc.ld (i := Crt.sTab) (by decide), hc.st (i := Crt.sEnt) (by decide),
    hc.st (i := Crt.sJ) (by decide), ht, hs, shl5_stride hw]
  rfl

end VG.Proof.Bignum.AArch64.WindowVector
