module

public import VerifiedGarbage.Impl.Rsa.AArch64.WindowLoop
public import VerifiedGarbage.Proof.Bignum.AArch64.CrtWindowTable
import Mathlib.Data.Int.ModEq
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! All outer-loop tests depend only on the public exponent length and index. -/

@[expose] public section
namespace VG.Proof.Bignum.AArch64.WindowFive
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Impl.Rsa.AArch64.WindowFive (haveFive advance loadTailByte remaining)

theorem haveFive_ok {s : State} {P : Addr} {w i L : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i ≤ L) (hL : L < 2 ^ 64)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hlen : word s.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) :
    WP isa (.block haveFive) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x9 = if i + 5 ≤ L then 1 else 0) ∧ Keep [.x3,.x4,.x5,.x9] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [haveFive,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide),hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sExpLen) (by decide),hidx,hlen,VG.Offset.ofNat_sub_ofNat hi,
    decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show L-i < 2 ^ 64 by omega)]
  change (if 18446744073709551616 ≤ L-i + 18446744073709551610 + 1 then (1#64) else 0) = _
  simp only [show (18446744073709551616 ≤ L-i + 18446744073709551610 + 1) ↔ i+5 ≤ L by omega]
  rfl

theorem advance_ok (n : Nat) (hn : n < 4096) {s : State} {P : Addr} {w i : Nat}
    {mi : BitVec 64} {X Xc : Nat} (hc : TableCtx s P w mi X Xc)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i) :
    WP isa (.block (advance n)) s fun t =>
      t.mem = s.mem.writeW (off P (8 * Crt.sI)) (BitVec.ofNat 64 (i+n)) ∧ Keep [.x3] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [advance,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hc.ld (i := Crt.sI) (by decide),hc.st (i := Crt.sI) (by decide),hidx,hn,ofNat_add_ofNat]

theorem remaining_ok {s : State} {P : Addr} {w i L : Nat} {mi : BitVec 64} {X Xc : Nat}
    (hc : TableCtx s P w mi X Xc) (hi : i ≤ L)
    (hidx : word s.mem P (8 * Crt.sI) = BitVec.ofNat 64 i)
    (hlen : word s.mem P (8 * Crt.sExpLen) = BitVec.ofNat 64 L) :
    WP isa (.block remaining) s fun t =>
      (t.mem = s.mem ∧ t.gpr .x3 = BitVec.ofNat 64 (L-i)) ∧ Keep [.x3,.x4] s t := by
  refine WP.keep _ ?_ rfl rfl rfl
  brun [remaining,hc.good.x0,hdr_enc (show Crt.sI < 32 by decide),
    hdr_enc (show Crt.sExpLen < 32 by decide),hc.ld (i := Crt.sI) (by decide),
    hc.ld (i := Crt.sExpLen) (by decide),hidx,hlen,VG.Offset.ofNat_sub_ofNat hi]

end VG.Proof.Bignum.AArch64.WindowFive
