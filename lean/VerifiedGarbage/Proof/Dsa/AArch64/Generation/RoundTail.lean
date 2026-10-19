module

public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.RoundTail
public import Mathlib.Data.Int.ModEq
public import VerifiedGarbage.Proof.Rsa.AArch64.KeyWs
import VerifiedGarbage.Proof.RsaKeyGen.AArch64.MrTail

/-! Reuse RSA's proven completion policy, including forced-witness accounting. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Rsa.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.RsaKeyGen.AArch64.Candidate
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.Rsa.AArch64 VG.Proof.MlKem.AArch64

theorem roundTail_ok {s : State} {B : Addr} {Z w : Nat} (h : Ws s B Z w)
    {f u : Bool} {i uni ch : Nat} (hF : word s.mem B (8 * kFlag) = mask f) (hI : word s.mem B (8 * kI) = BitVec.ofNat 64 i)
    (hU : word s.mem B (8 * kU) = mask u) (hN : word s.mem B (8 * kUni) = BitVec.ofNat 64 uni)
    (hC : word s.mem B (8 * kChecks) = BitVec.ofNat 64 ch) (hi : i < 2 ^ 62) (huni : uni < 2 ^ 62) (hch : ch < 2 ^ 62) :
    WP isa Impl.Dsa.AArch64.Generation.roundTail s fun t =>
      t.mem = (if f then ((s.mem.writeW (off B (8 * kI)) (BitVec.ofNat 64 (i + 1))).writeW (off B (8 * kUni))
          (BitVec.ofNat 64 (uni + u.toNat))).writeW (off B (8 * kStat))
          (BitVec.ofNat 64 (if i + 1 < 17 ∨ uni + u.toNat < ch then 4 else 1))
        else s.mem.writeW (off B (8 * kStat)) (BitVec.ofNat 64 3)) ∧ Keep mmRegs s t :=
  VG.Proof.RsaKeyGen.AArch64.roundTail_ok h hF hI hU hN hC hi huni hch

end VG.Proof.Dsa.AArch64.Generation
