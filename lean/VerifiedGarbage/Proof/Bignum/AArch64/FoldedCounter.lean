module

public import VerifiedGarbage.Impl.Rsa.AArch64.Folded
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section
namespace VG.Proof.Bignum.AArch64.FoldedPublic
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64

theorem next_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hn : 1 ≤ n) (hn' : n < 2^31)
    (hc : word s.mem B (8*sI) = BitVec.ofNat 64 n) :
    WP isa (.block Folded.next) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
      t.gpr .x3 = BitVec.ofNat 64 (n-1) ∧ Keep [.x3] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    omega
  refine WP.mono (WP.keep [.x3] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
    t.gpr .x3 = BitVec.ofNat 64 (n-1)) ?_ rfl rfl rfl)
    fun t ⟨⟨hm,hr⟩,hk⟩ => ⟨hm,hr,hk⟩
  unfold Folded.next
  brun [hg.x0, hdr_enc (show sI < 32 by decide), hg.scr.ld bound, hg.scr.st bound, hc,
    ofNat_sub_one' hn (by omega)]

theorem init_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [movi .x3 16, sth .x3 sI]) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (16 : BitVec 64) ∧ Keep [.x3] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    omega
  exact WP.keep [.x3] (by brun [hg.x0, hdr_enc (show sI < 32 by decide), hg.scr.st bound]; rfl) rfl rfl rfl

end VG.Proof.Bignum.AArch64.FoldedPublic
