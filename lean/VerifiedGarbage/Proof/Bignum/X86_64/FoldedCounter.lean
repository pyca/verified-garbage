import VerifiedGarbage.Impl.Rsa.X86_64.Folded
import VerifiedGarbage.Proof.Bignum.X86_64.Exp

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64
open VG.Proof.Bignum.X86_64
open VG.Proof.MlKem.X86_64

theorem next_ok {s : State} {B : Addr} {Z w n : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z)
    (hn : 1 ≤ n) (hn' : n < 2^31)
    (hc : word s.mem B (8*sI) = BitVec.ofNat 64 n) :
    WP isa (.block Folded.next) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
      t.zf = some (decide (n-1 = 0)) ∧ Keep [.rax] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    unfold sI sFn at *; omega
  refine WP.mono (WP.keep [.rax] (Q := fun t =>
    t.mem = s.mem.writeW (off B (8*sI)) (BitVec.ofNat 64 (n-1)) ∧
    t.zf = some (decide (n-1 = 0))) ?_ rfl) fun t ⟨⟨hm,hz⟩,hk⟩ => ⟨hm,hz,hk⟩
  unfold Folded.next
  xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld bound, hg.scr.st bound,
    hc, ofNat64_pred hn (by omega), ofNat64_beq_zero (show n-1 < 2^64 by omega)]

theorem init_ok {s : State} {B : Addr} {Z w : Nat} {mi : BitVec 64}
    (hg : Good s B Z w mi) (hZ : slot w 8 ≤ Z) :
    WP isa (.block [.mov32 .rax (.imm 16), .store (hdr sI) .rax]) s fun t =>
      t.mem = s.mem.writeW (off B (8*sI)) (16 : BitVec 64) ∧ Keep [.rax] s t := by
  have bound : 8*sI+8 ≤ Z := by
    have := hdr_lt_slot w 8 (show sI < 32 by decide)
    unfold sI sFn at *; omega
  exact WP.keep [.rax] (by xrun [State.ea,hdr,hg.rdi,hdrOff,hg.scr.st bound]; rfl) rfl

end VG.Proof.Bignum.X86_64.FoldedPublic
