module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillEntry
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.RefillOutcome
public import VerifiedGarbage.Proof.Dsa.Generation.RefillSearch
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.Memory
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.AttemptStatus
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.TapeState
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.ContextSlice
import VerifiedGarbage.Proof.Dsa.Generation.Memory
import VerifiedGarbage.Proof.RsaOaep.X86_64.Mgf
import VerifiedGarbage.Proof.Bignum.Octets

/-! # The refillable-tape search's controller on x86-64

The controller runs one seed per iteration while seeds are rejected. Its
invariant (`LoopInv`): the whole search's result is the search from the
octets `c` it has consumed on, those consumed before it
(`RefillSearch.lean`), and the controller's words hold the pointers to
`used` and `state` and the seeds it may still reject. -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64.Generation.Refill

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.RsaOaep.X86_64 VG.Impl.RsaOaep.X86_64
open VG.Impl.Mgf1.X86_64 (sp)

/-! ## Blocks -/

/-- The start of an iteration: the seed's start into `ctl 3`, and the seeds left tested. -/
theorem iterStart_ok {s : State} {F S : Addr} {V : Nat → Byte} {W : Nat → BitVec 64}
    (L : Lay s F S) (R : Rep s.mem F S V W) (hctl : ctlRegion F ∈ s.wr) (hb : F.toNat + 328 ≤ 2 ^ 64)
    {c n : Nat} (h16 : W 16 = BitVec.ofNat 64 c) (hn : n < 2 ^ 64)
    (h2 : (s.mem.writeW (off F 320) (BitVec.ofNat 64 c)).readW (off F 312) 64 = BitVec.ofNat 64 n) :
    WP isa (.block [.mov .rax (.mem (sp 128)), .store (Impl.Dsa.X86_64.Generation.Refill.ctl 3) .rax,
        .mov .rcx (.mem (Impl.Dsa.X86_64.Generation.Refill.ctl 2)), .alu .test .rcx (.reg .rcx)]) s fun t =>
      t.gpr .rax = BitVec.ofNat 64 c ∧ t.zf = some (decide (n = 0)) ∧
      t.mem = s.mem.writeW (off F 320) (BitVec.ofNat 64 c) ∧ Keep [.rax, .rcx] s t := by
  have cs : Scr s (off F 296) 32 := Scr.of_mem hctl (by
    simp only [off, BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
  have c2 : InRegions (s.rd ++ s.wr) (off F 312) 8 := by simpa [off_off] using cs.ld (d := 16) (by decide)
  have c3 : InRegions s.wr (off F 320) 8 := by simpa [off_off] using cs.st (d := 24) (by decide)
  refine WP.keep [.rax, .rcx] ?_ rfl
  xrun [Impl.Dsa.X86_64.Generation.Refill.ctl, Impl.Dsa.X86_64.Generation.Refill.frameBytes,
    ea_sp, L.rsp, L.ld (d := 128) (by decide), R.slot (d := 128) (k := 16) rfl (by decide) h16, c2, c3, h2,
    ofNat_beq_zero hn]
  sorry

end VG.Proof.Dsa.X86_64.Generation.Refill
