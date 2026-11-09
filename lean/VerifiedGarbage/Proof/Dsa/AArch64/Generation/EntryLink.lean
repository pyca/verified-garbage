module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.EntrySpill
import VerifiedGarbage.Proof.Framework.Offset

/-! Save the incoming link register outside the persistent generation words. -/
@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Impl.RsaOaep.AArch64 VG.Impl.Dsa.Generation.Layout

theorem link_frame (s : State) : Frame [linkRegion s] s.mem (linkState s).mem := by
  have gp := Spill.saveMem_frame (l := Impl.Dsa.AArch64.Generation.abiGprs) (lo := 296) (n := 152)
    (by decide) (by decide) s.mem (Refill.refillBase s) s.gpr
  have vp := Spill.saveMem_frame (l := vectorSlots) (lo := 296) (n := 152)
    (by decide) (by decide)
    (Spill.saveMem s.mem (Refill.refillBase s) s.gpr Impl.Dsa.AArch64.Generation.abiGprs)
    (Refill.refillBase s) (vectorValues s)
  have ff : Frame [linkRegion s] s.mem (savedAbiMem s) := gp.trans vp
  have hc : (linkRegion s).Contains (linkRegion s).base 8 := by
    have hc := Offset.contains_base (off (Refill.refillBase s) 296) (d := 0) (n := 8) (k := 152)
      (by decide) (by decide)
    simpa only [linkRegion, off, BitVec.add_zero] using hc
  exact ff.writeW (r := linkRegion s) (by simp) (s.gpr .x30) hc

end VG.Proof.Dsa.AArch64.Generation
