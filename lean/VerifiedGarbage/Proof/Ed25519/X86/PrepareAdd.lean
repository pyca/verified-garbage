module

public import VerifiedGarbage.Impl.Ed25519.X86.PointAccumulate
public import VerifiedGarbage.Proof.Ed25519.X86.PointTable
import VerifiedGarbage.Proof.Ed25519.X86.PointPowers
import VerifiedGarbage.Proof.Ed25519.X86.Points
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! Load a table point while preserving the accumulator for selection. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86
open VG VG.X86 VG.Impl.Ed25519.X86

theorem FieldKeep.of_mem {x : BitVec 32} {s t : State} (h : Keep s t) (hm : t.mem = s.mem) :
    FieldKeep x s t := ⟨h, by rw [hm]; exact Frame.refl _ _⟩

theorem FieldKeep.of_copy {x : BitVec 32} {s t : State} (h : CopyKeep x 64 128 s t)
    (hc : Ctx x s) : FieldKeep x s t :=
  ⟨⟨h.gpr _ (by decide), h.gpr _ (by decide), h.gpr _ (by decide), h.rd, h.wr⟩,
    frameWiden h.frame hc.fit (by decide) (by decide) (by decide)⟩

end VG.Proof.Ed25519.X86
