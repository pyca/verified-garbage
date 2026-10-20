module

public import VerifiedGarbage.Proof.Dsa.AArch64.CheckOperands
import VerifiedGarbage.Proof.Dsa.AArch64.BufferFrame

/-! # State and operand preservation between complete DSA schedules -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

theorem Ready.readLocal {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (d : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes) :
    OperandBytes s L.base activeBytes ⟨.local d, side.lengthField⟩
      (Spec.Rsa.bytesAt s.mem (off L.base d) (side.length L)) := by
  apply output_operand (h.length side) rfl _ (h.local_out hd hend)
  intro i hi
  rcases h.local_write hend i hi with ⟨region, hr, hc⟩
  exact ⟨region, List.mem_append_right _ hr, hc⟩

theorem Ready.preserveExternal {L : ExecutionLayout} {s t : State} (hs : Ready L s) (ht : Ready L t)
    (hf : Outside L.base 128 (usedBytes - 128) s.mem t.mem) (hk : Keep coreRegs s t)
    {a : Operand} {bytes : List Byte} (ha : a.length ≠ .mask) (hp : stablePointer a.pointer)
    (hb : OperandBytes s L.base usedBytes a bytes) : OperandBytes t L.base usedBytes a bytes := by
  refine ⟨(ht.fields a.length ha).trans ((hs.fields a.length ha).symm.trans hb.length), ?_⟩
  rw [hs.pointer_eq ht a.pointer hp]
  exact hb.source.congrK (InScr.of_outside hf (by decide)) hk

theorem Ready.encodedLocal {L : ExecutionLayout} {s : State} (h : Ready L s) (side : ModulusSide)
    (d value : Nat) (hd : activeBytes ≤ d) (hend : d + side.length L ≤ usedBytes)
    (hb : Spec.Rsa.bytesAt s.mem (off L.base d) (side.length L) = Spec.Dsa.encodeBE (side.length L) value) :
    OperandBytes s L.base activeBytes ⟨.local d, side.lengthField⟩ (Spec.Dsa.encodeBE (side.length L) value) := by
  have hs := h.readLocal side d hd hend
  rw [hb] at hs
  exact hs

end VG.Proof.Dsa.AArch64
