module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Layout
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Push
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! The native saved-register push preserves the entropy tape and every public policy word. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont

theorem SearchLayout.push_word {p : SearchParams} {s : State} (h : SearchLayout p s)
    {j : Nat} (bound : j < 16) :
    (bodyState s).mem.readW (off (State.addr p.control) (8 * j)) 64 =
      s.mem.readW (off (State.addr p.control) (8 * j)) 64 := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.control, 128⟩ (by simp [writeRegions])).sub_left
    (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact frame.readW (r := ⟨State.addr p.control, 128⟩)
    (Offset.contains_base _ (by omega : 8 * j + 8 ≤ 128) (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm) (by decide)

theorem SearchLayout.push_bytes {p : SearchParams} {s : State} (h : SearchLayout p s)
    (args : SearchAbi p s) :
    Spec.Rsa.bytesAt (bodyState s).mem (State.addr p.c.tape) p.c.bytes.length = p.c.bytes := by
  have frame : Frame [FrameStack.belowA s.sp 24] s.mem (bodyState s).mem :=
    FrameStack.pushed_frameA (rs := [.r4, .r9, .r10, .r11, .r12, .lr]) (by change 24 ≤ s.sp.toNat; have := h.stackFits; omega)
  have separate := (h.stackSeparate ⟨State.addr p.c.tape, p.c.bytes.length⟩
    (by simp [readRegions])).sub_left (FrameStack.belowA_sub (by decide : 24 ≤ 232) h.stackFits)
  exact (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by have := p.c.tapeCount; omega)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact separate.symm)).trans args.bytes

end VG.Proof.Ffdh.Arm.ParameterSearch
