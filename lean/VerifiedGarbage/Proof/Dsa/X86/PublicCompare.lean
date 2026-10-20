module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Comparisons used only for dispatch on public lengths -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem publicCompare_ok {s : State} {base : Addr} {size value wanted : Nat} (f : Field)
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hv : (pointerValue base s (.input f)).toNat = value)
    (hb : wanted < 2 ^ 32) :
    WP isa (.block [.mov .eax (.mem (sc (Layout.field f))), .alu .cmp .eax (.imm (BitVec.ofNat 32 wanted))]) s fun t =>
      t.zf = some (decide (value = wanted)) ∧ Keeps [.eax] s t ∧ t.mem = s.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have bound : Layout.field f + 4 ≤ size := by omega
  refine wp_movS (readSrc_sc hs bound) fun u su _ => ?_
  refine wp_cmpS rfl fun t ut zt => WP.block_nil ⟨?_, su.keeps.trans (ut.keeps [] |>.mono (by simp)), ut.mem.trans su.mem⟩
  rw [zt, su.gpr]
  change some (pointerValue base s (.input f) - BitVec.ofNat 32 wanted == 0) = _
  have W : pointerValue base s (.input f) = BitVec.ofNat 32 value := by
    rw [← hv]
    simpa only [BitVec.setWidth_eq] using (BitVec.ofNat_toNat 32 (pointerValue base s (.input f))).symm
  rw [W, sub_beq (by rw [← hv]; exact (pointerValue base s (.input f)).isLt) hb]

end VG.Proof.Dsa.X86
