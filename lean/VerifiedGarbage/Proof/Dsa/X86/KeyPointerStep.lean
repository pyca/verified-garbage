module
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer

import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # Advancing and saving a packed-key component pointer -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem addPointer_ok {s : State} {base : Addr} {size : Nat} (length dest : Field)
    (hs : Scr s base size) (hz : Layout.saved ≤ size) :
    WP isa (.block (Entry.addPointer length dest)) s fun t =>
      t.gpr .eax = s.gpr .eax + pointerValue base s (.input length) ∧
      pointerValue base t (.input dest) = s.gpr .eax + pointerValue base s (.input length) ∧
      Keeps [.eax] s t ∧ Outside base (Layout.field dest) 4 s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds dest
  have L := VG.Proof.Dsa.X86.Layout.field_bounds length
  unfold Entry.addPointer
  refine wp_addS (readSrc_sc hs (by omega)) fun u su _ => ?_
  have hu := hs.of_keeps su.keeps (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write (by omega)) fun t ut => WP.block_nil ⟨?_, ?_, ?_, ?_⟩
  · rw [ut.gpr, su.gpr]; rfl
  · change t.mem.readW (off base (Layout.field dest)) 32 = _
    rw [ut.mem, Mem.readW_writeW_self32, su.gpr]; rfl
  · exact su.keeps.trans (ut.keeps [.eax])
  · rw [ut.mem, su.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.Dsa.X86
