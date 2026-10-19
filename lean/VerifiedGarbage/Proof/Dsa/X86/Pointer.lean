module

public import VerifiedGarbage.Impl.Dsa.X86.Core
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Address selection for caller components and persistent DSA values -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

/-- The address selected by the public operand descriptor. -/
def pointerValue (base : Addr) (s : State) : Pointer → BitVec 32
  | .input f => s.mem.readW (off base (VG.Impl.Dsa.X86.Layout.field f)) 32
  | .local offset => s.gpr .edi + BitVec.ofNat 32 offset
  | .signatureS => s.mem.readW (off base (VG.Impl.Dsa.X86.Layout.field .signature)) 32 +
      s.mem.readW (off base (VG.Impl.Dsa.X86.Layout.field .qLen)) 32

theorem pointer_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (p : Pointer) :
    WP isa (.block (Core.pointer p)) s fun t =>
      t.gpr .esi = pointerValue base s p ∧ Keeps [.esi] s t ∧ t.mem = s.mem := by
  have bound (f : Field) : VG.Impl.Dsa.X86.Layout.field f + 4 ≤ size := by
    have := VG.Proof.Dsa.X86.Layout.field_bounds f
    omega
  cases p with
  | input f =>
    unfold Core.pointer pointerValue
    exact wp_movS (readSrc_sc hs (bound f)) fun t u _ => WP.block_nil ⟨u.gpr, u.keeps, u.mem⟩
  | «local» offset =>
    unfold Core.pointer pointerValue
    refine wp_movS rfl fun u uu _ => ?_
    refine wp_addS rfl fun t ut _ => WP.block_nil
      ⟨by rw [ut.gpr, uu.gpr], uu.keeps.trans ut.keeps, by rw [ut.mem, uu.mem]⟩
  | signatureS =>
    unfold Core.pointer pointerValue
    refine wp_movS (readSrc_sc hs (bound .signature)) fun u uu _ => ?_
    refine wp_addS (readSrc_sc (hs.of_keeps uu.keeps (by decide)) (bound .qLen)) fun t ut _ =>
      WP.block_nil ⟨by rw [ut.gpr, uu.gpr, uu.mem], uu.keeps.trans ut.keeps, by rw [ut.mem, uu.mem]⟩

end VG.Proof.Dsa.X86
