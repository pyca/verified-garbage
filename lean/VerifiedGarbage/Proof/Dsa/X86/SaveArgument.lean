module
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Impl.Dsa.X86.Entry

import VerifiedGarbage.Proof.Dsa.X86.Layout
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Mont.Words32
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass

/-! # Moving one cdecl argument into the persistent DSA header -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Mont.X86
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem saveArgument_ok {s : State} {base : Addr} {size i : Nat} {value : BitVec 32} (f : Field)
    (hs : Scr s base size) (hz : Layout.saved ≤ size)
    (hr : readSrc s (.mem (Entry.argument i)) = some value) :
    WP isa (.block (Entry.saveArgument i f)) s fun t =>
      pointerValue base t (.input f) = value ∧ Keeps [.eax] s t ∧
      Outside base (Layout.field f) 4 s.mem t.mem := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have bound : Layout.field f + 4 ≤ size := by omega
  unfold Entry.saveArgument
  refine wp_movS hr fun u su _ => ?_
  have hu := hs.of_keeps su.keeps (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write bound) fun t ut => WP.block_nil ⟨?_, ?_, ?_⟩
  · change t.mem.readW (off base (Layout.field f)) 32 = value
    rw [ut.mem, Mem.readW_writeW_self32, su.gpr]
  · exact su.keeps.trans (ut.keeps [.eax])
  · rw [ut.mem, su.mem]
    exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)

end VG.Proof.Dsa.X86
