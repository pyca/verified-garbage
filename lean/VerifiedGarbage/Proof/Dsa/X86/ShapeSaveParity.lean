module
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine

import VerifiedGarbage.Proof.Mont.X86.ContextInit
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # Saving p's parity before reusing the context to inspect q -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86

theorem saveParity_ok {s : State} {base : Addr} {size n m : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hm : wordsVal s.mem base (slot n 0) n = m) :
    WP isa (.block (Shape.saveParity n)) s fun t =>
      (shapeWord t base 56).toNat % 2 = m % 2 ∧ Keeps [.eax] s t ∧ Outside base 56 4 s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have bh := slot_header n 9
  change 64 ≤ contextBytes n at bh
  simp only [stride] at b0
  unfold Shape.saveParity
  refine wp_movS (readSrc_sc hs (d := slot n 0) (by omega)) fun u uu _ => ?_
  have hu := hs.of_keeps uu.keeps (by decide)
  refine wp_storeS (hu.ea (d := 56) (by omega)) (hu.write (d := 56) (n := 4) (by omega)) fun t mt =>
    WP.block_nil ⟨?_, uu.keeps.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, uu.gpr]
    have low := modulus_low hn hm
    change w32 s.mem base (slot n 0) % 2 = m % 2
    omega
  · rw [mt.mem, uu.mem]
    exact writeW32_outside _ _ _ (by decide)

end VG.Proof.Dsa.X86
