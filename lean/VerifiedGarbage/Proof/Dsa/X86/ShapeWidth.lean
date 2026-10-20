module

public import VerifiedGarbage.Proof.Dsa.X86.ShapeCombine
public import VerifiedGarbage.Proof.Ecdsa.X86.Flags
public import VerifiedGarbage.Spec.Dsa
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Dsa.X86.Width
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit

/-! # Saving actual-width checks in the public domain header -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem shapeWidth_ok {s : State} {base : Addr} {size n bits output : Nat}
    (hs : Scr s base size) (hn : 0 < n) (hz : contextBytes n ≤ size)
    (hb : 0 < bits) (ho : output + 4 ≤ size) :
    WP isa (Shape.saveWidth n bits output) s fun t =>
      shapeWord t base output = mask32 (Spec.Dsa.bitLength (wordsVal s.mem base (slot n 0) n) = bits) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s t ∧
      Outs base [(slot n 8, 8 * n), (output, 4)] s.mem t.mem := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have b8 := slot_bound (n := n) (i := 8) (by decide)
  have sep := slot_le (n := n) (i := 0) (j := 8) (by decide)
  simp only [stride] at b0 b8 sep
  unfold Shape.saveWidth
  refine WP.seq (WP.mono (optionalWidth_ok hs hn (by omega) (by omega) hb (.inl (by omega)))
    fun u ⟨Vu, Ku, Ou⟩ => ?_)
  have hu := hs.of_keeps Ku (by decide)
  refine wp_storeS (hu.ea (by omega)) (hu.write ho) fun t mt => WP.block_nil ⟨?_, Ku.trans (mt.keeps _), ?_⟩
  · rw [shapeWord, mt.mem, Mem.readW_writeW_self32, Vu]
  · have Ot : Outside base output 4 u.mem t.mem := by
      rw [mt.mem]
      exact writeW32_outside _ _ _ (by have := hs.nowrap; omega)
    exact (Outs.of_outside Ou (by simp)).trans (Outs.of_outside Ot (by simp))

end VG.Proof.Dsa.X86
