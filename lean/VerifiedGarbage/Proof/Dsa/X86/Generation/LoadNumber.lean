module

public import VerifiedGarbage.Proof.Dsa.X86.CoreLoad
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CheckCandidate
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! Load a saved candidate or subgroup with the common padded big-endian loader. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem load_number {s : State} {base : Addr} {bytes n len source destination : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48)
    (lower : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (sourceLow : 16384 ≤ source) (sourceFit : source + len ≤ bytes)
    (destinationFit : destination + 8 * n ≤ contextBytes n) :
    WP isa (VG.Impl.Dsa.X86.Core.load n len destination (.local source)) s fun t =>
      wordsVal t.mem base destination n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base source) len) ∧
      Outside base destination (8 * n) s.mem t.mem ∧ Keeps VG.Proof.Dsa.X86.loadClob s t := by
  have contextFit : contextBytes n ≤ bytes := by
    simp only [contextBytes, slot, stride]
    omega
  have sourceReady := VG.Proof.Dsa.X86.localReady scr (by omega) sourceFit
    (n := n) (by simp only [contextBytes, slot, stride]; omega)
  refine WP.mono (VG.Proof.Dsa.X86.coreLoad_ok scr (by unfold VG.Impl.Dsa.X86.Layout.saved; omega)
    (Nat.le_trans destinationFit contextFit) lower length aligned sourceReady.toReadableComponent
    (sourceReady.apart.sub_right (Offset.sub_base base destinationFit))) fun t ⟨value, K, O⟩ => ?_
  rw [VG.Proof.Dsa.X86.local_pointer scr (by omega) sourceFit] at value
  exact ⟨value, O, K⟩

end VG.Proof.Dsa.X86.Generation
