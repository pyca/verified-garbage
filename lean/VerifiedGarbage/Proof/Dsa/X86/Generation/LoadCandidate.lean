module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.CheckCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoadNumber
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparationReads
import VerifiedGarbage.Proof.Dsa.X86.LocalOperand
import VerifiedGarbage.Proof.Mont.OutsFrame
import VerifiedGarbage.Proof.Mont.X86.ContextLayout
import VerifiedGarbage.Proof.Framework.Offset

/-! The existing padded big-endian loader stages either a subgroup or modulus candidate. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic

theorem load_candidate {s : State} {base : Addr} {bytes n len offset : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (upper : n ≤ 48)
    (lower : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (sourceLow : 16384 ≤ offset) (sourceFit : offset + len ≤ bytes) :
    WP isa (VG.Impl.Dsa.X86.Core.load n len (slot n 0) (.local offset)) s fun t =>
      wordsVal t.mem base (slot n 0) n = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off base offset) len) ∧
      PreparationFrame base (s.gpr .esp) s t ∧ Keeps VG.Proof.Dsa.X86.loadClob s t := by
  have slotFit : slot n 0 + 8 * n ≤ montgomeryBytes := by
    simp only [slot, stride, montgomeryBytes]
    omega
  refine WP.mono (load_number scr capacity upper lower length aligned sourceLow sourceFit
    (by unfold contextBytes slot stride; omega)) fun t ⟨value, O, K⟩ => ?_
  refine ⟨value, ?_, K⟩
  apply (O.frameAt (by unfold slot stride; omega)).sub
  intro region hr
  rw [List.mem_singleton.mp hr]
  exact ⟨⟨base, montgomeryBytes⟩, by simp, Offset.sub_base base slotFit⟩

end VG.Proof.Dsa.X86.Generation
