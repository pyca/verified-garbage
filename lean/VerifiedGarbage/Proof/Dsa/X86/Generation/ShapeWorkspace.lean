module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.WorkspaceCopyArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.QShape
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HashWorkspacePointers
import VerifiedGarbage.Proof.Bignum.CopyOctets
import VerifiedGarbage.Proof.Framework.Offset

/-! Reuse the byte shaper for any disjoint saved workspace buffers. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Bignum.X86

theorem shape_workspace {s : State} {base : Addr} {bytes source destination len : Nat} {bs : List Byte}
    (scr : Scr s base bytes) (lower : 2 ≤ len) (length : bs.length = len)
    (sourceFit : source + len < bytes) (destinationFit : destination + len < bytes)
    (separate : source + len ≤ destination ∨ destination + len ≤ source)
    (input : Spec.Rsa.bytesAt s.mem (off base source) len = bs) :
    WP isa (shapeWorkspace source destination len) s fun t =>
      Spec.Rsa.bytesAt t.mem (off base destination) len = VG.Proof.Ffdh.ParameterCandidate.shapedOctets bs 7 ∧
      Frame [⟨off base destination, len⟩] s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  have srcAddr : byteAddr (s.gpr .edi + BitVec.ofNat 32 source) = off base source :=
    workspace_pointer_address scr (by omega)
  have dstAddr : byteAddr (s.gpr .edi + BitVec.ofNat 32 destination) = off base destination :=
    workspace_pointer_address scr (by omega)
  unfold shapeWorkspace
  refine WP.seq (WP.mono (workspace_copy_arguments (s := s) source destination len)
    fun a ⟨src, dst, count, memory, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  refine WP.mono (q_shape (bs := bs) (by omega) (by have := scr.nowrap; omega)
    (by rw [length]; exact workspace_pointer_fit scr sourceFit)
    (by rw [length]; exact workspace_pointer_fit scr destinationFit) src dst (by rw [length]; exact count)
    (by rw [srcAddr, length]; exact Sa.read (by omega))
    (by rw [dstAddr, length]; exact Sa.write (by omega))
    (by
      rw [srcAddr, dstAddr, length]
      exact Offset.disjoint base separate
        (by have := scr.nowrap; omega) (by have := scr.nowrap; omega))
    (by
      intro i hi
      rw [srcAddr, memory, ← VG.Proof.Bignum.bytesAt_getD s.mem (off base source) (by omega : i < len), input]))
    fun t ⟨shaped, F, KT⟩ => ?_
  rw [dstAddr, length] at shaped F
  rw [memory] at F
  exact ⟨shaped, F, (K.mono (by decide)).trans (KT.mono (by decide))⟩

end VG.Proof.Dsa.X86.Generation
