module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.ZeroOptional
public import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Framework.Offset

/-! Clear only the publicly known leading scalar bytes while advancing the
entropy and output pointers together. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem keyPrefix_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy) (dest : s.gpr .r0 = p.privateValue)
    (count : s.gpr .lr = BitVec.ofNat 32 p.scalarLead) (zero : s.gpr .r2 = 0) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s fun t =>
      ArgumentMemory p slots t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.scalarLead = List.replicate p.scalarLead 0 ∧
      t.gpr .r0 = p.scalarStart ∧ t.gpr .r1 = p.entropy + BitVec.ofNat 32 p.scalarLead ∧
      Frame [⟨State.addr p.privateValue, p.scalarLead⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  have bound : p.scalarLead ≤ p.k := by have := p.scalarLeadBound; omega
  have buf := output.prefix bound
  refine WP.mono (zeroOptional_ok true s (by have := p.maxLength; omega) buf.fits buf.writable
    zero source dest count) ?_
  rintro t ⟨bytes, ptr, src, frame, rest⟩
  have sub : (⟨State.addr p.privateValue, p.scalarLead⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Region.sub_prefix bound
  have context := h.after_output frame rest (domainSep.sub_right sub) (stackSep.sub_right sub) saved
  exact ⟨context, bytes, ptr, src, frame, rest⟩

end VG.Proof.Ffdh.Arm
