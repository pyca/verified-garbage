module

public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ZeroOptional
import VerifiedGarbage.Proof.Ffdh.Arm.OutputSlice
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.X25519.Arm.Instr
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.Arm.Isa

/-! Clear only the publicly known leading scalar bytes while advancing the
entropy and output pointers together. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem samplePrefix_ok (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat}
    (h : SampleMemory p l slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (output : OutputBuffer p.privateValue p.k s)
    (domainSep : Region.Disjoint ⟨State.addr p.domain, p.dom.length⟩ ⟨State.addr p.privateValue, p.k⟩)
    (stackSep : Region.Disjoint ⟨State.addr s.sp, 72⟩ ⟨State.addr p.privateValue, p.k⟩)
    (source : s.gpr .r1 = p.entropy) (dest : s.gpr .r0 = p.privateValue)
    (count : s.gpr .lr = BitVec.ofNat 32 l.lead) (zero : s.gpr .r2 = 0) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.GenerateKey.unlessZero .lr
      (.loop (.block VG.Impl.Ffdh.Arm.Domain.GenerateKey.prefixStep) .ne)) s fun t =>
      SampleMemory p l slots t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) l.lead = List.replicate l.lead 0 ∧
      t.gpr .r0 = l.start ∧ t.gpr .r1 = p.entropy + BitVec.ofNat 32 l.lead ∧
      Frame [⟨State.addr p.privateValue, l.lead⟩] s.mem t.mem ∧ Rest [.r0, .r1, .lr] s t := by
  have bound : l.lead ≤ p.k := by have := l.lead_lt; omega
  have buf := output.prefix bound
  refine WP.mono (zeroOptional_ok true s (by have := p.maxLength; omega) buf.fits buf.writable
    zero source dest count) ?_
  rintro t ⟨bytes, ptr, src, frame, rest⟩
  have sub : (⟨State.addr p.privateValue, l.lead⟩ : Region).Sub ⟨State.addr p.privateValue, p.k⟩ :=
    Region.sub_prefix bound
  have context := h.after_output frame rest (domainSep.sub_right sub) (stackSep.sub_right sub) saved
  exact ⟨context, bytes, ptr, src, frame, rest⟩

end VG.Proof.Ffdh.Arm
