module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyClear
import VerifiedGarbage.Proof.Ffdh.Arm.KeyMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
import VerifiedGarbage.Proof.Ffdh.Arm.Branch
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Block
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.Context

/-! Out-of-range random scalars return retry status 2 and clear both encodings. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm
open VG.Proof.X25519.Arm (Rest)

theorem keyFail_ok (s : State) {p : Inputs} {slots : List Nat}
    (h : ArgumentMemory p slots s) (saved : ∀ d ∈ slots, d + 4 ≤ 72)
    (h32 : 32 ∈ slots) (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (outputs : KeyOutputs p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar s fun t =>
      t.gpr .r0 = 2 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.privateValue) p.k = List.replicate p.k 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.publicValue) p.k = List.replicate p.k 0 ∧
      Frame [⟨State.addr p.privateValue, p.k⟩, ⟨State.addr p.publicValue, p.k⟩] s.mem t.mem := by
  rw [VG.Impl.Ffdh.Arm.Domain.GenerateKey.failScalar, WP.seq_iff]
  refine WP.mono (keyClear_ok s 40 h (by decide) h40 h32 outputs.privateBuffer) ?_
  rintro u ⟨privateU, frameU, restU⟩
  change Spec.Rsa.bytesAt u.mem (State.addr p.privateValue) p.k = _ at privateU
  change Frame [⟨State.addr p.privateValue, p.k⟩] s.mem u.mem at frameU
  have contextU := h.after_output frameU restU outputs.privateDomain outputs.privateStack saved
  rw [WP.seq_iff]
  refine WP.mono (keyClear_ok u 36 contextU (by decide) h36 h32 (outputs.publicBuffer.after restU)) ?_
  rintro v ⟨publicV, frameV, _⟩
  change Spec.Rsa.bytesAt v.mem (State.addr p.publicValue) p.k = _ at publicV
  change Frame [⟨State.addr p.publicValue, p.k⟩] u.mem v.mem at frameV
  refine WP.mono (ret_ok v 2 (by decide)) ?_
  rintro t ⟨⟨status, mem⟩, _⟩
  refine ⟨status, ?_, by rw [mem]; exact publicV, ?_⟩
  · rw [mem, VG.Proof.Bignum.Arm.rsa_bytes_frame frameV (by have := p.maxLength; omega)
      (by simpa using outputs.separate)]
    exact privateU
  · rw [mem]
    exact (frameU.mono (by simp)).trans (frameV.mono (by simp))

end VG.Proof.Ffdh.Arm
