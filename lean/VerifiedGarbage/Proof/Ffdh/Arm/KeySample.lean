module

import VerifiedGarbage.Proof.Ffdh.Arm.KeyGeometry
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Impl.Ffdh.Arm.GenerateKey
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
public import VerifiedGarbage.TCB.Arm.Isa

/-! Scalar sampling preserves the prepared RSA modulus and exposes both the
full output encoding and its public-width significant suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem keySample_ok (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (stable : stableSlots slots = true)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar s fun t =>
      Context p (16 :: 68 :: 20 :: slots) t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len (scalarOctets p rb) t ∧
      Octets p.base p.scalarStart p.len ((scalarOctets p rb).drop p.scalarLead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (keyScalar_ok s h stable h0 h24 h28 h32 h40 h48 h60 entropy size entropyStack
    outputs.privateBuffer outputs.privateDomain outputs.privateStack entropySep) ?_
  rintro t ⟨context, _, bytes, frame, rest⟩
  have workspaceSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr p.base, 8 * p.len⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact h.locals.separate.symm.sub_right (Offset.sub_base _ (by decide))
    · exact outputs.privateWorkspace.symm
  have baseSep (r : Region) (hr : r ∈ keyScalarWrites p s) :
      (⟨State.addr s.sp, 4⟩ : Region).Disjoint r := by
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact (Offset.disjoint_base _ (by decide) (by decide)).symm
    · exact outputs.privateStack.sub_left (Region.sub_prefix (by decide))
  have readyT := ready.after_external frame workspaceSep baseSep rest context.ptr
  have fits : Proof.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have scalar : Octets p.base p.privateValue p.len (scalarOctets p rb) t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [scalarOctets_length size]; exact outputs.privateBuffer.fits
    · rw [scalarOctets_length size, rest.rd, rest.wr]
      obtain ⟨r, hr, hc⟩ := outputs.privateBuffer.writable
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [scalarOctets_length size]; exact outputs.privateWorkspace
    · rw [scalarOctets_length size]; exact bytes
  have significant := scalar.slice (d := p.scalarLead) (k := p.scalarWidth) p.scalarWidthBounds.1
    (by rw [scalarOctets_length size]; unfold Inputs.scalarWidth; have := p.scalarLeadBound; omega)
  rw [List.take_of_length_le (by rw [List.length_drop, scalarOctets_length size]; rfl)] at significant
  exact ⟨context, readyT.1, (readyT.2.number fits (by decide : 0 < 8)).trans modulus,
    (readyT.2.number fits (by decide : 4 < 8)).trans r2, scalar, significant, frame, rest⟩

end VG.Proof.Ffdh.Arm
