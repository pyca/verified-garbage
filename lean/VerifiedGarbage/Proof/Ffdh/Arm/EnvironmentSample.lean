module

public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticExternal
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentScalar
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Impl.Ffdh.Arm.SampleScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalar
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentBoundLaw

/-! Scalar sampling preserves the prepared RSA modulus and exposes both the
full output encoding and its public-width significant suffix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt)
open VG.Proof.X25519.Arm (Rest)

theorem environmentSample_ok (env : SampleEnvironment) (layout : (p : Inputs) → ScalarLayout p) (bound : Prog isa)
    (law : EnvironmentBoundLaw env layout bound) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (h : Context p slots s) (environment : env.holds p s)
    (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots)
    (ready : ArithmeticReady p.base p.len p.w s)
    (modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P)
    (r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P)
    (entropy : Octets p.base p.entropy p.len rb s) (size : rb.length = p.k)
    (entropyStack : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr s.sp, 72⟩)
    (outputs : KeyOutputs p s)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩) :
    WP isa (VG.Impl.Ffdh.Arm.SampleScalar.code bound) s fun t =>
      SampleContext p (layout p) slots t ∧ ArithmeticReady p.base p.len p.w t ∧
      numAt t.mem (State.addr p.base) p.w 0 = p.P ∧
      numAt t.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P ∧
      Octets p.base p.privateValue p.len ((layout p).encode rb) t ∧
      Octets p.base (layout p).start p.len (((layout p).encode rb).drop (layout p).lead) t ∧
      Frame (keyScalarWrites p s) s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (environmentScalar_ok env layout bound law s h environment normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 entropy size entropyStack
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
  have fits : Spec.Rsa.Mont.arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  have scalar : Octets p.base p.privateValue p.len ((layout p).encode rb) t := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [(layout p).encode_length size]; exact outputs.privateBuffer.fits
    · rw [(layout p).encode_length size, rest.rd, rest.wr]
      obtain ⟨r, hr, hc⟩ := outputs.privateBuffer.writable
      exact ⟨r, List.mem_append_right _ hr, hc⟩
    · rw [(layout p).encode_length size]; exact outputs.privateWorkspace
    · rw [(layout p).encode_length size]; exact bytes
  have significant := scalar.slice (d := (layout p).lead) (k := (layout p).width) (layout p).width_bounds.1
    (by rw [(layout p).encode_length size]; unfold ScalarLayout.width; have := (layout p).lead_lt; omega)
  rw [List.take_of_length_le (by rw [List.length_drop, (layout p).encode_length size]; rfl)] at significant
  exact ⟨context, readyT.1, (readyT.2.number fits (by decide : 0 < 8)).trans modulus,
    (readyT.2.number fits (by decide : 4 < 8)).trans r2, scalar, significant, frame, rest⟩

end VG.Proof.Ffdh.Arm
