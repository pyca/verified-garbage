module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentSampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyCallMemory
import VerifiedGarbage.Proof.Framework.Arm.Syms
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.Arm.Isa

/-! Native key-generation states used to compose functional and timing proofs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

theorem environmentSample_next (env : SampleEnvironment) (sample : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (sampler : EnvironmentSampleLaw env layout sample) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h52 : 52 ∈ slots) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyPrepared p slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) :
    WP isa sample s (fun t => (SampleReady p (layout p) slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (sampler.correct s h.context environment normalized odd stable special h52 h0 h24 h28 h32 h40 h48 h60 h.ready h.modulus h.r2
    h.entropy size h.entropyStack h.outputs entropySep) ?_
  rintro t ⟨context, ready, modulus, r2, scalar, significant, frame, rest⟩ syms
  refine ⟨⟨⟨context, ready, modulus, r2, scalar, significant, h.outputs.after rest⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.sub (by
    intro r hr
    simp only [keyScalarWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr s.sp, 72⟩, by simp [keyCallWrites, keyWrites], Offset.sub_base _ (by decide)⟩
    · exact ⟨⟨State.addr p.privateValue, p.k⟩, by simp [keyCallWrites, keyWrites], fun _ hx => hx⟩)

theorem environmentImport_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (size : rb.length = p.k) (privateLength : p.privateLength = p.k) (h : SampleReady p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (fun t => (SampleImported p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  have length := l.encode_length size
  refine WP.mono_syms (importAt_ok s 1 40 44 h.context.toContext stable h40 h44 h.ready (by decide) (by decide) h.scalar
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength, length])) ?_
  rintro t ⟨context, ready, imported, keeps, frame, rest⟩ syms
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    (keeps_array_num keeps fits (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 0) (by decide)).trans h.modulus,
    (keeps_array_num keeps fits (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 4) (by decide)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, imported⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

theorem environmentRange_next (env : SampleEnvironment) (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (odd : p.P % 2 = 1) (h : SampleImported p l slots rb s) (calls : KeyCallMemory p s) (environment : env.holds p s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (fun t => (SampleRanged p l slots rb t ∧ KeyCallMemory p t) ∧ env.holds p t) := by
  refine WP.mono_syms (scalarRange_ok s h.context.toContext stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro t ⟨context, ready, flag, arrays, frame, rest⟩ syms
  rw [h.imported] at flag
  refine ⟨⟨⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, flag⟩, calls.after rest⟩, env.stable environment ?_ rest syms⟩
  exact frame.mono (by simp [keyCallWrites, keyWrites])

end VG.Proof.Ffdh.Arm
