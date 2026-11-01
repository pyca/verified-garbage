module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.Context
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarLayout

/-! Native key-generation states used to compose functional and timing proofs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

structure SampleReady (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : SampleContext p l slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  scalar : Octets p.base p.privateValue p.len (l.encode rb) s
  significant : Octets p.base l.start p.len ((l.encode rb).drop l.lead) s
  outputs : KeyOutputs p s

structure SampleImported (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleReady p l slots rb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip (l.encode rb)

structure SampleRanged (p : Inputs) (l : ScalarLayout p) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends SampleReady p l slots rb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip (l.encode rb))

theorem SampleReady.after_mem {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : SampleReady p l slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : SampleReady p l slots rb t := by
  have ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨⟨h.context.toContext.of_mem mem rest ptr, by rw [rest.sp, mem]; exact h.context.scalarStart, by rw [rest.sp, mem]; exact h.context.scalarWidth, by rw [rest.sp, mem]; exact h.context.scalarMask⟩, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩

theorem SampleRanged.after_mem {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : SampleRanged p l slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : SampleRanged p l slots rb t :=
  ⟨h.toSampleReady.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem sampleSample_next (env : SampleEnvironment) (sample : Prog isa) (layout : (p : Inputs) → ScalarLayout p)
    (sampler : SampleLaw env layout sample) (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (special : sampleSlots slots)
    (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyPrepared p slots rb s) (environment : env.holds p s) (normalized : 2 ^ (64 * (p.w - 1)) ≤ p.P) (odd : p.P % 2 = 1) :
    WP isa sample s (SampleReady p (layout p) slots rb) := by
  refine WP.mono (sampler.correct s h.context environment normalized odd stable special h0 h24 h28 h32 h40 h48 h60 h.ready h.modulus h.r2
    h.entropy size h.entropyStack h.outputs entropySep) ?_
  rintro t ⟨context, ready, modulus, r2, scalar, significant, _, rest⟩
  exact ⟨context, ready, modulus, r2, scalar, significant, h.outputs.after rest⟩

theorem sampleImport_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (size : rb.length = p.k) (privateLength : p.privateLength = p.k) (h : SampleReady p l slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (SampleImported p l slots rb) := by
  have length := l.encode_length size
  refine WP.mono (importAt_ok s 1 40 44 h.context.toContext stable h40 h44 h.ready (by decide) (by decide) h.scalar
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength, length])) ?_
  rintro t ⟨context, ready, imported, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide)).trans h.modulus,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 4) (by decide)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, imported⟩

theorem sampleRange_scalar_next (s : State) {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (odd : p.P % 2 = 1) (h : SampleImported p l slots rb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (SampleRanged p l slots rb) := by
  refine WP.mono (scalarRange_ok s h.context.toContext stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro t ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨h.context.after_workspace frame rest context.ptr (fun d hd => (stableSlots_at stable hd).1), ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, flag⟩

end VG.Proof.Ffdh.Arm
