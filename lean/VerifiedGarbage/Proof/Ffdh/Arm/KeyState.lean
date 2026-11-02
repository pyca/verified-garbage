module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarCT
import VerifiedGarbage.Proof.Ffdh.Arm.KeySample
import VerifiedGarbage.Proof.Ffdh.Arm.PrepareAt
public import VerifiedGarbage.Proof.Ffdh.Arm.ScalarRange
import VerifiedGarbage.Proof.Ffdh.Arm.ImportAt
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.KeepsLayout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.PrepareStack
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyOutputs
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyScalarSpec

/-! Native key-generation states used to compose functional and timing proofs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Rsa.Mont (numAt Operand arrAt)
open VG.Proof.X25519.Arm (Rest)

structure KeyPrepared (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyScalarInput p slots rb s where
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P

structure KeyReady (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop where
  context : Context p slots s
  ready : ArithmeticReady p.base p.len p.w s
  modulus : numAt s.mem (State.addr p.base) p.w 0 = p.P
  r2 : numAt s.mem (State.addr p.base) p.w 4 = 2 ^ (128 * p.w) % p.P
  scalar : Octets p.base p.privateValue p.len (scalarOctets p rb) s
  significant : Octets p.base p.scalarStart p.len ((scalarOctets p rb).drop p.scalarLead) s
  outputs : KeyOutputs p s

structure KeyImported (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyReady p slots rb s where
  imported : numAt s.mem (State.addr p.base) p.w 1 = Spec.Rsa.os2ip (scalarOctets p rb)

structure KeyRanged (p : Inputs) (slots : List Nat) (rb : List Byte) (s : State) : Prop extends KeyReady p slots rb s where
  flag : s.gpr .r11 = scalarValidFlag p (Spec.Rsa.os2ip (scalarOctets p rb))

theorem KeyReady.after_mem {p : Inputs} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : KeyReady p slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : KeyReady p slots rb t := by
  have ptr := (rest.gpr .r0 (by simp)).trans h.context.ptr
  have frame : Frame [⟨State.addr p.base, 8 * p.len⟩] s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.context.of_mem mem rest ptr, h.ready.of_mem mem rest ptr, by rw [mem]; exact h.modulus,
    by rw [mem]; exact h.r2, h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩

theorem KeyRanged.after_mem {p : Inputs} {slots : List Nat} {rb : List Byte} {s t : State}
    (h : KeyRanged p slots rb s) (mem : t.mem = s.mem) (rest : Rest [] s t) : KeyRanged p slots rb t :=
  ⟨h.toKeyReady.after_mem mem rest, (rest.gpr .r11 (by simp)).trans h.flag⟩

theorem keyPrepare_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h32 : 32 ∈ slots)
    (large : 1 < p.P) (odd : p.P % 2 = 1) (size : rb.length = p.k) (h : KeyScalarInput p slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.prepareAt 24) s (KeyPrepared p slots rb) := by
  have pStack : Region.Disjoint ⟨State.addr p.domain, p.k⟩ ⟨State.addr s.sp, 72⟩ :=
    h.context.domainStack.sub_left (Region.sub_prefix (by rw [p.domainLength]; split <;> omega))
  refine WP.mono (prepareAt_ok s 24 h.context stable h24 h32 h0 h.context.pBytes p.pLength pStack large odd) ?_
  rintro t ⟨context, ready, modulus, r2, frame, rest⟩
  have entropy := h.entropy.after_frame frame rest (by
    intro r hr
    simp only [prepareAtWrites, prepareWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.entropy.separate
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide))
    · rw [size]; exact h.entropyStack.sub_right (Offset.sub_base _ (by decide)))
  exact ⟨⟨context, entropy, h.outputs.after rest, by rw [rest.sp]; exact h.entropyStack⟩, ready, modulus, r2⟩

theorem keySample_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h0 : 0 ∈ slots) (h24 : 24 ∈ slots) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots)
    (h40 : 40 ∈ slots) (h48 : 48 ∈ slots) (h60 : 60 ∈ slots) (size : rb.length = p.k)
    (entropySep : Region.Disjoint ⟨State.addr p.entropy, p.k⟩ ⟨State.addr p.privateValue, p.k⟩)
    (h : KeyPrepared p slots rb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.GenerateKey.scalar s (KeyReady p (16 :: 68 :: 20 :: slots) rb) := by
  refine WP.mono (keySample_ok s h.context stable h0 h24 h28 h32 h40 h48 h60 h.ready h.modulus h.r2
    h.entropy size h.entropyStack h.outputs entropySep) ?_
  rintro t ⟨context, ready, modulus, r2, scalar, significant, _, rest⟩
  exact ⟨context, ready, modulus, r2, scalar, significant, h.outputs.after rest⟩

theorem keyImport_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h40 : 40 ∈ slots) (h44 : 44 ∈ slots)
    (size : rb.length = p.k) (privateLength : p.privateLength = p.k) (h : KeyReady p slots rb s) :
    WP isa (VG.Impl.Ffdh.Arm.Domain.importAt 1 40 44) s (KeyImported p slots rb) := by
  have length := scalarOctets_length (p := p) size
  refine WP.mono (importAt_ok s 1 40 44 h.context stable h40 h44 h.ready (by decide) (by decide) h.scalar
    (by rw [length]; have := p.minLength; omega) (by rw [length]; exact p.width.2.2.2.1)
    (by change BitVec.ofNat 32 p.privateLength = _; rw [privateLength, length])) ?_
  rintro t ⟨context, ready, imported, keeps, frame, rest⟩
  have fits : arrAt p.w 8 ≤ 8 * p.len := ready.width ▸ ready.layout.2.2.1
  exact ⟨⟨context, ready,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 0) (by decide)).trans h.modulus,
    (keeps_array_num keeps fits (by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp] : Operand 4) (by decide)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, imported⟩

theorem keyRange_scalar_next (s : State) {p : Inputs} {slots : List Nat} {rb : List Byte}
    (stable : stableSlots slots = true) (h28 : 28 ∈ slots) (h32 : 32 ∈ slots) (h60 : 60 ∈ slots)
    (odd : p.P % 2 = 1) (h : KeyImported p slots rb s) :
    WP isa VG.Impl.Ffdh.Arm.Domain.CheckPrivate.scalarRange s (KeyRanged p slots rb) := by
  refine WP.mono (scalarRange_ok s h.context stable h28 h32 h60 h.ready h.modulus odd) ?_
  rintro t ⟨context, ready, flag, arrays, frame, rest⟩
  rw [h.imported] at flag
  exact ⟨⟨context, ready, (arrays 0 (by simp)).trans h.modulus, (arrays 4 (by simp)).trans h.r2,
    h.scalar.after_workspace frame rest, h.significant.after_workspace frame rest, h.outputs.after rest⟩, flag⟩

end VG.Proof.Ffdh.Arm
