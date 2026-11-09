module

public import VerifiedGarbage.Impl.Ffdh.Arm.Domain
import VerifiedGarbage.Proof.Ffdh.Arm.SampleMemory
public import VerifiedGarbage.Proof.Ffdh.Arm.KeyState
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

end VG.Proof.Ffdh.Arm
