module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialSmall
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy

/-! Each sieve step reads the same public table entry and candidate octets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint two_map two_ite)

structure SieveData where
  dst : BitVec 32
  base : BitVec 32
  bytes : List Byte

structure SieveStepStart (p : SieveData × Nat) (s : State) : Prop where
  context : SieveContext p.1.dst p.1.base p.1.bytes.length s
  index : p.2 < trialCount p.1.bytes.length
  cursor : s.gpr .r10 = p.1.base + BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((p.1.bytes.length + 7) / 8) 34 + 4 * p.2)
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p.1.dst) p.1.bytes.length = p.1.bytes
  bad : s.mem.readW (State.addr (s.sp + 64#32)) 32 = if sieveAny (Spec.Rsa.os2ip p.1.bytes) p.2 then 1 else 0

private structure SieveEntryReady (p : SieveData × Nat) (s : State) : Prop where
  context : SieveContext p.1.dst p.1.base p.1.bytes.length s
  index : p.2 < trialCount p.1.bytes.length
  prime : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2)
  bytes : Spec.Rsa.bytesAt s.mem (State.addr p.1.dst) p.1.bytes.length = p.1.bytes

private def SieveDivided (p : SieveData × Nat) (s : State) : Prop :=
  s.z = decide (Spec.Rsa.os2ip p.1.bytes % VG.Impl.RsaKeyGen.tabEntry p.2 = 0)

private def sieveTrial (p : SieveData × Nat) : TrialData :=
  ⟨p.1.dst, p.1.bytes.length, BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2), p.1.bytes.reverse⟩

theorem sieveActiveStep_ct : RelCT isa (Two SieveStepStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveActiveStep (fun _ _ => True) := by
  obtain ⟨hint, checked⟩ := sieveEntry_taint
  have entryTrace : RelCT isa (Two SieveStepStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveEntry)
      (fun _ _ => True) := by
    refine two_taint [.r10] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.cursor.trans b.cursor.symm
  have entry : RelCT isa (Two SieveStepStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveEntry) (Two SieveEntryReady) :=
    two_post entryTrace (fun p s h => WP.mono (sieveEntry_ok h.context h.index h.cursor) (fun t ⟨⟨prime, _, memory⟩, rest⟩ =>
      ⟨h.context.after_memory memory rest, h.index, prime, by rw [memory]; exact h.bytes⟩))
  have trialTrace : RelCT isa (Two SieveEntryReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall (fun _ _ => True) := by
    refine (two_map sieveTrial ?_ trialSmall_ct).mono (fun _ _ h => h) (fun _ _ _ => trivial)
    intro p s h
    have buffers := trialBuffers_of_octets (prime := BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry p.2)) h.context.read rfl h.bytes
    exact ⟨buffers.1, h.prime, buffers.2⟩
  have trial : RelCT isa (Two SieveEntryReady) VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall (Two SieveDivided) :=
    two_post trialTrace (fun p s h => by
      refine WP.mono (trialSmall_ok s p.1.dst h.context.read.positive h.context.read.countFits h.context.read.bufferFits
        (by have := h.index; have := trialCount_bound p.1.bytes.length; omega : p.2 < 1024) h.prime (h.context.read.frame.read (by decide))
        (h.context.read.frame.read (by decide)) h.context.read.out h.context.read.width h.context.read.readable) ?_
      rintro t ⟨flag, _, _⟩
      rwa [h.bytes] at flag)
  have flag : RelCT isa (Two SieveDivided) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag (fun s t => s.sp = t.sp) :=
    sieveFlag_ct.mono (fun _ _ ⟨_, a, b, sp⟩ => ⟨sp, a.trans b.symm⟩) (fun _ _ h => h)
  have count : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount)
      (fun s t => s.sp = t.sp) := stackOnly_ct _ rfl
  exact entry.seq (trial.seq (flag.seq (count.seq (RelCT.block_nil (fun _ _ _ => trivial)))))

private def SieveGuarded (p : SieveData × Nat) (s : State) : Prop :=
  SieveStepStart p s ∧ s.z = !sieveAny (Spec.Rsa.os2ip p.1.bytes) p.2

theorem sieveStep_ct : RelCT isa (Two SieveStepStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep (fun _ _ => True) := by
  have guardTrace : RelCT isa (Two SieveStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (fun _ _ => True) :=
    (stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)
  have guard : RelCT isa (Two SieveStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (Two SieveGuarded) := by
    refine two_post guardTrace ?_
    intro p s h
    refine WP.mono (sieveFinish_ok h.context.read.frame.space h.bad) ?_
    rintro t ⟨⟨flag, memory⟩, rest⟩
    refine ⟨⟨h.context.after_memory memory rest, h.index, ?_, ?_, ?_⟩, flag⟩
    · rw [rest.gpr .r10 (by simp)]; exact h.cursor
    · rw [memory]; exact h.bytes
    · rw [memory, rest.sp]; exact h.bad
  refine guard.seq (two_ite ?_ ?_ ?_)
  · intro p s t h k
    change some s.z = some t.z
    rw [h.2, k.2]
  · exact sieveActiveStep_ct.mono
      (fun _ _ ⟨p, a, b, sp⟩ => ⟨p, a.1.1, b.1.1, sp⟩) (fun _ _ h => h)
  · exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveSkip rfl).mono
      (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.ParameterCandidate
