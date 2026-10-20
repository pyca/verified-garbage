module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.TCB.Mem

/-! Complete small-prime reduction, with the branch accumulator determined by public octets. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

structure TrialData where
  dst : BitVec 32
  n : Nat
  prime : BitVec 32
  values : List Byte

def TrialState (p : TrialData) (s : State) : Prop :=
  ReadContext p.dst p.n s ∧ s.gpr .r7 = p.prime ∧
  ∀ i < p.n, s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - BitVec.ofNat 32 (i + 1))) = p.values[i]?.getD 0

private def TrialReady (p : TrialData) (s : State) : Prop :=
  TrialState p s ∧ s.gpr .r0 = p.dst + BitVec.ofNat 32 p.n ∧ s.gpr .r1 = BitVec.ofNat 32 p.n ∧
  s.gpr .r2 = 0 ∧ s.gpr .r3 = p.prime ∧ s.gpr .r4 = VG.Proof.RsaKeyGen.ninv p.prime

private theorem trialStart_ready (p : TrialData) (s : State) (h : TrialState p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s (TrialReady p) := by
  refine WP.mono (trialStart_ok s p.dst p.n (h.1.frame.read (by decide)) (h.1.frame.read (by decide))
    (h.1.frame.saved 4 (by decide)) (h.1.frame.saved 12 (by decide))) ?_
  rintro t ⟨⟨ptr, count, acc, prime, inverse, memory⟩, rest⟩
  rw [h.2.1] at prime inverse
  exact ⟨⟨h.1.after_memory memory rest, (rest.gpr .r7 (by simp)).trans h.2.1,
    by rw [memory]; exact h.2.2⟩, ptr, count, acc, prime, inverse⟩

private theorem trialReady_pair {s t : State} (h : Two TrialReady s t) : TrialLoopPair s t := by
  obtain ⟨p, a, b, _⟩ := h
  have countNat : (s.gpr .r1).toNat = p.n := by
    rw [a.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt a.1.1.countFits]
  refine ⟨a.2.1.trans b.2.1.symm, a.2.2.1.trans b.2.2.1.symm,
    a.2.2.2.1.trans b.2.2.2.1.symm, a.2.2.2.2.1.trans b.2.2.2.2.1.symm,
    a.2.2.2.2.2.trans b.2.2.2.2.2.symm, ?_, ?_, ?_, ?_⟩
  · rw [countNat]; exact a.1.1.positive
  · rw [countNat, a.2.1]; exact a.1.1.readable
  · rw [countNat, b.2.1]; exact b.1.1.readable
  · rw [countNat, a.2.1]
    intro i hi
    exact (a.1.2.2 i hi).trans (b.1.2.2 i hi).symm

theorem trialSmall_ct : RelCT isa (Two TrialState)
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall (fun s t => s.gpr .r2 = t.gpr .r2) := by
  have start : RelCT isa (Two TrialState) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) (Two TrialReady) :=
    two_post (trialStart_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) trialStart_ready
  have loop := trialLoop_ct.mono (fun _ _ h => trialReady_pair h) (fun _ _ h => h)
  obtain ⟨hint, checked⟩ := trialFlag_taint
  have flag : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag (fun _ _ => True) := by
    refine RelCT.taint (A := taint) (Taint.ofRegs [.r2]) ?_ checked
    intro s t h
    refine Taint.agree_ofRegs ?_
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact h
  have keep : RelCT isa (fun s t => s.gpr .r2 = t.gpr .r2)
      VG.Impl.Ffdh.Arm.ParameterCandidate.trialFlag (fun s t => s.gpr .r2 = t.gpr .r2) := by
    intro s t trS trT u v h runS runT
    obtain ⟨_, u', execS, _, _, restS⟩ := trialFlag_ok s
    obtain ⟨_, v', execT, _, _, restT⟩ := trialFlag_ok t
    obtain ⟨_, rfl⟩ := Exec.det runS execS
    obtain ⟨_, rfl⟩ := Exec.det runT execT
    exact ⟨(flag _ _ _ _ _ _ h runS runT).1,
      (restS.gpr .r2 (by simp)).trans (h.trans (restT.gpr .r2 (by simp)).symm)⟩
  exact start.seq (loop.seq (keep.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
