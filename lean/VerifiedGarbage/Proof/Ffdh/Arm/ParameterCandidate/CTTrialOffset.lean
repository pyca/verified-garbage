module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialSmall
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
public import Init.Prelude
public import VerifiedGarbage.TCB.Arm.Isa

/-! The offset carry is determined by the public trial divisor and preserves the public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

private def OriginalReady (p : TrialData) (s : State) : Prop :=
  TrialState p s ∧ s.gpr .r0 = p.dst + BitVec.ofNat 32 p.n ∧ s.gpr .r1 = BitVec.ofNat 32 p.n ∧
  s.gpr .r2 = 0 ∧ s.gpr .r3 = p.prime ∧ s.gpr .r4 = VG.Proof.RsaKeyGen.ninv p.prime

private theorem trialStart_ready (p : TrialData) (s : State) (h : TrialState p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) s (OriginalReady p) := by
  refine WP.mono (trialStart_ok s p.dst p.n (h.1.frame.read (by decide)) (h.1.frame.read (by decide))
    (h.1.frame.saved 4 (by decide)) (h.1.frame.saved 12 (by decide))) ?_
  rintro t ⟨⟨ptr, count, acc, prime, inverse, memory⟩, rest⟩
  rw [h.2.1] at prime inverse
  exact ⟨⟨h.1.after_memory memory rest, (rest.gpr .r7 (by simp)).trans h.2.1,
    by rw [memory]; exact h.2.2⟩, ptr, count, acc, prime, inverse⟩

private def TrialReady (p : TrialData) (s : State) : Prop :=
  TrialState p s ∧ s.gpr .r0 = p.dst + BitVec.ofNat 32 p.n ∧ s.gpr .r1 = BitVec.ofNat 32 p.n ∧
  s.gpr .r2 = p.prime-1 ∧ s.gpr .r3 = p.prime ∧ s.gpr .r4 = VG.Proof.RsaKeyGen.ninv p.prime

private theorem offset_ready (p : TrialData) (s : State) (h : OriginalReady p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffsetInit) s (TrialReady p) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffsetInit
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_imm (by decide)) fun t upd => WP.block_nil ?_
  have rest := upd.rest (by simp : Reg.r2 ∈ [.r2])
  refine ⟨⟨h.1.1.after_memory upd.mem rest, (rest.gpr .r7 (by simp)).trans h.1.2.1,
    by rw [upd.mem]; exact h.1.2.2⟩,
    (rest.gpr .r0 (by simp)).trans h.2.1, (rest.gpr .r1 (by simp)).trans h.2.2.1,
    ?_, (rest.gpr .r3 (by simp)).trans h.2.2.2.2.1,
    (rest.gpr .r4 (by simp)).trans h.2.2.2.2.2⟩
  rw [upd.gpr,VG.Proof.X25519.Arm.dpVal,h.2.2.2.2.1]

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

theorem trialOffset_ct : RelCT isa (Two TrialState)
    VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffset (fun s t => s.gpr .r2 = t.gpr .r2) := by
  have start : RelCT isa (Two TrialState) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialStart) (Two OriginalReady) :=
    two_post (trialStart_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) trialStart_ready
  have offset : RelCT isa (Two OriginalReady) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.trialOffsetInit) (Two TrialReady) :=
    two_post ((VG.Proof.Bignum.Arm.stackOnly_ct _ (by decide)).mono
      (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)) offset_ready
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
  exact start.seq (offset.seq (loop.seq (keep.seq (RelCT.block_nil (fun _ _ h => h)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
