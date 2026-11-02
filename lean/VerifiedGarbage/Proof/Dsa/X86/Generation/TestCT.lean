module

import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.HashCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Dsa.X86.Generation.ABIEnv
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Geo
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestPre
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TimingBase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.Words

/-! # Two runs of a probable-prime test of the same candidate leak the same -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Dsa.X86
open VG.Impl.Dsa.X86.Generation
open VG.Impl.Mont.X86 (sc)

/-- Before a test: the witness cursor `p.1` and the candidate `p.2`. -/
def TPre (E : Env) (bits : Nat) (p : Nat × Nat) (s : State) : Prop :=
  Base E s ∧ s.mem.readW (off E.base fUsed) 32 = BitVec.ofNat 32 p.1 ∧ p.1 ≤ E.witLen ∧
    Proof.Dsa.ProbablePrime.candidateAt (VG.Impl.Dsa.X86.ProbablePrime.layout bits) s.mem (off E.base sPP) = p.2 ∧
    p.2 % 2 = 1 ∧ Spec.Dsa.bitLength p.2 = bits

/-- The test's writable regions, with `esp` at `E.sp`. -/
def testWrSp (E : Env) : List Region :=
  [⟨off E.base sPP, 8 * ppWords⟩, ⟨off E.base fUsedOut, 8⟩, ⟨(E.sp - 20#32).setWidth 64, 20⟩]

theorem testWr_sp {E : Env} {t : State} (h : t.gpr .esp = E.sp) : testWr E t = testWrSp E := by
  simp only [testWr, testWrSp, h]

theorem test_ct {bits : Nat} {name : String} {callee : Prog isa}
    (verified : Verified target callee (ppContract bits)) (noSp : NoSp callee) (stack : stackUse callee ≤ 152)
    {E : Env} (v : E.Valid) (lay : (VG.Impl.Dsa.X86.ProbablePrime.layout bits).size ≤ 8 * ppWords) :
    RelCT isa (Both (TPre E bits)) (test name callee) fun _ _ => True := by
  have sz := v.size_ge
  have psz : sPP ≤ E.size := by simp only [sPP]; omega
  unfold test
  simp only [seqs]
  -- The cursor and the octets left.
  refine RelCT.seq (both_post (Ψ := fun p t => ∃ s, TPre E bits p s ∧
      TestHead E.base (E.wit.setWidth 32) E.witLen p.1 s t)
    (both_agree [.esp, .edi] (fun _ => baseVal E) (fun _ _ h => base_pins h.1) (tcheck _ _ (by decide +kernel)))
    fun p s h => WP.mono (testHead_ok h.1.scr psz h.1.witW h.1.witLenW h.2.1 h.2.2.1 v.lens.2.2)
      fun t H => ⟨s, h, H⟩) ?_
  have pins₁ : ∀ (p : Nat × Nat) t, (∃ s, TPre E bits p s ∧ TestHead E.base (E.wit.setWidth 32) E.witLen p.1 s t) →
      ∀ r ∈ [Reg.esp, .edi], t.gpr r = baseVal E r := by
    rintro p t ⟨s, h, H⟩ r hr
    rw [H.other r (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl <;> decide) (by simp at hr; rcases hr with rfl | rfl <;> decide)
      (by simp at hr; rcases hr with rfl | rfl <;> decide)]
    exact base_pins h.1 r hr
  refine RelCT.assoc (RelCT.seq (both_post (Ψ := fun p t => ∃ s, TPre E bits p s ∧
      TestArgs E.base (E.wit.setWidth 32) E.witLen p.1 s t) ?_
    fun p t ⟨s, h, H⟩ => WP.mono (testMid_ok h.1.scr psz h.1.witW H) fun u A => ⟨s, h, A⟩) ?_)
  · -- The pointer to the witnesses left.
    refine RelCT.seq (both_ite (fun p => decide (E.witLen - p.1 = 0)) (fun p t ⟨s, _, H⟩ => H.zf)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun p t h => pins₁ p t h.1) (tkeep _ _ (by decide +kernel)))
      (RelCT.nil fun x y ⟨p, h₁, h₂⟩ => agree_regs fun r hr =>
        (pins₁ p x h₁.1 r hr).trans (pins₁ p y h₂.1 r hr).symm)) (tcheck _ _ (by decide +kernel))
  refine RelCT.seq (both_post (Φ := fun p t => ∃ s, TPre E bits p s ∧
      TestArgs E.base (E.wit.setWidth 32) E.witLen p.1 s t)
    (Ψ := fun p u => ∃ s, TPre E bits p s ∧ TestRet E bits p.1 p.2 s u) ?_ fun p t hp => by
      obtain ⟨s, h, A⟩ := hp
      refine WP.mono (testCall_ok verified noSp stack v h.1 A h.2.2.1 lay
        (by rw [h.2.2.2.1]; exact h.2.2.2.2.1) (by rw [h.2.2.2.1]; exact h.2.2.2.2.2)) fun u R => ⟨s, h, ?_⟩
      rw [← h.2.2.2.1]; exact R) ?_
  · -- The call.
    refine both_exists fun p => ?_
    refine callWithPop (rs := testRegs) verified.1 verified.2.1 (testRd E p.1) (testWrSp E)
      fun t₁ t₂ hp => ?_
    obtain ⟨⟨s₁, h₁, A₁⟩, ⟨s₂, h₂, A₂⟩⟩ := hp
    have sp₁ : t₁.gpr .esp = E.sp := by
      rw [A₁.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h₁.1.sp]
    have sp₂ : t₂.gpr .esp = E.sp := by
      rw [A₂.other _ (by decide) (by decide) (by decide) (by decide) (by decide), h₂.1.sp]
    have c₁ := testCallPre v h₁.1 A₁ h₁.2.2.1 lay (by rw [h₁.2.2.2.1]; exact h₁.2.2.2.2.1)
      (by rw [h₁.2.2.2.1]; exact h₁.2.2.2.2.2)
    have c₂ := testCallPre v h₂.1 A₂ h₂.2.2.1 lay (by rw [h₂.2.2.2.1]; exact h₂.2.2.2.2.1)
      (by rw [h₂.2.2.2.1]; exact h₂.2.2.2.2.2)
    rw [testWr_sp sp₁] at c₁
    rw [testWr_sp sp₂] at c₂
    have F₁ := testEntry_facts v h₁.1 A₁ h₁.2.2.1 lay
    have F₂ := testEntry_facts v h₂.1 A₂ h₂.2.2.1 lay
    simp only [testEntry, testWr_sp sp₁, testWr_sp sp₂] at F₁ F₂
    refine ⟨c₁, c₂, sp₁.trans sp₂.symm, ?_⟩
    generalize (pushed testRegs t₁).callEntry.withRegions (testRd E p.1) (testWrSp E) = w₁ at F₁ ⊢
    generalize (pushed testRegs t₂).callEntry.withRegions (testRd E p.1) (testWrSp E) = w₂ at F₂ ⊢
    sig_pub [ppContract, Proof.Dsa.ProbablePrime.contract, Proof.Dsa.ProbablePrime.sig, abi, argSlots, argVal,
      argBytes, Abi.withConsts, VG.Impl.RsaKeyGen.TrialTable32.consts]
    obtain ⟨esp₁, sy₁, a0₁, a1₁, a2₁, a3₁, -, a0'₁, a2'₁, a3'₁, a4'₁, cand₁, ent₁⟩ := F₁
    obtain ⟨esp₂, sy₂, a0₂, a1₂, a2₂, a3₂, -, a0'₂, a2'₂, a3'₂, a4'₂, cand₂, ent₂⟩ := F₂
    refine ⟨esp₁.trans esp₂.symm, ?_, ?_, by rw [a0'₁, a0'₂, h₁.1.edi, h₂.1.edi], a1₁.trans a1₂.symm,
      a2'₁.trans a2'₂.symm, a3'₁.trans a3'₂.symm, by rw [a4'₁, a4'₂, h₁.1.edi, h₂.1.edi]⟩
    · rw [sy₁, sy₂]
      have e := h₁.1.syms.trans h₂.1.syms.symm
      exact BitVec.eq_of_toNat_eq (by
        have := congrArg BitVec.toNat e
        rwa [toNat_wide, toNat_wide] at this)
    · rw [a0₁, a2₁, a3₁, cand₁, ent₁, a0₂, a2₂, a3₂, cand₂, ent₂, h₁.2.2.2.1, h₂.2.2.2.1]
  -- The status, and the octets read.
  have pins₃ : ∀ (p : Nat × Nat) u, (∃ s, TPre E bits p s ∧ TestRet E bits p.1 p.2 s u) →
      ∀ r ∈ [Reg.esp, .edi], u.gpr r = baseVal E r := by
    rintro p u ⟨s, h, R⟩ r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact R.esp
    · exact R.edi.trans h.1.edi
  refine RelCT.seq (both_post (Ψ := fun p x => x.zf = some (BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
      (Spec.Dsa.probablePrime p.2 (E.witT.drop p.1))) - 0 == 0) ∧ ∀ r ∈ [Reg.esp, .edi], x.gpr r = baseVal E r)
    (both_agree [.esp, .edi] (fun _ => baseVal E) pins₃ (tcheck _ _ (by decide +kernel))) fun p u hp => ?_) ?_
  · obtain ⟨s, h, R⟩ := hp
    have hsU : Scr u E.base E.size := Scr.of_eq h.1.scr R.edi (R.esp.trans h.1.sp.symm) R.wr
    refine st_ok hsU (by simp only [fRes, hdr]; omega) fun x₁ M₁ => wp_cmpi fun x₂ F₂ _ z₂ => WP.block_nil ⟨?_, ?_⟩
    · rw [z₂, M₁.gpr, R.eax]
    · intro r hr; rw [F₂.gpr, M₁.gpr]; exact pins₃ p u ⟨s, h, R⟩ r hr
  · refine both_ite (fun p => BitVec.ofNat 32 (Proof.Dsa.ProbablePrime.status
      (Spec.Dsa.probablePrime p.2 (E.witT.drop p.1))) - 0 == 0) (fun p x h => h.1) (RelCT.nil fun _ _ _ => trivial)
      (both_agree [.esp, .edi] (fun _ => baseVal E) (fun p x h => h.1.2) (tcheck _ _ (by decide +kernel)))

end VG.Proof.Dsa.X86.Generation
