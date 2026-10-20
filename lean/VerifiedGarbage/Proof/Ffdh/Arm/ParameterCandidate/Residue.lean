module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ReadContext
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResiduePrime
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueLow
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueBytes
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Complete generator residue screening, using the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private theorem residue3_accept {acc p : Nat} (bound : acc < 6)
    (residue : acc % 3 = p % 3) (low : p % 8 = 3) :
    (acc ∈ [2, 5]) ↔ p % 24 = 11 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have criterion := residue24 (n := p)
  omega

private theorem residue5_accept {acc p : Nat} (bound : acc < 10)
    (residue : acc % 5 = p % 5) (odd : p % 2 = 1) :
    (acc ∈ [2, 3, 7, 8]) ↔ p % 10 = 3 ∨ p % 10 = 7 := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  have criterion := residue10 odd
  omega

theorem residue2_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 s fun t =>
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 24 = 11) ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue2
  refine WP.seq (WP.mono (residueLow_ok s dst n (h.frame.read (by decide))
    (h.frame.read (by decide)) h.out h.width (h.readable.low h.positive)) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  have last := candidate_mod8_last s.mem (State.addr dst) h.positive
  rw [h.lastAddress, ← last] at flag
  let p := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)
  change u.z = decide (p % 8 = 3) at flag
  by_cases low : p % 8 = 3
  · refine WP.ite true (by change some u.z = some true; rw [flag, decide_eq_true low]) ?_ (by intro h; cases h)
    intro _
    have trial := residuePrime_ok (h.after_memory memory rest) (prime := 0) (by decide) 2 [5] (by simp)
    rw [trialPrime3] at trial
    refine WP.mono trial ?_
    rintro t ⟨acc, bound, residue, accepted, memT, restT⟩
    have congruence : acc % 3 = p % 3 := by simpa only [memory] using residue
    exact ⟨accepted.trans (decide_eq_decide.mpr (residue3_accept bound congruence low)),
      memT.trans memory, (rest.mono (by simp)).trans restT⟩
  · refine WP.ite false (by change some u.z = some false; rw [flag, decide_eq_false low]) (by intro h; cases h) ?_
    intro _
    have reject : ¬ p % 24 = 11 := by have criterion := residue24 (n := p); omega
    refine WP.block_nil ⟨?_, memory, rest.mono (by simp)⟩
    change u.z = decide (p % 24 = 11)
    rw [flag, decide_eq_false low, decide_eq_false reject]

theorem residue5_ok {s : State} {dst : BitVec 32} {n : Nat} (h : ReadContext dst n s)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue5 s fun t =>
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 3 ∨
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 7) ∧
        t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue5
  have trial := residuePrime_ok h (prime := 1) (by decide) 2 [3, 7, 8] (by simp)
  rw [trialPrime5] at trial
  refine WP.mono trial ?_
  rintro t ⟨acc, bound, residue, flag, memory, rest⟩
  exact ⟨flag.trans (decide_eq_decide.mpr (residue5_accept bound residue odd)), memory, rest⟩

theorem residueHead_ok {s : State} {dst : BitVec 32} {n generator : Nat}
    (h : ReadContext dst n s) (bound : generator < 2 ^ 32)
    (saved : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 generator) :
    WP isa (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) s fun t =>
      (t.z = decide (generator = 2) ∧ t.mem = s.mem) ∧ Rest [.r1] s t := by
  have read := h.frame.read (d := 28) (by decide)
  have zero : ((BitVec.ofNat 32 generator - (2 : BitVec 32)) == (0 : BitVec 32)) = decide (generator = 2) := by
    rw [sub_beq_zero]
    exact ofNat_beq_eq bound (by decide)
  refine withRest [.r1] ?_ (by
    intro r hr op hop
    have checked : (instrs (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)] : Prog isa)).all
        (fun op => !(clobbers op r)) = true := by
      cases r <;> try rfl
      all_goals exact False.elim (hr (by decide))
    have h := List.all_eq_true.mp checked op hop
    cases hc : clobbers op r <;> simp_all) (by rfl)
  ffrun [BitVec.add_zero, read, saved, zero]

theorem residue_ok {s : State} {dst : BitVec 32} {n generator : Nat}
    (h : ReadContext dst n s) (allowed : generator = 2 ∨ generator = 5)
    (saved : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 generator)
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s fun t =>
      t.z = (if generator = 2 then
        decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 24 = 11) else
        decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 3 ∨
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 10 = 7)) ∧
      t.mem = s.mem ∧ Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.residue
  refine WP.seq (WP.mono (residueHead_ok h (by rcases allowed with rfl | rfl <;> decide) saved) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  by_cases two : generator = 2
  · refine WP.ite true (by change some u.z = some true; rw [flag, decide_eq_true two]) ?_ (by intro h; cases h)
    intro _
    refine WP.mono (residue2_ok (h.after_memory memory rest)) ?_
    rintro t ⟨flagT, memoryT, restT⟩
    refine ⟨?_, memoryT.trans memory, (rest.mono (by simp)).trans restT⟩
    simpa only [memory, ite_eq_left two] using flagT
  · refine WP.ite false (by change some u.z = some false; rw [flag, decide_eq_false two]) (by intro h; cases h) ?_
    intro _
    refine WP.mono (residue5_ok (h.after_memory memory rest) (by simpa only [memory] using odd)) ?_
    rintro t ⟨flagT, memoryT, restT⟩
    refine ⟨?_, memoryT.trans memory, (rest.mono (by simp)).trans restT⟩
    simpa only [memory, ite_eq_right two] using flagT

end VG.Proof.Ffdh.Arm.ParameterCandidate
