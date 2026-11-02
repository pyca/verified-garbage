module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrials
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairMath
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
import VerifiedGarbage.Proof.Ffdh.Arm.Block
import VerifiedGarbage.Proof.X25519.Arm.Instr
/-! One compact-table sieve iteration uses RSA's verified native reducer. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PairControl.lean`, which only this module imported.
section

/-! Advance the shared prime cursor and bounded count once for each pair of trials. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem pairAdvanceCount_ok {s : State} {count : Nat} (positive : 0 < count) (bound : count ≤ 1024)
    (saved : s.gpr .r11 = BitVec.ofNat 32 count) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount)) s fun t =>
      (t.gpr .r10 = s.gpr .r10 + 4 ∧ t.gpr .r11 = BitVec.ofNat 32 (count - 1) ∧
        t.z = decide (count = 1) ∧ t.mem = s.mem) ∧ Rest [.r10, .r11] s t := by
  have subtract : BitVec.ofNat 32 count - (1 : BitVec 32) = BitVec.ofNat 32 (count - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  have zero : (BitVec.ofNat 32 (count - 1) == (0 : BitVec 32)) = decide (count = 1) := by
    rw [ofNat_beq_zero (by omega : count - 1 < 2 ^ 32)]
    exact decide_eq_decide.mpr (by omega)
  refine withRest_all [.r10, .r11] ?_ (by rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount
  ffrun [List.cons_append, List.nil_append, saved, subtract, zero]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem pairActiveStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : PairInv s0 dst base n value i s) (more : i < (trialCount n)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep s fun t =>
      PairInv s0 dst base n value (i + 1) t ∧ t.z = decide (i + 1 = (trialCount n)) := by
  have limitBound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (pairTrials_ok inv.context more inv.cursor inv.candidate) ?_)
  rintro v ⟨divides,memV,restV⟩
  have ctxV := inv.context.after_memory memV restV
  have old : v.mem.readW (State.addr (v.sp+64#32)) 32 = if pairAny value i then 1 else 0 := by
    rw [memV,restV.sp]
    exact inv.bad
  refine WP.seq (WP.mono (sieveFlag_ok ctxV.read.frame.space old) ?_)
  rintro a ⟨badA,changedA,restA⟩
  have ctxA := ctxV.after_frame changedA restA
  have through : Rest sieveRegs s a :=
    (restV.mono (by simp [sieveRegs])).trans (restA.mono (by simp [sieveRegs]))
  have countA : a.gpr .r11=BitVec.ofNat 32 (trialCount n-i) := by
    rw [restA.gpr .r11 (by simp),restV.gpr .r11 (by simp)]
    exact inv.count
  refine WP.seq (WP.mono (pairAdvanceCount_ok (by omega : 0<trialCount n-i) (by omega) countA) ?_)
  rintro t ⟨⟨cursorT,countT,zeroT,memT⟩,restT⟩
  refine WP.block_nil ⟨⟨ctxA.after_memory memT restT,by omega,?_,?_,?_,?_,?_,
    (inv.rest.trans through).trans (restT.mono (by simp [sieveRegs]))⟩,?_⟩
  · rw [cursorT,restA.gpr .r10 (by simp),restV.gpr .r10 (by simp),inv.cursor]
    change (base+BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i))+BitVec.ofNat 32 4 = _
    rw [BitVec.add_assoc,BitVec.ofNat_add_ofNat]
    have offset : Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i+4 =
        Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*(i+1) := by omega
    rw [offset]
  · simpa only [show trialCount n-i-1=trialCount n-(i+1) by omega] using countT
  · rw [divides,←pairAny_succ] at badA
    rw [memT,restT.sp]
    exact badA
  · rw [memT,ctxV.bytes_after changedA,memV]
    exact inv.candidate
  · have changed : Frame [sieveLocal s0.sp] s.mem t.mem := by
      rw [memT]
      simpa only [restV.sp,inv.rest.sp,memV] using changedA
    exact inv.changed.trans changed
  · rw [zeroT]
    exact decide_eq_decide.mpr (by omega)

theorem pairStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : PairInv s0 dst base n value i s) (more : i < (trialCount n)) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep s fun t =>
      PairInv s0 dst base n value (pairNext n value i) t ∧ t.z = decide (pairNext n value i = trialCount n) := by
  have limitBound := trialCount_bound n
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
  refine WP.seq (WP.mono (sieveFinish_ok inv.context.read.frame.space inv.bad) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  have invU : PairInv s0 dst base n value i u := by
    refine ⟨inv.context.after_memory memory rest, inv.index, ?_, ?_, ?_, ?_, ?_,
      inv.rest.trans (rest.mono (by simp [sieveRegs]))⟩
    · rw [rest.gpr .r10 (by simp)]; exact inv.cursor
    · rw [rest.gpr .r11 (by simp)]; exact inv.count
    · rw [memory, rest.sp]; exact inv.bad
    · rw [memory]; exact inv.candidate
    · rw [memory]; exact inv.changed
  cases bad : pairAny value i with
  | false =>
    have zero : u.z = true := by simpa only [bad, Bool.not_false] using flag
    refine WP.ite true (by change some u.z = some true; rw [zero]) ?_ (by intro h; cases h)
    intro _
    simpa only [pairNext, bad, Bool.false_eq_true, ite_false] using pairActiveStep_ok invU more
  | true =>
    have zero : u.z = false := by simpa only [bad, Bool.not_true] using flag
    refine WP.ite false (by change some u.z = some false; rw [zero]) (by intro h; cases h) ?_
    intro _
    refine WP.mono (sieveSkip_ok u) ?_
    rintro t ⟨⟨cursor, count, last, mem⟩, restT⟩
    simp only [pairNext, bad, ite_true, decide_true]
    have totalBad := pairAny_mono inv.index bad
    refine ⟨⟨invU.context.after_memory mem restT, Nat.le_refl _, ?_, ?_, ?_, ?_, ?_,
      invU.rest.trans (restT.mono (by simp [sieveRegs]))⟩, last⟩
    · rw [cursor, invU.cursor, invU.count, BitVec.shiftLeft_eq_mul_twoPow]
      change (base + BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i)) +
        BitVec.ofNat 32 (trialCount n-i)*BitVec.ofNat 32 4 = _
      rw [BitVec.ofNat_mul_ofNat,BitVec.add_assoc,BitVec.ofNat_add_ofNat]
      have offset : Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*i+(trialCount n-i)*4 =
          Proof.Rsa.Mont.arrAt ((n+7)/8) 34+4*trialCount n := by
        have := inv.index
        omega
      rw [offset]
    · rw [Nat.sub_self]
      exact count.trans (by decide)
    · rw [mem, restT.sp, invU.bad, bad, totalBad]
    · rw [mem]; exact invU.candidate
    · rw [mem]; exact invU.changed

end VG.Proof.Ffdh.Arm.ParameterCandidate
