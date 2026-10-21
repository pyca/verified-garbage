module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveEntry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialSmall
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! One compact-table sieve iteration uses RSA's verified native reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem sieveActiveStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : SieveInv s0 dst base n value i s) (more : i < 53) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieveActiveStep s fun t =>
      SieveInv s0 dst base n value (i + 1) t ∧ t.z = decide (i + 1 = 53) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveActiveStep VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (sieveEntry_ok inv.context more inv.cursor) ?_)
  rintro u ⟨⟨prime, cursor, memU⟩, restU⟩
  have ctxU := inv.context.after_memory memU restU
  refine WP.seq (WP.mono (trialSmall_ok u dst ctxU.read.positive ctxU.read.countFits ctxU.read.bufferFits
    (by omega : i < 1024) prime (ctxU.read.frame.read (by decide)) (ctxU.read.frame.read (by decide))
    ctxU.read.out ctxU.read.width ctxU.read.readable) ?_)
  rintro v ⟨flag, memV, restV⟩
  have ctxV := ctxU.after_memory memV restV
  have old : v.mem.readW (State.addr (v.sp + 64#32)) 32 = if sieveAny value i then 1 else 0 := by
    rw [memV, restV.sp, memU, restU.sp]
    exact inv.bad
  have divides : v.z = (value % VG.Impl.RsaKeyGen.tabEntry i == 0) := by
    rw [memU, inv.candidate] at flag
    rwa [← Bool.beq_eq_decide_eq] at flag
  refine WP.seq (WP.mono (sieveFlag_ok ctxV.read.frame.space old) ?_)
  rintro a ⟨badA, changedA, restA⟩
  have ctxA := ctxV.after_frame changedA restA
  have through : Rest sieveRegs s a :=
    ((restU.mono (by simp [sieveRegs])).trans (restV.mono (by simp [sieveRegs]))).trans (restA.mono (by simp [sieveRegs]))
  have countA : a.gpr .r11 = BitVec.ofNat 32 (53 - i) := by
    rw [restA.gpr .r11 (by simp), restV.gpr .r11 (by simp), restU.gpr .r11 (by simp)]
    exact inv.count
  refine WP.seq (WP.mono (sieveCount_ok (by omega : 0 < 53 - i) (by omega) countA) ?_)
  rintro t ⟨⟨countT, zeroT, memT⟩, restT⟩
  refine WP.block_nil ⟨⟨ctxA.after_memory memT restT, by omega, ?_, ?_, ?_, ?_, ?_,
    (inv.rest.trans through).trans (restT.mono (by simp [sieveRegs]))⟩, ?_⟩
  · rw [restT.gpr .r10 (by simp), restA.gpr .r10 (by simp), restV.gpr .r10 (by simp)]
    exact cursor
  · simpa only [show 53 - i - 1 = 53 - (i + 1) by omega] using countT
  · rw [divides, ← sieveAny_succ] at badA
    rw [memT, restT.sp]
    exact badA
  · rw [memT, ctxV.bytes_after changedA, memV, memU]
    exact inv.candidate
  · have changed : Frame [sieveLocal s0.sp] s.mem t.mem := by
      rw [memT]
      simpa only [restV.sp, restU.sp, inv.rest.sp, memV, memU] using changedA
    exact inv.changed.trans changed
  · rw [zeroT]
    exact decide_eq_decide.mpr (by omega)

theorem sieveStep_ok {s0 s : State} {dst base : BitVec 32} {n value i : Nat}
    (inv : SieveInv s0 dst base n value i s) (more : i < 53) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep s fun t =>
      SieveInv s0 dst base n value (i + 1) t ∧ t.z = decide (i + 1 = 53) := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep
  refine WP.seq (WP.mono (sieveFinish_ok inv.context.read.frame.space inv.bad) ?_)
  rintro u ⟨⟨flag, memory⟩, rest⟩
  have invU : SieveInv s0 dst base n value i u := by
    refine ⟨inv.context.after_memory memory rest, inv.index, ?_, ?_, ?_, ?_, ?_,
      inv.rest.trans (rest.mono (by simp [sieveRegs]))⟩
    · rw [rest.gpr .r10 (by simp)]; exact inv.cursor
    · rw [rest.gpr .r11 (by simp)]; exact inv.count
    · rw [memory, rest.sp]; exact inv.bad
    · rw [memory]; exact inv.candidate
    · rw [memory]; exact inv.changed
  cases bad : sieveAny value i with
  | false =>
    have zero : u.z = true := by simpa only [bad, Bool.not_false] using flag
    refine WP.ite true (by change some u.z = some true; rw [zero]) ?_ (by intro h; cases h)
    intro _
    exact sieveActiveStep_ok invU more
  | true =>
    have zero : u.z = false := by simpa only [bad, Bool.not_true] using flag
    refine WP.ite false (by change some u.z = some false; rw [zero]) (by intro h; cases h) ?_
    intro _
    refine WP.mono (sieveSkip_ok (by omega : 0 < 53 - i) (by omega) invU.count) ?_
    rintro t ⟨⟨cursor, count, last, mem⟩, restT⟩
    refine ⟨⟨invU.context.after_memory mem restT, by omega, ?_, ?_, ?_, ?_, ?_,
      invU.rest.trans (restT.mono (by simp [sieveRegs]))⟩, ?_⟩
    · rw [cursor, invU.cursor]
      change (base + BitVec.ofNat 32 (Spec.Rsa.Mont.arrAt ((n + 7) / 8) 34 + 4 * i)) + BitVec.ofNat 32 4 = _
      rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      have offset : Spec.Rsa.Mont.arrAt ((n + 7) / 8) 34 + 4 * i + 4 =
          Spec.Rsa.Mont.arrAt ((n + 7) / 8) 34 + 4 * (i + 1) := by omega
      rw [offset]
    · simpa only [show 53 - i - 1 = 53 - (i + 1) by omega] using count
    · rw [mem, restT.sp, invU.bad, sieveAny_succ, bad]
      rfl
    · rw [mem]; exact invU.candidate
    · rw [mem]; exact invU.changed
    · rw [last]
      exact decide_eq_decide.mpr (by omega)

end VG.Proof.Ffdh.Arm.ParameterCandidate
