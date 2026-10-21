module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialValue
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialOctets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialFlag
import VerifiedGarbage.Proof.Framework.Omega

/-! Trial division of an entire FFDH candidate by one prime, using RSA's
verified native reducer and inverse computation. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm

private def trialRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7]

theorem trialSmall_value_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32)
    (primeBound : prime < 1024)
    (divisor : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : TrialReadable s (dst + BitVec.ofNat 32 n) n) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall s fun t =>
      ∃ next steps, next < 2 * VG.Impl.RsaKeyGen.tabEntry prime ∧ t.gpr .r2 = BitVec.ofNat 32 next ∧
        next * 2 ^ (16 * steps) % VG.Impl.RsaKeyGen.tabEntry prime =
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % VG.Impl.RsaKeyGen.tabEntry prime ∧
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) %
        VG.Impl.RsaKeyGen.tabEntry prime = 0) ∧ t.mem = s.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  have facts := VG.Proof.RsaKeyGen.tabEntry_facts primeBound
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (trialStart_ok s dst n readOut readWidth out width) ?_)
  rintro u ⟨⟨ptr, cnt, zero, div, inverse, mem⟩, rest⟩
  have readable : TrialReadable u (u.gpr .r0) n := by
    rw [ptr]
    intro i hi
    rw [rest.rd, rest.wr]
    exact read i hi
  have inv : (u.gpr .r4).toNat =
      (VG.Proof.RsaKeyGen.ninv (BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))).toNat := by
    rw [inverse, divisor]
  refine WP.seq (WP.mono (trialLoop_ok u positive fits cnt readable zero (div.trans divisor)
    facts.2 inv (VG.Proof.RsaKeyGen.ninv_tab primeBound)) ?_)
  rintro v ⟨next, steps, bound, value, congruence, _, memory, keep⟩
  have inputValue : trialValue u.mem (u.gpr .r0) n =
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) := by
    rw [mem, ptr, trialValue_octets, trialBytes_at _ _ fits bufferFits]
  rw [inputValue] at congruence
  have divides := trialDigit_divides facts.1 bound congruence
  have divV : v.gpr .r3 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime) :=
    (keep.gpr .r3 (by simp)).trans (div.trans divisor)
  have preserved : Rest trialRegs s v := (rest.mono (by simp [trialRegs])).trans (keep.mono (by simp [trialRegs]))
  refine WP.seq (WP.mono (trialFlag_ok v) ?_)
  rintro t ⟨flag, memT, restT⟩
  refine WP.block_nil ⟨next, steps, bound, (restT.gpr .r2 (by simp)).trans value, congruence,
    ?_, memT.trans (memory.trans mem), preserved.trans (restT.mono (by simp))⟩
  rw [flag, value, divV, ofNat_beq_zero (by omega : next < 2 ^ 32),
    ofNat_beq_eq (by omega : next < 2 ^ 32) (by omega : VG.Impl.RsaKeyGen.tabEntry prime < 2 ^ 32),
    ← Bool.decide_or]
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using divides.symm

theorem trialSmall_ok (s : State) (dst : BitVec 32) {n prime : Nat}
    (positive : 0 < n) (fits : n < 2 ^ 32) (bufferFits : dst.toNat + n ≤ 2 ^ 32)
    (primeBound : prime < 1024)
    (divisor : s.gpr .r7 = BitVec.ofNat 32 (VG.Impl.RsaKeyGen.tabEntry prime))
    (readOut : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 4)) 4)
    (readWidth : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 12)) 4)
    (out : s.mem.readW (State.addr (s.sp + 4)) 32 = dst)
    (width : s.mem.readW (State.addr (s.sp + 12)) 32 = BitVec.ofNat 32 n)
    (read : TrialReadable s (dst + BitVec.ofNat 32 n) n) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.trialSmall s fun t =>
      t.z = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) %
        VG.Impl.RsaKeyGen.tabEntry prime = 0) ∧ t.mem = s.mem ∧
        Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7] s t := by
  refine WP.mono (trialSmall_value_ok s dst positive fits bufferFits primeBound divisor
    readOut readWidth out width read) ?_
  rintro t ⟨_, _, _, _, _, flag, mem, rest⟩
  exact ⟨flag, mem, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
