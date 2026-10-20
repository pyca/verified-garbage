module
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Entry
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MillerRabin.X86_64.CallerStages

/-! # FFDH parameter generation on x86-64: initialize the retained input state -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64
open VG.Impl.Bignum.X86_64 (saved)
open VG.Impl.Ffdh.X86_64.ParameterCandidate VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64 VG.Proof.Ffdh.X86_64

def candidateOfState (s : State) : CandidateP :=
  ⟨stackArg s 1, (stackArg s 2).toNat * 8, (s.gpr .rsi).toNat, (s.gpr .rcx).toNat,
    ((s.gpr .r8).setWidth 32).toNat, s.gpr .rdi, s.gpr .rdx, s.gpr .r9, pcRand s, s.gpr .rsp⟩

theorem candidateEntry_base {s : State} (c : PcCtx s) :
    WP isa (.block VG.Impl.Ffdh.X86_64.ParameterCandidate.entry) s fun t =>
      CandidateTape (candidateOfState s) 0 t ∧ t.gpr .rdi = (candidateOfState s).B ∧
      word t.mem (candidateOfState s).B (8 * oStatus) = 0 ∧
      InScr (candidateOfState s).B (candidateOfState s).Z s.mem t.mem ∧
      (∀ i < 6, word t.mem (candidateOfState s).B (8 * i) = s.gpr (saved.getD i .rax)) ∧
      Keep (.rdi :: mmRegs) s t := by
  refine WP.mono (candidateEntry_ok rfl (fun i hi => c.scr.st (by omega_using [hi, c.room])) c.args)
    fun t ⟨hd, hsaved, hh, hptr, hleft, hused, hstatus, hf, k⟩ => ?_
  have hframe : InScr (candidateOfState s).B (candidateOfState s).Z s.mem t.mem :=
    InScr.of_outside hf (by dsimp only [candidateOfState]; omega_using [c.room])
  have hsp : t.gpr .rsp = (candidateOfState s).sp := k.gpr (by decide)
  have hbase : CandidateBase (candidateOfState s) t := by
    refine ⟨c.bits1, c.bits2, c.len, c.gen, ?_, c.room, c.scr.congr k.2.2,
      ⟨fun i hi => by rw [k.2.2]; exact c.out.wr i hi, c.out.sep⟩, c.usedMem.congr k.2.2,
      ⟨fun i hi => by rw [k.2.2]; exact c.used.wr i hi, c.used.sep⟩,
      c.rand.congrK hframe k, ?_, c.outUsed, hsp, c.stackSize, c.stackScr.symm, ?_, ?_⟩
    · change (pcRand s).length < 2 ^ 64
      rw [bytesAt_length]
      exact (stackArg s 0).isLt
    · change Apart (s.gpr .rdi) (s.gpr .rsi).toNat (s.gpr .r9) (pcRand s).length
      rw [bytesAt_length]
      exact c.outRand
    · intro i hi
      change i < (pcRand s).length at hi
      apply c.stackRand.symm
      have hlen : (pcRand s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
      exact Offset.contains_base _ (by omega_using [hi, hlen]) (by omega_using [hi, hlen, (stackArg s 0).isLt])
    · have hg : BitVec.ofNat 64 ((s.gpr .r8).setWidth 32).toNat = ((s.gpr .r8).setWidth 32).setWidth 64 := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
      simpa only [CandidateP.headers, candidateOfState, BitVec.ofNat_toNat, BitVec.setWidth_eq, hg] using hh
  refine ⟨⟨hbase, by omega, ?_, ?_, hused⟩, hd, hstatus, hframe, hsaved, k.mono (by decide)⟩
  · simpa only [candidateOfState, off, BitVec.ofNat_toNat, BitVec.add_zero] using hptr
  · simpa only [candidateOfState, bytesAt_length, Nat.sub_zero, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hleft

end VG.Proof.Ffdh.X86_64.ParameterCandidate
