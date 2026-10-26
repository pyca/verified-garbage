module
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Finish
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
import Mathlib.Data.Nat.GCD.Basic

/-! # FFDH parameter generation on x86-64: functional correctness of the callable -/

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def FinalResult (p : CandidateP) (t : State) : Prop :=
  let r := Spec.Ffdh.parameterCandidate p.bits p.gen p.rand
  ((t.gpr .rax).setWidth 32).toNat = Spec.Ffdh.candidateStatus r ∧
    Spec.Rsa.bytesAt t.mem p.op p.k =
      (match r with | some (some n, _) => Spec.Rsa.i2osp n p.k | _ => List.replicate p.k 0) ∧
    word t.mem p.up 0 = BitVec.ofNat 64
      (match r with | some (_, rest) => p.rand.length - rest.length | none => 0)

private theorem finish_result {p : CandidateP} {used : Nat} {s t : State}
    (hbound : used ≤ p.rand.length) (hr : NativeResult p used s.mem)
    (hout : word s.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P)
    (hax : t.gpr .rax = BitVec.ofNat 64 (Spec.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand)))
    (hused : word t.mem p.up 0 = BitVec.ofNat 64
      (if Spec.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) = 0 then 0 else used))
    (hbytes : Spec.Rsa.bytesAt t.mem p.op p.k =
      (if Spec.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) = 1 then
        Spec.Rsa.bytesAt s.mem p.op p.k else List.replicate p.k 0)) : FinalResult p t := by
  unfold FinalResult
  cases he : Spec.Ffdh.parameterCandidate p.bits p.gen p.rand with
  | none => simpa [he, Spec.Ffdh.candidateStatus, hax] using And.intro hbytes hused
  | some ar =>
    obtain ⟨value, rest⟩ := ar
    have hrest : rest = p.rand.drop used := by simpa only [NativeResult, he] using hr.2.1
    have hcount : p.rand.length - rest.length = used := by
      rw [hrest, List.length_drop]
      omega
    cases value with
    | none =>
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Spec.Ffdh.candidateStatus]
      · simpa only [he, Spec.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false] using hbytes
      · simpa only [he, Spec.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused
    | some n =>
      have hn : n = p.P := hr.2.2 n rest he
      have hstatus : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 1 := by
        simpa only [he, Spec.Ffdh.candidateStatus] using hr.1
      have hval := hout hstatus
      have hi := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem p.op p.k)
      rw [bytesAt_length, hval, ← hn] at hi
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Spec.Ffdh.candidateStatus]
      · simpa only [he, Spec.Ffdh.candidateStatus, ite_true, hi] using hbytes
      · simpa only [he, Spec.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused

theorem correct_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s fun t => pcPost s t ∧
      (∀ r ∈ saved, t.gpr r = s.gpr r) ∧ Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.ParameterCandidate.code
  refine WP.seq (WP.mono (body_ok M R K c) fun u ⟨used, hu, hdu, hr, hout, hsaved, ku⟩ => ?_)
  let p := candidateOfState s
  have hsmall : Spec.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) < 2 ^ 64 := by
    cases Spec.Ffdh.parameterCandidate p.bits p.gen p.rand with
    | none => decide
    | some ar => obtain ⟨value, rest⟩ := ar; cases value <;> dsimp only [Spec.Ffdh.candidateStatus] <;> decide
  refine WP.mono (finish_ok hu hdu hr.1 hsmall hsaved)
    fun t ⟨hax, hused, hbytes, hregs, kt⟩ => ?_
  have hfinal := finish_result hu.bound hr hout hax hused hbytes
  refine ⟨?_, hregs, (ku.trans kt).mono (by decide)⟩
  change pcPost s t
  unfold pcPost
  refine ⟨hfinal.1, hfinal.2.1, ?_⟩
  have hw := hfinal.2.2
  change VG.Proof.Bignum.word t.mem (s.gpr .rdx) 0 = BitVec.ofNat 64
    (match pcResult s with | some (_, rest) => (pcRand s).length - rest.length | none => 0) at hw
  have hlen : (pcRand s).length = (stackArg s 0).toNat := bytesAt_length _ _ _
  rw [hlen] at hw
  change [VG.Proof.Bignum.word t.mem (s.gpr .rdx) 0] = _
  exact congrArg (fun x : BitVec 64 => [x]) hw

end VG.Proof.Ffdh.X86_64.ParameterCandidate
