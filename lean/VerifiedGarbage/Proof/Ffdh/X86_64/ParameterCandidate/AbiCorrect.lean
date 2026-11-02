module

public import VerifiedGarbage.Impl.Ffdh.X86_64.ParameterCandidate.Core
public import VerifiedGarbage.Proof.Bignum.X86_64.R2Impl
public import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Contract
public import VerifiedGarbage.Proof.MillerRabin.X86_64.Kernel

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Context
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Data
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Body
import VerifiedGarbage.Proof.Ffdh.X86_64.ParameterCandidate.Finish
import VerifiedGarbage.Proof.Rsa.Octets
import VerifiedGarbage.Proof.Bignum.Octets
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.NeZero
public import VerifiedGarbage.Proof.Ffdh.Contract
/-! # FFDH parameter generation on x86-64: preserve the complete System V ABI -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/X86_64/ParameterCandidate/Correct.lean`, which only this module imported.
section

/-! # FFDH parameter generation on x86-64: functional correctness of the callable -/

section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Ffdh.X86_64.ParameterCandidate
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64
open VG.Proof.MillerRabin.X86_64

def FinalResult (p : CandidateP) (t : State) : Prop :=
  let r := Spec.Ffdh.parameterCandidate p.bits p.gen p.rand
  ((t.gpr .rax).setWidth 32).toNat = Proof.Ffdh.candidateStatus r ∧
    Spec.Rsa.bytesAt t.mem p.op p.k =
      (match r with | some (some n, _) => Spec.Rsa.i2osp n p.k | _ => List.replicate p.k 0) ∧
    word t.mem p.up 0 = BitVec.ofNat 64
      (match r with | some (_, rest) => p.rand.length - rest.length | none => 0)

private theorem finish_result {p : CandidateP} {used : Nat} {s t : State}
    (hbound : used ≤ p.rand.length) (hr : NativeResult p used s.mem)
    (hout : word s.mem p.B (8 * oStatus) = 1 → Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem p.op p.k) = p.P)
    (hax : t.gpr .rax = BitVec.ofNat 64 (Proof.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand)))
    (hused : word t.mem p.up 0 = BitVec.ofNat 64
      (if Proof.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) = 0 then 0 else used))
    (hbytes : Spec.Rsa.bytesAt t.mem p.op p.k =
      (if Proof.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) = 1 then
        Spec.Rsa.bytesAt s.mem p.op p.k else List.replicate p.k 0)) : FinalResult p t := by
  unfold FinalResult
  cases he : Spec.Ffdh.parameterCandidate p.bits p.gen p.rand with
  | none => simpa [he, Proof.Ffdh.candidateStatus, hax] using And.intro hbytes hused
  | some ar =>
    obtain ⟨value, rest⟩ := ar
    have hrest : rest = p.rand.drop used := by simpa only [NativeResult, he] using hr.2.1
    have hcount : p.rand.length - rest.length = used := by
      rw [hrest, List.length_drop]
      omega
    cases value with
    | none =>
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Proof.Ffdh.candidateStatus]
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false] using hbytes
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused
    | some n =>
      have hn : n = p.P := hr.2.2 n rest he
      have hstatus : word s.mem p.B (8 * oStatus) = BitVec.ofNat 64 1 := by
        simpa only [he, Proof.Ffdh.candidateStatus] using hr.1
      have hval := hout hstatus
      have hi := VG.Proof.Rsa.i2osp_os2ip (Spec.Rsa.bytesAt s.mem p.op p.k)
      rw [bytesAt_length, hval, ← hn] at hi
      refine ⟨?_, ?_, ?_⟩
      · simp [hax, he, Proof.Ffdh.candidateStatus]
      · simpa only [he, Proof.Ffdh.candidateStatus, ite_true, hi] using hbytes
      · simpa only [he, Proof.Ffdh.candidateStatus, Nat.reduceEqDiff, ite_false, hcount] using hused

theorem correct_ok (M : Mont) (R : R2Impl M) (K : Kernel) {s : State} (c : PcCtx s) :
    WP isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s fun t => pcPost s t ∧
      (∀ r ∈ saved, t.gpr r = s.gpr r) ∧ Keep (.rdi :: mmRegs) s t := by
  unfold VG.Impl.Ffdh.X86_64.ParameterCandidate.code
  refine WP.seq (WP.mono (body_ok M R K c) fun u ⟨used, hu, hdu, hr, hout, hsaved, ku⟩ => ?_)
  let p := candidateOfState s
  have hsmall : Proof.Ffdh.candidateStatus (Spec.Ffdh.parameterCandidate p.bits p.gen p.rand) < 2 ^ 64 := by
    cases Spec.Ffdh.parameterCandidate p.bits p.gen p.rand with
    | none => decide
    | some ar => obtain ⟨value, rest⟩ := ar; cases value <;> dsimp only [Proof.Ffdh.candidateStatus] <;> decide
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
end

end

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.ParameterCandidate

open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Bignum.X86_64 (saved)
open VG.Proof.MlKem.X86_64 VG.Proof.MillerRabin.X86_64

private theorem ret_frame {c : Prog isa} {s t : State} {tr : List Leak}
    (h : pcPre s) (hs : SpSafe c) (hd : c.x86_64Depth ≤ 128) (he : Exec isa c s tr t) :
    t.mem.readW (s.gpr .rsp) 64 = s.mem.readW (s.gpr .rsp) 64 := by
  obtain ⟨_, _, _, hwr, _, _, _, _, _, _, _, _, _, hro, hru, _, hrs, _⟩ := h
  have hf := Exec.stackFrame hs he (by omega_using [hd])
  refine hf.readW (r := ⟨s.gpr .rsp, 8⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rcases List.mem_append.mp hr with hr | hr
  · rw [hwr] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    exacts [hro, hru, hrs]
  · simp only [List.mem_singleton] at hr; subst r
    exact Offset.base_disjoint_below _ (by omega_using [hd])

theorem pc_correct (M : Mont) (R : R2Impl M) (K : Kernel)
    (hs : SpSafe (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run))
    (hd : (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run).x86_64Depth ≤ 128)
    (hmx : (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run).allInstrs (fun i => !loadsMxcsr i) = true)
    (s : State) (h : pcContract.pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.X86_64.ParameterCandidate.code M.mm R.code K.run) s tr t ∧
      abiPreserved s t ∧ pcContract.post s t := by
  obtain ⟨tr, t, he, hp, hregs, k⟩ := correct_ok M R K (pcCtx_of h)
  have hg : gprPreserved s t := by
    refine ⟨?_, ret_frame h hs hd he⟩
    intro r hr
    simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact k.gpr (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
    · exact hregs _ (by decide)
  exact ⟨tr, t, he, abiPreserved_of_exec hmx he hg, hp⟩

end VG.Proof.Ffdh.X86_64.ParameterCandidate
