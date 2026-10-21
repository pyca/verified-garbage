module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.CorePair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetryFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallMask
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.SmallPublic
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRuntime.DSelectTiming

/-! # The native retry branch is public through the shared released result -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.KeyRuntime
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key (aPa aQa aD aE kEv kOk)
open VG.Impl.RsaKeyGen.X86.KeyRuntime
open VG.Proof.RsaKeyGen.X86.Key (KeyReady)

def RetryTest (B : Addr) (Z n e p q p' q' : Nat) (s t : State) : Prop :=
  ReadyPair B Z n e p q p' q' s t ∧ isa.eval .ne s = isa.eval .ne t

theorem retry_eval {B : Addr} {n : Nat} {m : Mem} {s : State}
    (flag : s.zf = some (decide (¬(slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))))) :
    isa.eval .ne s = some (decide (slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n))) := by
  change s.zf.map Bool.not = _
  rw [flag]
  by_cases small : slot m B kOk = 1 ∧ num m B n aD ≤ 2 ^ (16 * n) <;> simp [small]

theorem smallMask_trace (B : Addr) (Z n e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (ReadyPair B Z n e p q p' q') smallMask (RetryTest B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := public_trace smallMask_public _ _ _ _ _ _ P.agree A C
  obtain ⟨leftWs, leftFrame, leftFlag, _⟩ := wp_result (smallMask_ok P.left P.leftReady.bit) A
  obtain ⟨rightWs, rightFrame, rightFlag, _⟩ := wp_result (smallMask_ok P.right P.rightReady.bit) C
  have leftEval := retry_eval leftFlag
  have rightEval := retry_eval rightFlag
  refine ⟨trace, ⟨leftWs, rightWs, agree, P.leftReady.small P.left.old leftFrame,
    P.rightReady.small P.right.old rightFrame⟩, ?_⟩
  rw [leftEval, rightEval]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact P.leftReady.retry_iff.trans (release.trans P.rightReady.retry_iff.symm)

end VG.Proof.RsaKeyGen.X86.KeyRuntime
