module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCorePair
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyRetryFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeySmall
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyCrtTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDSelectTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTiming
import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyIO
/-! # Completed numeric key derivation retains the public output environment and a boolean validity mask -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyRetryTiming.lean`, which only this module imported.
section

/-! # The native retry branch is public through the shared released result -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

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
    RelCT isa (ReadyPair B Z n e p q p' q') (smallMask n) (RetryTest B Z n e p q p' q') := by
  intro s t tr ur u v P A C
  obtain ⟨trace, agree⟩ := key_public_trace (smallMask_public n) _ _ _ _ _ _ P.agree A C
  obtain ⟨leftWs, leftFrame, leftFlag, _⟩ := wp_result (smallMask_ok P.left P.leftReady.bit) A
  obtain ⟨rightWs, rightFrame, rightFlag, _⟩ := wp_result (smallMask_ok P.right P.rightReady.bit) C
  have leftEval := retry_eval leftFlag
  have rightEval := retry_eval rightFlag
  refine ⟨trace, ⟨leftWs, rightWs, agree, P.leftReady.small P.left leftFrame,
    P.rightReady.small P.right rightFrame⟩, ?_⟩
  rw [leftEval, rightEval]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact P.leftReady.retry_iff.trans (release.trans P.rightReady.retry_iff.symm)

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyFinalTiming.lean`, which only this module imported.
section

/-! # Final validity checks never branch on secret key values -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem andFlag_public : KeyPublic andFlag :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem withFlag_public {c : Prog isa} (H : KeyPublic c) : KeyPublic (withFlag c) :=
  H.seq andFlag_public

theorem topBit_public (n : Nat) : KeyPublic (.block (topBit n)) := by
  refine ⟨.block [], workspaceTaint true, ?_, rfl⟩
  change taint.checkBlock (workspaceTaint true) (topBit n) = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .shift .shr .eax 31,
      .store (VG.Impl.Mont.X86.sc 0) .eax] = _
  rfl

theorem exponentUpper_public : KeyPublic (.block exponentUpper) :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem exponentAtLeastThree_public (n : Nat) : KeyPublic (exponentAtLeastThree n) := by
  refine (constArray_public ..).seq ((sub3_public ..).seq (KeyPublic.seq ?_ ?_))
  all_goals exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem finalMask_public (n : Nat) : KeyPublic (finalMask n) := by
  unfold finalMask
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact withFlag_public (topBit_public _)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public exponentUpper_public
  · exact exponentAtLeastThree_public _

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyPartTiming.lean`, which only this module imported.
section

/-! # The complete post-retry arithmetic has a fixed native schedule -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem keyPart_public (n : Nat) : KeyPublic (keyPart n) := by
  unfold keyPart
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · exact qinvPart_public _
  · exact crtPart_public _
  · exact nPart_public _
  · exact finalMask_public _
  · exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem retry_public : KeyPublic retry :=
  ⟨.block [], zeroTaint true, rfl, rfl⟩

end VG.Proof.RsaKeyGen.X86.Key
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyDeriveTiming.lean`, which only this module imported.
section

/-! # Complete native numeric key derivation is constant time modulo the released retry status -/

section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem deriveLoaded_trace (B : Addr) (Z n k e p q p' q' : Nat)
    (width : n = 2 * k) (positive : 0 < k) (even : k % 2 = 0)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * n) e p' q' = .inr ())) :
    RelCT isa (fun s t => CoreStart B Z n k e p q s ∧ CoreStart B Z n k e p' q' t ∧
      VG.X86.Taint.Agree (workspaceTaint true) s t)
      (deriveLoaded n) (VG.X86.Taint.Agree (workspaceTaint true)) := by
  unfold deriveLoaded
  apply RelCT.seq (prepareReady_trace B Z n k e p q p' q' width positive even)
  apply RelCT.seq (smallMask_trace B Z n e p q p' q' release)
  apply RelCT.ite (fun _ _ P => P.2)
  · exact (key_public_trace retry_public).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)
  · exact (key_public_trace (keyPart_public n)).mono (fun _ _ P => P.1.1.agree) (fun _ _ P => P)

end VG.Proof.RsaKeyGen.X86.Key
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Proof.Mont.X86.Dynamic VG.Proof.Dsa.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem core_mask_bit {B : Addr} {n e p q : Nat} {m : Mem} (R : CoreOutcome B n e p q m) :
    slot m B kOk ≤ 1 := by
  unfold CoreOutcome at R
  split at R <;> omega

theorem deriveOutput_ok {E : Environment} {s : State} {e p q : Nat} (h : Input E s)
    (C : CoreStart E.base E.size E.n E.k e p q s) :
    WP isa (deriveLoaded E.n) s fun t =>
      Input E t ∧ slot t.mem E.base kOk ≤ 1 ∧ Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t := by
  have widths := h.valid.widths
  refine WP.mono (deriveLoaded_ok h.ws widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 widths.1 widths.2.1
    C.pBound C.qBound C.zero C.one (C.loaded.trans C.exponent.symm))
    fun t ⟨ht, O, result, K⟩ => ?_
  exact ⟨h.afterStage ht K O, core_mask_bit result, K⟩

theorem deriveOutput_trace (E : Environment) (e p q p' q' : Nat)
    (release : (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p q = .inr ()) ↔
      (Spec.RsaKeyGen.keyFromPrimes (32 * E.n) e p' q' = .inr ())) :
    RelCT isa (ImportedPair E e p q p' q') (deriveLoaded E.n) (OutputPair E) := by
  intro s t tr ur u v P A C
  have widths := P.inputs.left.valid.widths
  obtain ⟨trace, agree⟩ := deriveLoaded_trace E.base E.size E.n E.k e p q p' q'
    widths.2.2.1 widths.2.2.2.1 widths.2.2.2.2.1 release _ _ _ _ _ _ ⟨P.left, P.right, P.agree⟩ A C
  obtain ⟨leftInput, leftBit, leftKeeps⟩ := wp_result (deriveOutput_ok P.inputs.left P.left) A
  obtain ⟨rightInput, rightBit, rightKeeps⟩ := wp_result (deriveOutput_ok P.inputs.right P.right) C
  refine ⟨trace, ⟨leftInput, rightInput, ?_⟩, agree, leftBit, rightBit⟩
  rw [leftKeeps.1 .esp (by decide), rightKeeps.1 .esp (by decide)]
  exact P.inputs.stack

end VG.Proof.RsaKeyGen.X86.Key
