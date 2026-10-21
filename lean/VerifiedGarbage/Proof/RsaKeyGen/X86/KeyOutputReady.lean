module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyImportedPair
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyWritePortTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDeriveTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyDerive
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyGeometry
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Completed numeric key derivation retains the public output environment and a boolean validity mask -/

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
