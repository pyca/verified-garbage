module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateTestState
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate
import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateGuard
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchPrime
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots

/-! # The full-width guard and primality test implement one p-candidate decision -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem pCandidateTest_ok {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {value used : Nat}
    (R : SearchContext P W s) (bound : value < 256 ^ P.geometry.pLen) (odd : value % 2 = 1)
    (bytes : Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value)
    (usedValue : W 16 = BitVec.ofNat 32 used) (usedBound : used ≤ P.witnesses.bytes.length) :
    WP isa (pCandidateTest P.geometry.pLen) s fun t => ∃ result : PrimeStepResult,
      SearchContext P (frameUpdate (frameUpdate (frameUpdate W 22 (P.geometry.pointer p))
        16 (BitVec.ofNat 32 result.used)) 19 (BitVec.ofNat 32 result.status)) t ∧
      CandidateTestResult P value used result t ∧
      Frame (candidateTestWrites P.geometry) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have pw := P.geometry.width
  have room : p + P.geometry.pLen ≤ usedBytes P.geometry.pLen := by unfold p usedBytes domainCheck; omega
  unfold pCandidateTest
  refine WP.seq (WP.mono (pCandidateGuard_ok R bound bytes) fun a ⟨Ra, cf, Oa, Ka⟩ => ?_)
  by_cases small : value < 2 ^ (8 * P.geometry.pLen - 1)
  · refine WP.ite true (by simp [eval, cf, small]) (fun _ => ?_) (fun h => Bool.noConfusion h)
    refine WP.mono (searchStatus_ok Ra 3) fun t ⟨Rt, Ot, Kt⟩ => ?_
    refine ⟨⟨3, 0, used⟩, ?_, ?_, (Oa.mono (candidateTest_frame _)).trans (Ot.mono (candidateTest_frame _)),
      (Ka.mono (by decide)).trans (Kt.mono (by decide))⟩
    · dsimp only
      rw [frameUpdate_same (show frameUpdate W 22 (P.geometry.pointer p) 16 = BitVec.ofNat 32 used from usedValue)]
      exact Rt
    · exact ⟨Nat.le_refl _, usedBound, Or.inr (Or.inr rfl), by rw [ite_eq_left small]; exact ⟨rfl, rfl⟩,
        by intro impossible; change 3 = 1 at impossible; contradiction⟩
  · refine WP.ite false (by simp [eval, cf, small]) (fun h => Bool.noConfusion h) (fun _ => ?_)
    have upper : value < 2 ^ (8 * P.geometry.pLen) := by
      rw [Nat.pow_mul]
      exact bound
    let D : VG.Proof.Dsa.Generation.PDomain P.geometry.pLen value := ⟨pw, odd, by omega, upper⟩
    have lo : 4 ≤ P.geometry.pLen := by omega
    have hi : P.geometry.pLen ≤ 384 := by omega
    have words : P.geometry.pLen % 4 = 0 := by rcases pw with h | h | h <;> rw [h] <;> decide
    let C := P.geometry.prime P.witnesses P.geometry.pLen value lo hi words D.bits odd
    have va : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt a.mem (off P.geometry.base p) P.geometry.pLen) = value := by
      rw [drawFrame_bytes Oa (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact (P.geometry.frame_part room).symm)
        (by omega), bytes, VG.Proof.Dsa.decodeBE_encodeBE bound]
    have test := searchPrime_ok Ra (show frameUpdate W 22 (P.geometry.pointer p) 22 = P.geometry.pointer p from rfl)
      lo hi words D.bits odd room (by unfold p arithmetic; omega) va
      (show frameUpdate W 22 (P.geometry.pointer p) 16 = BitVec.ofNat 32 used from usedValue) usedBound
    refine WP.mono test fun t ⟨Rt, ready, Ot, Kt⟩ => ?_
    let result := primeDecision C a.mem used
    have bounds := primeDecision_bounds (G := C) (mem := a.mem) usedBound
    have spec := primeDecision_spec (G := C) a.mem used (by have := D.large; exact Nat.lt_trans (by decide) this) odd
    have tape : Spec.Rsa.bytesAt a.mem (C.tape.setWidth 64) C.tapeLen = P.witnesses.bytes := Ra.witnesses.value
    rw [tape] at spec
    exact ⟨result, Rt, ⟨bounds.1, bounds.2.1, bounds.2.2, by rw [ite_eq_right small]; exact spec,
      fun accepted => ⟨D, (ready accepted).prepared⟩⟩,
      (Oa.mono (candidateTest_frame _)).trans (Ot.sub (candidateTest_prime _ _ _ _ _ _ _ _ _)),
      (Ka.mono (by decide)).trans Kt⟩
end VG.Proof.Dsa.X86.Generation
