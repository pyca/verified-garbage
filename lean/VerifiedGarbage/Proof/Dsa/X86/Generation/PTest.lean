module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateWidth
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckCandidate
import VerifiedGarbage.Proof.Dsa.X86.Generation.SetWord
import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Framework.Offset

/-! Reject undersized candidates without drawing witnesses, then run the common primality routine. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.MillerRabin.X86

def pTestResult (bits p : Nat) (r : List Byte) : Option (Bool × List Byte) :=
  if p < 2 ^ (bits - 1) then some (false, r) else Spec.Dsa.probablePrime p r

theorem p_test (v : RoundImpl) {s : State} {base : Addr} {bytes n p : Nat} {r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes) (sizes : n = 16 ∨ n = 32 ∨ n = 48)
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (bound : p < 2 ^ (64 * n)) (odd : p % 2 = 1)
    (encoded : Spec.Rsa.bytesAt s.mem (off base Layout.p) (8 * n) = Spec.Dsa.encodeBE (8 * n) p)
    (startBound : r.length < 2 ^ 32) :
    WP isa (pTest v.name v.code n) s fun t => ∃ rest next,
      PrimalityResult s base bytes (8 * n) (pTestResult (64 * n) p r) rest next t := by
  have lower : 4 ≤ n := by rcases sizes with h | h | h <;> omega
  have upper : n ≤ 48 := by rcases sizes with h | h | h <;> omega
  have bits : 8 * (8 * n) = 64 * n := by omega
  unfold pTest
  refine WP.seq (WP.mono (candidate_width scr capacity (by omega : 0 < 8 * n)
    (by rw [bits]; exact bound) encoded) fun a ⟨carry, memory, K⟩ => ?_)
  rw [bits] at carry
  have Sa := scr.of_keeps K (by decide)
  have Ra : RoundRoom (a.gpr .esp) base bytes := by rw [K.1 .esp (by decide)]; exact room
  have stackA : StkOk (a.gpr .esp - 16#32) base bytes := by rw [K.1 .esp (by decide)]; exact stack
  have Ta : WitnessTape base bytes (a.gpr .esp) ptr r a := by
    rw [K.1 .esp (by decide)]
    exact tape.of_keeps K.2.1 K.2.2 memory
  have cursorA : a.mem.readW (off base witnessCursor) 32 = ptr := by rw [memory]; exact cursor
  have remainingA : a.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length := by rw [memory]; exact remaining
  refine WP.ite (decide (p < 2 ^ (64 * n - 1))) carry ?_ ?_
  · intro reject
    have small := of_decide_eq_true reject
    refine WP.mono (set_word (d := primeStatus) (value := 3) Sa
      (Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity)) fun t ⟨written, eax, KT⟩ => ?_
    have F : SampleRoundFrame base (s.gpr .esp) (8 * n) a t := by
      unfold SampleRoundFrame
      rw [written]
      exact (Frame.refl _ _).writeW (r := ⟨off base Layout.control, 512⟩) (by simp) _
        (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide) (by decide))
    have finalTape := (tape.of_keeps K.2.1 K.2.2 memory).keep F capacity (by omega) KT.2.1 KT.2.2
    refine ⟨r, ptr, finalTape, ?_, ?_, ?_, ?_, (K.mono (by decide)).trans (KT.mono (by decide))⟩
    · rw [written, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessCursor))
        (by decide) (by decide)) (by decide), cursorA]
    · rw [written, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessRemaining))
        (by decide) (by decide)) (by decide), remainingA]
    · rw [pTestResult, ite_eq_left small]
      exact ⟨rfl, eax⟩
    · unfold SampleRoundFrame at F ⊢
      rw [memory] at F
      exact F
  · intro accept
    have full := Nat.le_of_not_gt (of_decide_eq_false accept)
    have domain : VG.Proof.Dsa.Generation.PDomain (8 * n) p := by
      refine ⟨?_, odd, ?_, ?_⟩
      · rcases sizes with h | h | h <;> simp [h]
      · rw [bits]; exact full
      · rw [bits]; exact bound
    refine WP.mono (check_candidate v Sa capacity Ra stackA Ta cursorA remainingA lower upper
      (by omega) (Nat.le_refl _) (by omega) (by decide) (by unfold Layout.p; omega)
      (by rw [memory, encoded, VG.Proof.Dsa.decodeBE_encodeBE (by rw [VG.Proof.Bignum.pow256_eq, bits]; exact bound)])
      domain.large odd domain.bits (by rw [bits]; rcases sizes with h | h | h <;> rw [h] <;> decide) startBound)
      fun t ⟨rest, next, R⟩ => ?_
    refine ⟨rest, next, ?_⟩
    rw [pTestResult, ite_eq_right (of_decide_eq_false accept)]
    exact R.prefix (by unfold SampleRoundFrame; rw [memory]; exact Frame.refl _ _) (K.mono (by decide))

end VG.Proof.Dsa.X86.Generation
