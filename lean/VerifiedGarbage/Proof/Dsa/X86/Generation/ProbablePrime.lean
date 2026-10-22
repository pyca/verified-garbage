module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.TestCandidate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimalityResult
import VerifiedGarbage.Proof.Dsa.X86.Generation.SetWord
import VerifiedGarbage.Proof.Framework.Offset

/-! Trial division and the witness loop implement the shared primality policy. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Impl.Mont.X86.Dynamic
open VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86

theorem probable_prime (v : RoundImpl) {s : State} {base : Addr}
    {bytes n len candidate : Nat} {r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (room : RoundRoom (s.gpr .esp) base bytes)
    (stack : StkOk (s.gpr .esp - 16#32) base bytes)
    (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (lower : 4 ≤ n) (upper : n ≤ 48) (lenLow : 4 ≤ len) (length : len ≤ 8 * n) (aligned : len % 4 = 0)
    (modulus : wordsVal s.mem base (slot n 0) n = candidate) (large : 8161 < candidate)
    (odd : candidate % 2 = 1) (bitLength : Spec.Dsa.bitLength candidate = 8 * len)
    (policy : 1024 < 8 * len ↔ 16 < n) (startBound : r.length < 2 ^ 32) :
    WP isa (probablePrime v.name v.code n len) s fun t => ∃ rest next,
      PrimalityResult s base bytes len (Spec.Dsa.probablePrime candidate r) rest next t := by
  have lenBound : len ≤ 384 := by omega
  unfold probablePrime
  refine WP.seq (WP.mono (candidate_trial scr capacity room.callRoom (by omega) upper modulus large policy)
    fun a ⟨value, F, K⟩ => ?_)
  have preparation := trial_preparation_frame F
  have stage := preparation_round_frame (len := len) preparation room.low
  have controls := preparation_control preparation capacity room.callRoom
  have candidateA := (trial_candidate_keep F capacity room.callRoom upper).trans modulus
  refine WP.seq (wp_cmpS rfl fun b B zf => WP.block_nil ?_)
  have KB : Keeps loopRegs s b := (K.mono (by decide)).trans (B.keeps _)
  have FB : SampleRoundFrame base (s.gpr .esp) len s b := by
    unfold SampleRoundFrame at stage ⊢
    rw [B.mem]
    exact stage
  have TB := (tape.keep stage capacity lenBound K.2.1 K.2.2).of_keeps B.rd B.wr B.mem
  have SB := (scr.of_keeps K (by decide)).of_keeps (B.keeps []) (by decide)
  have RB : RoundRoom (b.gpr .esp) base bytes := by rw [KB.1 .esp (by decide)]; exact room
  have stackB : StkOk (b.gpr .esp - 16#32) base bytes := by rw [KB.1 .esp (by decide)]; exact stack
  have cursorB : b.mem.readW (off base witnessCursor) 32 = ptr := by
    rw [B.mem, controls witnessCursor (by decide) (by decide), cursor]
  have remainingB : b.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length := by
    rw [B.mem, controls witnessRemaining (by decide) (by decide), remaining]
  have spec := VG.Proof.Dsa.Generation.probablePrime_large (by omega : 3 < candidate) odd r
  rw [bitLength] at spec
  have flag : b.zf = some (!(Spec.RsaKeyGen.obviouslyComposite (8 * len) candidate)) := by
    rw [zf, value]
    cases Spec.RsaKeyGen.obviouslyComposite (8 * len) candidate <;> rfl
  cases composite : Spec.RsaKeyGen.obviouslyComposite (8 * len) candidate
  · rw [composite] at flag spec
    refine WP.ite true flag ?_ (by intro h; cases h)
    intro _
    have tapeB : WitnessTape base bytes (b.gpr .esp) ptr r b := by rw [KB.1 .esp (by decide)]; exact TB
    refine WP.mono (test_candidate v SB capacity RB stackB tapeB cursorB remainingB lower upper lenLow length aligned
      (by rw [B.mem]; exact candidateA) (by omega) odd bitLength startBound) fun t ⟨rest, next, R⟩ => ?_
    refine ⟨rest, next, ?_⟩
    rw [spec]
    exact R.primality.prefix FB KB
  · rw [composite] at flag spec
    refine WP.ite false flag (by intro h; cases h) ?_
    intro _
    refine WP.mono (set_word (d := primeStatus) (value := 3) SB
      (Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity)) fun t ⟨memory, eax, KT⟩ => ?_
    have FT : Frame [⟨off base Layout.control, 512⟩] b.mem t.mem := by
      rw [memory]
      exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide) (by decide))
    have step : SampleRoundFrame base (s.gpr .esp) len b t := FT.mono (by simp)
    refine ⟨r, ptr, TB.keep step capacity lenBound KT.2.1 KT.2.2, ?_, ?_, ?_, FB.trans step,
      KB.trans (KT.mono (by decide))⟩
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessCursor))
        (by decide) (by decide)) (by decide), cursorB]
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessRemaining))
        (by decide) (by decide)) (by decide), remainingB]
    · rw [spec]
      exact ⟨rfl, eax⟩

end VG.Proof.Dsa.X86.Generation
