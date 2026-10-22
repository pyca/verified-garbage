module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopStep
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeLoopInit
import VerifiedGarbage.Proof.Framework.Offset

/-! Complete functional correctness of the streamed, shared-policy witness loop. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Proof.Dsa.Generation (candidateLoop)

theorem miller_rabin (v : RoundImpl) {s : State} {base : Addr}
    {bytes n len candidate checks drawBytes : Nat} {r : List Byte} {ptr : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (S : PrimeState base n candidate s)
    (stack : RoundRoom (s.gpr .esp) base bytes) (tape : WitnessTape base bytes (s.gpr .esp) ptr r s)
    (cursor : s.mem.readW (off base witnessCursor) 32 = ptr)
    (remaining : s.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 r.length)
    (positive : 0 < n) (upper : n ≤ 48) (lower : 4 ≤ len)
    (length : len ≤ 8 * n) (aligned : len % 4 = 0) (padded : len ≤ drawBytes)
    (bits : Spec.RsaKeyGen.bitLength (candidate - 1) = 8 * len)
    (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes)
    (drawBound : drawBytes < 2 ^ 32) (checksBound : checks < 2 ^ 32) (startBound : r.length < 2 ^ 32) :
    WP isa (millerRabin v.name v.code n len drawBytes checks) s fun t =>
      ∃ rest next, LoopResult s base bytes n len candidate (candidateLoop candidate checks 1 0 r) rest next t := by
  unfold millerRabin
  refine WP.seq (WP.mono (prime_loop_init scr capacity) fun a ⟨memory, F, fine, K⟩ => ?_)
  have step : SampleRoundFrame base (s.gpr .esp) len s a := F.mono (by simp)
  have A : LoopReady s base bytes n len candidate checks r.length
      (candidateLoop candidate checks 1 0 r) r.length r ptr 1 0 a := by
    refine ⟨S.control F K (by decide) (by decide), tape.keep step capacity (by omega) K.2.1 K.2.2,
      rfl, Nat.le_refl _, by omega, by decide, Or.inl (by decide), ?_, ?_, ?_, ?_, rfl,
      step, K.mono (by decide)⟩
    · rw [policy_tape_control fine (d := witnessCursor) (by decide) (by decide), cursor]
    · rw [policy_tape_control fine (d := witnessRemaining) (by decide) (by decide), remaining]
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : roundIndex + 4 ≤ primeStatus))
        (by decide) (by decide)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : roundIndex + 4 ≤ uniformCount))
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inl (by decide : uniformCount + 4 ≤ primeStatus))
        (by decide) (by decide)) (by decide), Mem.readW_writeW_self32]
  exact witness_loop v scr capacity stack positive upper lower length aligned padded bits width drawBound checksBound startBound
    ⟨r, ptr, 1, 0, A⟩

end VG.Proof.Dsa.X86.Generation
