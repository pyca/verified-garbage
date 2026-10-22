module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.LoopState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SetWord
import VerifiedGarbage.Proof.Framework.Offset

/-! A short witness tape returns failure without reading a partial draw. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem loop_short {s₀ s : State} {base : Addr} {bytes n len candidate checks startLen measure drawBytes : Nat}
    {result : Option (Bool × List Byte)} {r : List Byte} {ptr : BitVec 32} {i uniform : Nat}
    (R : LoopReady s₀ base bytes n len candidate checks startLen result measure r ptr i uniform s)
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) (length : len ≤ 384)
    (width : Spec.RsaKeyGen.witnessBytes candidate = drawBytes) (positive : 0 < drawBytes)
    (short : r.length < drawBytes) :
    WP isa (.block (setHeader primeStatus 0)) s fun b => WP isa (.block primeLoopEnd) b
      (LoopStepPost s₀ base bytes n len candidate checks startLen result measure) := by
  have failed : result = none := by
    rw [R.spec, VG.Proof.Dsa.Generation.candidate_loop_step r R.go width positive,
      ite_eq_right (show ¬ drawBytes ≤ r.length by omega)]
  refine WP.mono (set_word (d := primeStatus) (value := 0) scr
    (Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity)) fun b ⟨memory, _, K⟩ => ?_
  have F : Frame [⟨off base Layout.control, 512⟩] s.mem b.mem := by
    rw [memory]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide) (by decide))
  have step : SampleRoundFrame base (s.gpr .esp) len s b := F.mono (by simp)
  have T : LoopTerminal s₀ base bytes n len candidate result r ptr 0 b := by
    refine ⟨R.prime.control F K (by decide) (by decide),
      R.keep_tape step (K.mono (by decide)) capacity length, ?_, ?_, ?_, by decide,
      by rw [failed]; rfl, R.frame_step step, R.regs.trans (K.mono (by decide))⟩
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessCursor))
        (by decide) (by decide)) (by decide), R.cursor]
    · rw [memory, Mem.readW_writeW_sep (Offset.sep base (.inr (by decide : primeStatus + 4 ≤ witnessRemaining))
        (by decide) (by decide)) (by decide), R.remaining]
    · rw [memory, Mem.readW_writeW_self32]
  exact WP.mono (T.finish (scr.of_keeps K (by decide)) capacity) fun _ h => Or.inl h

end VG.Proof.Dsa.X86.Generation
