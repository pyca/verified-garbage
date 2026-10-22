module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawRound
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PolicyValues
public import VerifiedGarbage.Impl.Dsa.X86.Generation.MillerRabin

/-! Apply the shared blinded/uniform policy to a consumed witness draw. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

theorem tested_draw {s : State} {base : Addr} {name : String} {code : Prog isa}
    {bytes n len drawBytes remaining candidate i uniform checks : Nat} {src : BitVec 32}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (draw : WP isa (drawRound name code n len drawBytes) s
      (DrawRoundResult s base n len drawBytes remaining candidate src))
    (index : s.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i)
    (count : s.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform)
    (hi : i + 1 < 2 ^ 32) (hu : uniform + 1 < 2 ^ 32) (hc : checks < 2 ^ 32) :
    WP isa (testedDraw name code n len drawBytes checks) s fun t =>
      let w := drawnWitness candidate s.mem src drawBytes
      let passed := Spec.MillerRabin.round candidate w.1
      let status := nextStatus passed i uniform checks w.2
      PrimeState base n candidate t ∧ t.gpr .eax = BitVec.ofNat 32 status ∧
      t.zf = some (decide (status = 4)) ∧ t.mem.readW (off base primeStatus) 32 = BitVec.ofNat 32 status ∧
      t.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 (if passed then i + 1 else i) ∧
      t.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 (if passed then uniform + w.2.toNat else uniform) ∧
      t.mem.readW (off base witnessCursor) 32 = src + BitVec.ofNat 32 drawBytes ∧
      t.mem.readW (off base witnessRemaining) 32 = BitVec.ofNat 32 (remaining - drawBytes) ∧
      SampleRoundFrame base (s.gpr .esp) len s t ∧ Keeps [.eax, .ebx, .ecx, .edx, .esi, .ebp] s t := by
  unfold testedDraw
  refine WP.seq (WP.mono draw fun a ⟨A, result, flag, next, left, controls, F, K⟩ => ?_)
  have Sa := scr.of_keeps K (by decide)
  have ia : a.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i := by
    rw [controls roundIndex (by decide) (by decide), index]
  have ua : a.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform := by
    rw [controls uniformCount (by decide) (by decide), count]
  have flagWord : a.mem.readW (off base witnessUniform) 32 =
      BitVec.ofNat 32 (drawnWitness candidate s.mem src drawBytes).2.toNat := by
    apply BitVec.eq_of_toNat_eq
    change w32 a.mem base witnessUniform = _
    rw [flag]
    cases (drawnWitness candidate s.mem src drawBytes).2 <;> rfl
  refine WP.mono (round_tail Sa capacity ia ua flagWord hi (by
    have : (drawnWitness candidate s.mem src drawBytes).2.toNat ≤ 1 := Bool.toNat_le _
    omega) hc result) fun t ⟨value, memory, zf, Ft, fine, Kt⟩ => ?_
  obtain ⟨it, ut⟩ := policy_counters ia ua memory
  refine ⟨A.control Ft Kt (by decide) (by decide), value, zf, ?_, it, ut, ?_, ?_, ?_,
    K.trans (Kt.mono (by decide))⟩
  · rw [memory, Mem.readW_writeW_self32]
  · rw [policy_tape_control fine (d := witnessCursor) (by decide) (by decide), next]
  · rw [policy_tape_control fine (d := witnessRemaining) (by decide) (by decide), left]
  · exact F.trans (Ft.mono (by simp))

end VG.Proof.Dsa.X86.Generation
