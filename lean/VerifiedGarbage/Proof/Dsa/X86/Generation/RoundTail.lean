module

public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundOutcome
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundFinish
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SampleGeometry
import VerifiedGarbage.Proof.Framework.Offset

/-! Complete the shared blinded/uniform policy after one verified round. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.X86.Wp VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation
open VG.Proof.Mont VG.Proof.Mont.X86

def PolicyFrame (base : Addr) (s t : State) : Prop :=
  Frame [⟨off base roundIndex, 4⟩, ⟨off base uniformCount, 4⟩,
    ⟨off base primeStatus, 4⟩] s.mem t.mem

theorem next_status_valid (passed u : Bool) (i uniform checks : Nat) :
    nextStatus passed i uniform checks u = 1 ∨ nextStatus passed i uniform checks u = 3 ∨
      nextStatus passed i uniform checks u = 4 := by
  cases passed
  · exact .inr (.inl rfl)
  · by_cases h : i + 1 < 17 ∨ uniform + u.toNat < checks
    · exact .inr (.inr (by simp only [nextStatus, ite_true, ite_eq_left h]))
    · exact .inl (by simp only [nextStatus, ite_true, ite_eq_right h])

theorem round_tail {s : State} {base : Addr} {bytes i uniform checks : Nat} {passed u : Bool}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes)
    (index : s.mem.readW (off base roundIndex) 32 = BitVec.ofNat 32 i)
    (count : s.mem.readW (off base uniformCount) 32 = BitVec.ofNat 32 uniform)
    (witness : s.mem.readW (off base witnessUniform) 32 = BitVec.ofNat 32 u.toNat)
    (hi : i + 1 < 2 ^ 32) (hu : uniform + u.toNat < 2 ^ 32) (hc : checks < 2 ^ 32)
    (result : s.gpr .eax = BitVec.ofNat 32 passed.toNat) :
    WP isa (roundTail checks) s fun t =>
      t.gpr .eax = BitVec.ofNat 32 (nextStatus passed i uniform checks u) ∧
      t.mem = (if passed then countMemory s.mem base i uniform u else s.mem).writeW
        (off base primeStatus) (BitVec.ofNat 32 (nextStatus passed i uniform checks u)) ∧
      t.zf = some (decide (nextStatus passed i uniform checks u = 4)) ∧
      Frame [⟨off base Layout.control, 512⟩] s.mem t.mem ∧ PolicyFrame base s t ∧
      Keeps [.eax, .ecx, .edx] s t := by
  unfold roundTail
  refine WP.seq (wp_cmpS rfl fun a A zf => WP.block_nil ?_)
  have test : a.zf = some (!passed) := by
    rw [zf, result]
    cases passed <;> rfl
  have Sa := scr.of_keeps (A.keeps []) (by decide)
  refine WP.seq (WP.mono (round_outcome Sa capacity (by rw [A.mem]; exact index)
    (by rw [A.mem]; exact count) (by rw [A.mem]; exact witness) hi hu hc test)
    fun b ⟨value, mem, Kb⟩ => ?_)
  have K : Keeps [.eax, .ecx, .edx] s b := (A.keeps _).trans Kb
  have Sb := scr.of_keeps K (by decide)
  refine WP.mono (round_finish Sb capacity (next_status_valid passed u i uniform checks) value)
    fun t ⟨memory, zf, Kt⟩ => ?_
  have allmem : t.mem = (if passed then countMemory s.mem base i uniform u else s.mem).writeW
      (off base primeStatus) (BitVec.ofNat 32 (nextStatus passed i uniform checks u)) := by
    rw [memory, mem, A.mem]
  refine ⟨(Kt.1 .eax (by decide)).trans value, allmem, zf, ?_, ?_, K.trans (Kt.mono (by decide))⟩
  · rw [allmem]
    cases passed
    · exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide : primeStatus + 4 ≤ Layout.control + 512) (by decide))
    · exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
        (Offset.contains base (by decide : Layout.control ≤ roundIndex) (by decide : roundIndex + 4 ≤ Layout.control + 512) (by decide))).writeW
        (List.mem_singleton_self _) _
        (Offset.contains base (by decide : Layout.control ≤ uniformCount) (by decide : uniformCount + 4 ≤ Layout.control + 512) (by decide))).writeW
        (List.mem_singleton_self _) _
        (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide : primeStatus + 4 ≤ Layout.control + 512) (by decide))
  · unfold PolicyFrame
    rw [allmem]
    cases passed
    · exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    · exact (((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
        (by simp) _ (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.Dsa.X86.Generation
