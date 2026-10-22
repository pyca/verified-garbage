module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.MillerRabin
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SetWord
public import VerifiedGarbage.Proof.Dsa.X86.Generation.RoundTail
import VerifiedGarbage.Proof.Framework.Offset

/-! Initialize the shared policy without disturbing a retained candidate or tape cursor. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation VG.Proof.Mont VG.Proof.Mont.X86

theorem prime_loop_init {s : State} {base : Addr} {bytes : Nat}
    (scr : Scr s base bytes) (capacity : 40960 ≤ bytes) :
    WP isa (.block primeLoopInit) s fun t =>
      t.mem = ((s.mem.writeW (off base roundIndex) 1#32).writeW (off base uniformCount) 0#32).writeW
        (off base primeStatus) 4#32 ∧
      Frame [⟨off base Layout.control, 512⟩] s.mem t.mem ∧ PolicyFrame base s t ∧ Keeps [.eax] s t := by
  unfold primeLoopInit
  rw [List.append_assoc]
  refine WP.block_append (WP.mono (set_word (d := roundIndex) (value := 1) scr
    (Nat.le_trans (by decide : roundIndex + 4 ≤ 40960) capacity)) fun a ⟨ma, _, Ka⟩ => ?_)
  have Sa := scr.of_keeps Ka (by decide)
  refine WP.block_append (WP.mono (set_word (d := uniformCount) (value := 0) Sa
    (Nat.le_trans (by decide : uniformCount + 4 ≤ 40960) capacity)) fun b ⟨mb, _, Kb⟩ => ?_)
  have Sb := Sa.of_keeps Kb (by decide)
  refine WP.mono (set_word (d := primeStatus) (value := 4) Sb
    (Nat.le_trans (by decide : primeStatus + 4 ≤ 40960) capacity)) fun t ⟨mt, _, Kt⟩ => ?_
  have memory : t.mem = ((s.mem.writeW (off base roundIndex) 1#32).writeW (off base uniformCount) 0#32).writeW
      (off base primeStatus) 4#32 := by rw [mt, mb, ma]
  refine ⟨memory, ?_, ?_, (Ka.trans Kb).trans Kt⟩
  · rw [memory]
    exact (((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ roundIndex) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ uniformCount) (by decide) (by decide))).writeW
      (List.mem_singleton_self _) _
      (Offset.contains base (by decide : Layout.control ≤ primeStatus) (by decide) (by decide))
  · unfold PolicyFrame
    rw [memory]
    exact (((Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)).writeW
      (by simp) _ (Region.contains_self _ _)).writeW (by simp) _ (Region.contains_self _ _)

end VG.Proof.Dsa.X86.Generation
