module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.WindowState
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.LoadWord
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame

/-! # Loading the next exponent word prepares the eight-window stage -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

def wordFields : List Nat := [sFlag, sWords]

theorem Stage.loadWord {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s)
    (q : Nat) (positive : 0 < q) (bound : q ≤ g.words) (count : V sWords = BitVec.ofNat 32 q)
    (word : BitVec 32) (readWord : s.mem.readW (off g.W (g.array aExponent + 4 * (q - 1))) 32 = word) :
    WP isa (.block loadWord) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sValue word) sWindows 8#32) windowFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .edx, .ebp] s t := by
  have header := v.headerFit
  have wf : sWindows + 4 ≤ g.L := by unfold sWindows; omega
  have vf : sValue + 4 ≤ g.L := by unfold sValue; omega
  have scratch : ∀ d ∈ [sValue, sWindows], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sValue; simp
    · unfold scratchWord sWindows; simp
  have countRead := (S.data.slotValues sWords (by decide)).2.trans count
  refine WP.mono (loadWord_ok v S.data.context q positive bound countRead)
    fun t ⟨M, O, K, C⟩ => ?_
  have D : Data g A Js (setAt (setAt V sValue word) sWindows 8#32) ([sValue, sWindows] ++ wordFields) t := by
    refine S.data.afterSlots v C [sValue, sWindows] ?_ ?_ O
    · intro d mem
      refine ⟨scratch d mem, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · change t.mem.readW (off g.W sValue) 32 = word
        apply BitVec.eq_of_toNat_eq
        change w32 t.mem g.W sValue = word.toNat
        rw [M, w32_write_ne S.data.context.ws.nowrap wf vf
          (by left; unfold sValue sWindows; decide), w32_write_self, readWord]
      · change t.mem.readW (off g.W sWindows) 32 = 8#32
        rw [M, Mem.readW_writeW_self32]
    · intro d mem _
      change d ∈ [184, 232] at mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> rfl
  have St := S.afterSlots v D [sValue, sWindows] scratch O K (by decide)
  refine ⟨St.mono (fun _ mem => ⟨mem, rfl⟩) ?_, scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩
  intro d mem
  refine ⟨?_, rfl⟩
  change d ∈ [208, 240, 184, 232]
  change d ∈ [184, 208, 232, 240] at mem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl <;> decide

end VG.Proof.MillerRabin.X86
