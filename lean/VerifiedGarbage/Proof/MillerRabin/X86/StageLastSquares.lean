module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.LastSquares
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
public import VerifiedGarbage.Proof.RsaKeyGen.MrWindow
public import VerifiedGarbage.TCB.Code

/-! # The folded marker prepares a fixed three-square finishing stage -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.lastSquares {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A Js V wordFields s)
    {k : Nat} (bound : k < 64)
    (lo : s.mem.readW (off g.W (g.array aExponent + 4 * g.words)) 32 = BitVec.ofNat 32 (2 ^ k % 2 ^ 32))
    (hi : s.mem.readW (off g.W (g.array aExponent + 4 * g.words + 4)) 32 = BitVec.ofNat 32 (2 ^ k / 2 ^ 32)) :
    WP isa (.block lastSquares) s fun t =>
      Stage g capacity c p A Js
        (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
        ([sThreshold, sSquares] ++ wordFields) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  have header := v.headerFit
  have tf : sThreshold + 4 ≤ g.L := by unfold sThreshold; omega
  have sf : sSquares + 4 ≤ g.L := by unfold sSquares; omega
  have scratch : ∀ d ∈ [sThreshold, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sThreshold; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (lastSquares_ok v S.data.context bound lo hi) fun t ⟨M, O, K, C⟩ => ?_
  have D : Data g A Js
      (setAt (setAt V sThreshold (BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k))) sSquares 3#32)
      ([sThreshold, sSquares] ++ wordFields) t := by
    refine S.data.afterSlots v C [sThreshold, sSquares] ?_ ?_ O
    · intro d mem
      refine ⟨scratch d mem, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl
      · change t.mem.readW (off g.W sThreshold) 32 = BitVec.ofNat 32 (4 - VG.Proof.RsaKeyGen.sigOf k)
        apply BitVec.eq_of_toNat_eq
        change w32 t.mem g.W sThreshold = _
        rw [M, w32_write_ne S.data.context.ws.nowrap sf tf
          (by right; unfold sThreshold sSquares; decide), w32_write_self]
      · change t.mem.readW (off g.W sSquares) 32 = 3#32
        rw [M, Mem.readW_writeW_self32]
    · intro d mem _
      change d ∈ [184, 232] at mem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl <;> rfl
  exact ⟨S.afterSlots v D [sThreshold, sSquares] scratch O K (by decide),
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
