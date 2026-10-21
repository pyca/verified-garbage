module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.StageLiteral

/-! # Every four-bit window starts with four unconditional squarings -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem fourSquares_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s) :
    WP isa (.block fourSquares) s fun t =>
      Stage g capacity c p A Js (setAt (setAt V sThreshold 0#32) sSquares 4#32)
        (sSquares :: sThreshold :: Ds) t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax] s t := by
  change WP isa (.block ([.mov .eax (.imm 0), .store (slot sThreshold) .eax] ++
    [.mov .eax (.imm 4), .store (slot sSquares) .eax])) s _
  refine WP.block_append (WP.mono (S.literal v sThreshold
    (by unfold scratchWord sThreshold; simp) 0#32) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.mono (Sa.literal v sSquares (by unfold scratchWord sSquares; simp) 4#32)
    fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨St, Oa.trans Ot, Ka.trans Kt⟩

end VG.Proof.MillerRabin.X86
