module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.DataSquareControl
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame

/-! # A square's public countdown keeps the complete prepared stage usable -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.squareFlag {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    {q r : Nat} (positive : 0 < q) (qBound : q < 2 ^ 31) (rBound : r < 2 ^ 31) (E F : Bool)
    (known : ∀ d ∈ [sSquares, sThreshold, sEq2, sFlag], d ∈ Ds)
    (count : V sSquares = BitVec.ofNat 32 q) (threshold : V sThreshold = BitVec.ofNat 32 r)
    (eqBit : V sEq2 = BitVec.ofNat 32 E.toNat) (flag : V sFlag = BitVec.ofNat 32 F.toNat) :
    WP isa (.block squareFlag) s fun t =>
      Stage g capacity c p A Js (squareSlots V q r E F) ([sFlag, sSquares] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sSquares], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sSquares; simp
  refine WP.mono (S.data.squareFlag v positive qBound rBound E F known count threshold eqBit flag)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sSquares] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
