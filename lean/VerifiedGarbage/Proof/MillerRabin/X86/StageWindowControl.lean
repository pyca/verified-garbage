module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.DataWindowControl
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.StageSlots
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame

/-! # A completed window retains all invariants needed by the next window -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.windowEnd {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (q : Nat) (positive : 0 < q) (bound : q < 2 ^ 32) (E1 E2 F : Bool)
    (known : ∀ d ∈ [sEq1, sEq2, sFlag, sValue, sWindows], d ∈ Ds)
    (eq1 : V sEq1 = BitVec.ofNat 32 E1.toNat) (eq2 : V sEq2 = BitVec.ofNat 32 E2.toNat)
    (flag : V sFlag = BitVec.ofNat 32 F.toNat) (count : V sWindows = BitVec.ofNat 32 q) :
    WP isa (.block windowEnd) s fun t =>
      Stage g capacity c p A Js (windowSlots V q E1 E2 F) ([sFlag, sValue, sWindows] ++ Ds) t ∧
      t.zf = some (decide (q = 1)) ∧ WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx] s t := by
  have scratch : ∀ d ∈ [sFlag, sValue, sWindows], scratchWord d := by
    intro d mem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · unfold scratchWord sFlag; simp
    · unfold scratchWord sValue; simp
    · unfold scratchWord sWindows; simp
  refine WP.mono (S.data.windowEnd v q positive bound E1 E2 F known eq1 eq2 flag count)
    fun t ⟨D, Z, O, K⟩ => ?_
  exact ⟨S.afterSlots v D [sFlag, sValue, sWindows] scratch O K (by decide), Z,
    scalar_roundFrame S.data.context.ws.nowrap scratch O, K⟩

end VG.Proof.MillerRabin.X86
