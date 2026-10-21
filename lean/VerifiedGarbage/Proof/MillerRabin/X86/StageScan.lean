module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.DataScan
import VerifiedGarbage.Proof.MillerRabin.X86.RoundScalarFrame
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame

/-! # Selecting a secret digit keeps the modulus and caller frame reusable -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.scan {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A Js V Ds s)
    (tableKnown : ∀ j < 16, aTable + j ∈ Js) (digitKnown : sValue ∈ Ds) (maskUnknown : sEq1 ∉ Ds) :
    WP isa scan s fun t =>
      Stage g capacity c p (setAt A aX (A (aTable + (V sValue >>> 28).toNat))) (aX :: Js) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.mono (S.data.scan v tableKnown digitKnown maskUnknown) fun t ⟨D, O, K⟩ => ?_
  have W := WorkspaceFrame.of_outs S.data.context.ws.nowrap O
  have head := v.arrayHeader aX
  have M : Modulus g c t.mem := S.modulus.keep v W (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; decide
    · left; dsimp only; omega) (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · right; have := v.arrayHeader 0; unfold sEq1; omega
    · exact Or.inl (g.arrayBefore (by decide : 0 < aX)))
  have C := S.caller.keepOuts K (by decide) O (by
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · have := v.headerFit; unfold sEq1; dsimp only; omega
    · exact v.arrayFit (by decide : aX < 28))
  refine ⟨⟨D, M, C, ?_⟩, ?_, K⟩
  · intro j mem
    rcases List.mem_cons.mp mem with rfl | mem
    · decide
    · exact S.noScratch j mem
  · apply W.cover
    intro r mem
    simp only [scanWrites, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl
    · exact scalar_roundRange g (d := sEq1) (by unfold scratchWord sEq1; simp)
    · exact array_roundRange g (j := aX) (by unfold roundArray aX; simp) (by unfold Geometry.words; omega)

end VG.Proof.MillerRabin.X86
