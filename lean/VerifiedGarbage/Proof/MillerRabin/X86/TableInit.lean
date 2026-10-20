module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.TableMath
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame

/-! # Initialize table powers zero and one and the product accumulator -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem tableInit_ok {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {Ds : List Nat} {s : State}
    (S : Stage g capacity c p A initialArrays V Ds s) :
    WP isa (seqs [copy aTable aOne, copy (aTable + 1) aX, copy aY aX]) s fun t =>
      Stage g capacity c p (tableValues A c g.w 0) (tableArrays 0) V Ds t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  change WP isa (.seq (copy aTable aOne) (.seq (copy (aTable + 1) aX) (copy aY aX))) s _
  refine WP.seq (WP.mono (S.copy v aTable aOne (by decide) (by decide) (by decide) (by decide))
    fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.copy v (aTable + 1) aX (by decide) (by decide) (by decide) (by decide))
    fun b ⟨Sb, Ob, Kb⟩ => ?_)
  refine WP.mono (Sb.copy v aY aX (by decide) (by decide) (by decide) (by decide))
    fun t ⟨St, Ot, Kt⟩ => ?_
  refine ⟨St.mono ?_ (fun _ mem => ⟨mem, rfl⟩), ?_, (Ka.trans Kb).trans Kt⟩
  · intro j known
    refine ⟨?_, tableValues_initial A c g.w j known⟩
    change j ∈ [6, 12, 11, 0, 5, 9, 10, 27]
    change j ∈ [6, 11, 12, 0, 5, 9, 10, 27] at known
    simp only [List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact ((array_roundFrame S.data.context.ws.nowrap (by unfold roundArray aTable; simp) Oa).trans
      (array_roundFrame Sa.data.context.ws.nowrap (by unfold roundArray aTable; omega) Ob)).trans
        (array_roundFrame Sb.data.context.ws.nowrap (by unfold roundArray aY; simp) Ot)

end VG.Proof.MillerRabin.X86
