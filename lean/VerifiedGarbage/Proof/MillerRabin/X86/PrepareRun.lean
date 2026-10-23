module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.MillerRabin.X86.RunView
public import VerifiedGarbage.Proof.MillerRabin.X86.StageLoadWord
public import VerifiedGarbage.Proof.MillerRabin.X86.RoundFrame
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86.Call
import VerifiedGarbage.Proof.MillerRabin.X86.Table
import VerifiedGarbage.Proof.MillerRabin.X86.StageCopy
import VerifiedGarbage.Proof.MillerRabin.X86.InitWindows
import VerifiedGarbage.Proof.MillerRabin.X86.RoundArrayFrame

/-! # The table and initial Montgomery one are ready before exponent scanning -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem prepareRun_ok {code : Prog isa} {name : String}
    (verified : Verified target code (Spec.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp code) (stack : stackUse code ≤ 56)
    {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {V : Nat → BitVec 32} {s : State}
    (S : Stage g capacity c p A initialArrays V [] s)
    (length : g.L = 8 * capacity) (odd : c % 2 = 1) (Xlt : A aX < c) :
    WP isa (.seq (table name code) (.seq (copy aY aOne) (.block initWindows))) s fun t =>
      Stage g capacity c p (runValues A c g.w) runArrays
        (setAt (setAt V sWords (BitVec.ofNat 32 g.words)) sFlag 0#32) wordFields t ∧
      WorkspaceFrame g (roundWrites g) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s t := by
  refine WP.seq (WP.mono (table_ok verified noSp stack v S length odd Xlt) fun a ⟨Sa, Oa, Ka⟩ => ?_)
  refine WP.seq (WP.mono (Sa.copy v aY aOne (by decide) (by decide) (by decide)
    (by simp [tableArrays, initialArrays])) fun b ⟨Sb, Ob, Kb⟩ => ?_)
  change Stage g capacity c p (runValues A c g.w) (aY :: tableArrays 14) V [] b at Sb
  have Start : Stage g capacity c p (runValues A c g.w) runArrays V [] b :=
    Sb.mono (by
      intro j mem
      refine ⟨?_, rfl⟩
      rcases List.mem_append.mp mem with base | power
      · change j ∈ [6, 9, 10, 27, 0] at base
        simp only [List.mem_cons, List.not_mem_nil, or_false] at base
        rcases base with rfl | rfl | rfl | rfl | rfl <;> decide
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ power)))
      (fun _ mem => ⟨mem, rfl⟩)
  refine WP.mono (initWindows_ok v Start) fun t ⟨St, Ot, Kt⟩ => ?_
  exact ⟨St, (Oa.trans (array_roundFrame Sa.data.context.ws.nowrap
    (by unfold roundArray aY; simp) Ob)).trans Ot,
    (Ka.trans (Kb.mono (by decide))).trans (Kt.mono (by decide))⟩

end VG.Proof.MillerRabin.X86
