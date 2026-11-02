module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PrepareRt
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Zero
import VerifiedGarbage.Proof.RsaKeyGen.X86.PrepareRt.Doubles
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Squares
import VerifiedGarbage.Proof.RsaKeyGen.X86.WitnessRt.Blocks
import VerifiedGarbage.Proof.MillerRabin.X86.Copy

/-! # R² in array 4 at the run-time width, with `PreparedR2.code_ok`'s post-state -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PrepareRt
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.RsaKeyGen.X86.PrepareRt (r2)
open VG.Proof.RsaKeyGen.X86.PreparedR2 (Ready phaseRanges coreRanges ranges)

theorem r2_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 56)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s)
    (odd : c % 2 = 1) (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (r2 name mont) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t ∧ WorkspaceFrame g (ranges g) s.mem t.mem := by
  obtain ⟨fit6, -, -, words⟩ := WitnessRt.fits v
  have nowrap := S.scratch.nowrap
  unfold r2
  refine WP.seq (WP.seq (WP.mono (seed_ok v S) fun a ⟨A, Va, Oa, Ka⟩ => ?_))
  have Wa : WorkspaceFrame g (phaseRanges g) s.mem a.mem :=
    (WorkspaceFrame.of_outs nowrap (Outs.of_outside Oa (List.mem_singleton_self _))).cover fun r mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact ⟨(g.array 6, 8 * g.w), by simp [phaseRanges], Nat.le_refl _, by dsimp only; omega⟩
  have Fa : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem a.mem :=
    (workspaceGlobalFrame (Outs.of_outside Oa (List.mem_singleton_self _)) fun r mem => by
      obtain rfl := List.mem_singleton.mp mem; exact fit6).mono fun r mem => List.mem_append_left _ mem
  refine WP.seq (WP.mono (doubles_ok v A odd top Va) fun b ⟨B, Vb, Wb, Fb, Kb⟩ => ?_)
  refine WP.mono (PreparedR2.squares_ready verified noSp stack v length B odd Vb) fun d ⟨D, Vd⟩ => ?_
  have K : Keeps VG.Proof.Mont.X86.Dynamic.powerClob s d :=
    (((Ka.mono (by decide)).trans Kb).widen D.keeps)
  have W : WorkspaceFrame g (coreRanges g) s.mem d.mem :=
    ((Wa.trans Wb).mono fun r mem => List.mem_append_left _ mem).trans
      (D.workspace.mono fun r mem => List.mem_append_right _ mem)
  have F : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) s.mem d.mem := (Fa.trans Fb).trans D.memory
  have A := D.ready
  refine WP.mono (copy_ok v A.context 4 6 (by decide) (by decide)) fun t ⟨copy, O, Kt, C⟩ => ?_
  have Ot := WorkspaceFrame.of_outs A.scratch.nowrap (Outs.of_outside O (List.mem_singleton_self _))
  have Mt := A.modulus.keep v Ot
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 4; omega))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide)))
  have fit : g.array 4 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have caller := A.caller.keepOuts Kt (by decide) (Outs.of_outside O (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 80]) d.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside O (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨⟨C, Mt, caller, A.scratch.of_keeps Kt (by decide)⟩,
    copy.trans Vd, F.trans Ft, K.widen Kt,
    (W.mono (fun r mem => List.mem_append_left _ mem)).trans
      (Ot.mono (fun r mem => List.mem_append_right _ mem))⟩

end VG.Proof.RsaKeyGen.X86.PrepareRt
