module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.PreparedR2
public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Proof.Framework.X86.Call
public import VerifiedGarbage.Proof.Mont.X86.PowerStep
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2Core
import VerifiedGarbage.Proof.MillerRabin.X86.Copy
import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedContext

/-! # Retain fast R² in its final prepared Miller–Rabin array -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.PreparedR2
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86
open VG.Impl.Bignum.X86.PublicContext

theorem code_ok {mont : Prog isa} {name : String}
    (verified : Verified target mont (Spec.Rsa.Mont.mulContract abi 16))
    (noSp : NoSp mont) (stack : stackUse mont ≤ 16)
    {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (length : g.L = 8 * capacity) (S : Ready g c capacity p s) (bound : g.w ≤ 64)
    (odd : c % 2 = 1) (top : 2 ^ (64 * g.w - 1) ≤ c) :
    WP isa (VG.Impl.RsaKeyGen.X86.PreparedR2.code g.w name mont) s fun t =>
      Ready g c capacity p t ∧
      val32 t.mem g.W (g.array 4) g.words = 2 ^ (64 * g.w) * 2 ^ (64 * g.w) % c ∧
      Frame ([⟨g.W, g.L⟩] ++ [below p 40]) s.mem t.mem ∧
      Keeps VG.Proof.Mont.X86.Dynamic.powerClob s t := by
  unfold VG.Impl.RsaKeyGen.X86.PreparedR2.code
  rw [Prepared.slot_eq, Prepared.slot_eq]
  refine WP.seq (WP.mono (core_ok verified noSp stack v length S bound odd top)
    fun a ⟨A, value, F, K⟩ => ?_)
  refine WP.mono (copy_ok v A.context 4 6 (by decide) (by decide)) fun t ⟨copy, O, Kt, C⟩ => ?_
  have Ot := WorkspaceFrame.of_outs A.scratch.nowrap (Outs.of_outside O (List.mem_singleton_self _))
  have Mt := A.modulus.keep v Ot
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 4; omega))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide)))
  have fit : g.array 4 + 4 * g.words ≤ g.L := v.arrayFit (by decide)
  have caller := A.caller.keepOuts Kt (by decide) (Outs.of_outside O (List.mem_singleton_self _))
    (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)
  have Ft : Frame ([⟨g.W, g.L⟩] ++ [below p 40]) a.mem t.mem :=
    (workspaceGlobalFrame (Outs.of_outside O (List.mem_singleton_self _))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact fit)).mono
      (fun r mem => List.mem_append_left _ mem)
  exact ⟨⟨C, Mt, caller, A.scratch.of_keeps Kt (by decide)⟩,
    copy.trans value, F.trans Ft, K.widen Kt⟩

end VG.Proof.RsaKeyGen.X86.PreparedR2
