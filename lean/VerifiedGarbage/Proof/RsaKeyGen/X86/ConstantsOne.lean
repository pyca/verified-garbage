module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.Mont.X86.Power
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.Mont.X86.PowerInit

/-! # Plain one enters the prepared multiplier without rebuilding its modulus -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Constants
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

theorem plainOne_ok {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) :
    WP isa (VG.Impl.Mont.X86.Dynamic.one g.w (g.array 6)) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array 6) g.words = 1 ∧
      val32 t.mem g.W (g.array 4) g.words = val32 s.mem g.W (g.array 4) g.words ∧
      Outside g.W (g.array 6) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ebp, .edx] s t := by
  refine WP.mono (VG.Proof.Mont.X86.Dynamic.one_ok S.scratch (by have := v.minWidth; omega)
    (show g.array 6 + 8 * g.w ≤ g.L from by have := v.arrayFit (j := 6) (by decide); unfold Geometry.words at this; omega))
    fun t ⟨O, V, K⟩ => ?_
  rw [show 8 * g.w = 4 * g.words by unfold Geometry.words; omega] at O
  have W := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.scratch.nowrap W
  refine ⟨⟨S.context.keepOutside K (by decide) O (v.arrayHeader _),
    S.modulus.keep v F (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (by have := v.arrayHeader 6; omega))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore (by decide))),
    S.caller.keepOuts K (by decide) W (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit (by decide)),
    S.scratch.of_keeps K (by decide)⟩, ?_, ?_, O, K⟩
  · unfold Geometry.words
    rw [← wordsVal_eq_val32]
    exact V
  · exact O.val32 (Or.inl (g.arrayBefore (by decide))) (by have := S.scratch.nowrap; have := v.arrayFit (j := 4) (by decide); omega)

end VG.Proof.RsaKeyGen.X86.Constants
