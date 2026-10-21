module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.PreparedR2State
public import VerifiedGarbage.Impl.MillerRabin.X86.Ops
public import VerifiedGarbage.Proof.Framework.Semantics
import VerifiedGarbage.Proof.MillerRabin.X86.Copy

/-! # Copy a prepared operand while retaining the modulus and callable context -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Prepared
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.MillerRabin.X86 VG.Proof.RsaKeyGen.X86.PreparedR2

theorem copy_ready {g : Geometry} (v : g.Valid) {s : State} {c capacity : Nat} {p : BitVec 32}
    (S : Ready g c capacity p s) (dst src : Nat) (dstIndex : dst < 28) (srcIndex : src < 28) (notMod : 0 < dst) :
    WP isa (VG.Impl.MillerRabin.X86.copy dst src) s fun t =>
      Ready g c capacity p t ∧ val32 t.mem g.W (g.array dst) g.words = val32 s.mem g.W (g.array src) g.words ∧
      Outside g.W (g.array dst) (4 * g.words) s.mem t.mem ∧ Keeps [.eax, .ebx, .edx, .ebp, .esi] s t := by
  refine WP.mono (copy_ok v S.context dst src dstIndex srcIndex) fun t ⟨V, O, K, C⟩ => ?_
  have W := Outs.of_outside O (List.mem_singleton_self _)
  have F := WorkspaceFrame.of_outs S.scratch.nowrap W
  refine ⟨⟨C, S.modulus.keep v F (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (Nat.le_trans (by decide) (v.arrayHeader dst)))
      (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact Or.inl (g.arrayBefore notMod)),
    S.caller.keepOuts K (by decide) W (fun r mem => by obtain rfl := List.mem_singleton.mp mem; exact v.arrayFit dstIndex),
    S.scratch.of_keeps K (by decide)⟩, V, O, K⟩

end VG.Proof.RsaKeyGen.X86.Prepared
