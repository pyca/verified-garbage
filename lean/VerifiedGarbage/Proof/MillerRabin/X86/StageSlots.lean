module

public import VerifiedGarbage.Proof.MillerRabin.X86.Stage
public import VerifiedGarbage.Proof.MillerRabin.X86.DataSlots

/-! # Scratch updates preserve the reusable modulus and nested-call interface -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

theorem Stage.afterSlots {g : Geometry} (v : g.Valid) {capacity c : Nat} {p : BitVec 32}
    {A : Nat → Nat} {Js : List Nat} {V V' : Nat → BitVec 32} {Ds Ds' : List Nat} {s t : State}
    (S : Stage g capacity c p A Js V Ds s) (D : Data g A Js V' Ds' t)
    (changed : List Nat) (scratch : ∀ d ∈ changed, scratchWord d)
    (O : Outs g.W (slotWrites changed) s.mem t.mem)
    {regs : List Reg} (K : Keeps regs s t) (sp : .esp ∉ regs) :
    Stage g capacity c p A Js V' Ds' t := by
  have M : Modulus g c t.mem := S.modulus.keep v (WorkspaceFrame.of_outs S.data.context.ws.nowrap O) (by
    intro r mem
    obtain ⟨d, known, rfl⟩ := List.mem_map.mp mem
    have h := scratch d known
    unfold scratchWord at h
    dsimp only
    omega) (by
    intro r mem
    obtain ⟨d, known, rfl⟩ := List.mem_map.mp mem
    exact Or.inr (Nat.le_trans (scratch_fit (scratch d known)) (v.arrayHeader 0)))
  have C := S.caller.keepOuts K sp O (by
    intro r mem
    obtain ⟨d, known, rfl⟩ := List.mem_map.mp mem
    exact Nat.le_trans (scratch_fit (scratch d known)) v.headerFit)
  exact ⟨D, M, C, S.noScratch⟩

end VG.Proof.MillerRabin.X86
