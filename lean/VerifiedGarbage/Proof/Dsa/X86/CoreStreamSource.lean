module

public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Mont.X86.ContextFrame
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.X86.Wp
import VerifiedGarbage.Proof.Mont.X86.Words
import VerifiedGarbage.TCB.X86.Isa
import VerifiedGarbage.TCB.X86.State

/-! # The public byte-source pointer for scalar reduction -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

theorem streamSource_ok {s : State} {base : Addr} {size n m : Nat}
    (h : Context n m base size s) (hz : VG.Impl.Dsa.X86.Layout.saved ≤ size) (p : Pointer) :
    WP isa (.block (Core.pointer p)) s fun t =>
      Context n m base size t ∧ t.gpr .esi = pointerValue base s p ∧ t.mem = s.mem ∧ Keeps [.esi] s t :=
  WP.mono (pointer_ok h.scr hz p) fun u ⟨Pu, Ku, Mu⟩ =>
    ⟨⟨h.scr.of_keeps Ku (by decide), h.size_le, Mu ▸ h.modulus, h.gt_one, Mu ▸ h.inverse⟩, Pu, Mu, Ku⟩

end VG.Proof.Dsa.X86
