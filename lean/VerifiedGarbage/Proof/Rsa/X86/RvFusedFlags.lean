module

import VerifiedGarbage.Proof.Rsa.X86.RvSlots
public import VerifiedGarbage.Proof.Rsa.RecoverExp
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Rsa.X86.RvBase
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass

/-! Boolean header operations for the fused recovery pass. -/
@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys
open VG.Proof.Rsa (b2n)

section
variable {g : Geo} {s0 s : State} {A AW V : Nat → Nat} {live liveW ls : List Nat}

 theorem KS.flagNot_ok {d a : Nat} {x : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (va : V a = b2n x) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagNot d a) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (!x))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagNot
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inr rfl) rfl fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (!x) := by
    rw [D.gpr, ite_eq_right (by decide), U.gpr, va]
    cases x <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

theorem KS.flagAnd_ok {d a b : Nat} {x y : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (hb : b ∈ ls)
    (va : V a = b2n x) (vb : V b = b2n y) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagBin .and d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (x && y))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagBin
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_logicS (.inl rfl) (hu.readSlot hb) fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (x && y) := by
    rw [D.gpr, ite_eq_left rfl, U.gpr, va, vb]
    cases x <;> cases y <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

theorem KS.flagOr_ok {d a b : Nat} {x y : Bool}
    (h : KS g s0 A live AW liveW V ls s) (hd : SlotOk d) (ha : a ∈ ls) (hb : b ∈ ls)
    (va : V a = b2n x) (vb : V b = b2n y) :
    WP isa (VG.Impl.Rsa.X86.RecoverRt.flagBin .or d a b) s fun t =>
      KS g s0 A live AW liveW (upd V d (b2n (x || y))) (d :: ls) t := by
  unfold VG.Impl.Rsa.X86.RecoverRt.flagBin
  refine wp_movS (h.readSlot ha) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_orS (hu.readSlot hb) fun v D => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = b2n (x || y) := by
    rw [D.gpr, U.gpr, va, vb]
    cases x <;> cases y <;> decide
  refine WP.block_append (WP.mono (hv.storeSlot hd .eax) fun t ⟨ht, _, _⟩ => ?_)
  rw [value] at ht
  exact WP.block_nil ht

end
end VG.Proof.Rsa.X86.Recover
