module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Rsa.X86.RvScalarOps
import VerifiedGarbage.Proof.Rsa.KeyBits32
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Recording whether the current exponent is even and counting its halvings -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys VG.Proof.Rsa.KeyBits32

def Vhalf (V : Nat → Nat) (R : Nat) : Nat → Nat :=
  upd (upd (upd V sBit (R % 2)) sBit (1 - R % 2)) sTc (V sTc + (1 - R % 2))

theorem KS.halfBit_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hr : wR ∈ liveW) (hc : sTc ∈ ls)
    (bound : V sTc ≤ 16384) :
    WP isa (.block (halfBit g.n)) s fun t =>
      KS g s0 A live AW liveW (Vhalf V (AW wR)) (sTc :: sBit :: sBit :: ls) t := by
  unfold halfBit
  refine WP.block_append (WP.mono (h.bitOf_W hr (by decide)) fun u ⟨hu, _⟩ => ?_)
  refine WP.block_append (WP.mono (hu.loadSlot (d := sBit) (by simp) (r := .eax) (by decide))
    fun v ⟨hv, vx, _⟩ => ?_)
  refine wp_logicS (.inr rfl) rfl fun w W => ?_
  have hw := hv.of_rest W.keeps (by decide) W.mem
  have even : (w.gpr .eax).toNat = 1 - AW wR % 2 := by
    rw [W.gpr, ite_eq_right (by decide), vx, upd_self]
    rw [bv_xor_bits (by rw [BitVec.toNat_ofNat]; omega) (by decide), BitVec.toNat_ofNat]
    simp only [show (1 : BitVec 32).toNat = 1 from rfl]
    omega
  refine WP.block_append (WP.mono (hw.storeSlot (d := sBit) (by decide) .eax)
    fun x ⟨hx, _, rx⟩ => ?_)
  rw [even] at hx
  refine WP.block_append (WP.mono (hx.loadSlot (d := sTc) (by simp [hc]) (r := .edx) (by decide))
    fun y ⟨hy, yt, ry⟩ => ?_)
  refine wp_addS rfl fun z Z _ => ?_
  have hz := hy.of_rest Z.keeps (by decide) Z.mem
  have total : (z.gpr .edx).toNat = V sTc + (1 - AW wR % 2) := by
    rw [Z.gpr, yt, ry.1 .eax (by decide), rx.1 .eax (by decide),
      upd_ne _ _ (by decide : sTc ≠ sBit), upd_ne _ _ (by decide : sTc ≠ sBit),
      BitVec.toNat_add, BitVec.toNat_ofNat, even]
    omega
  refine WP.mono (hz.storeSlot (d := sTc) (by decide) .edx) fun t ⟨ht, _, _⟩ => ?_
  rw [total] at ht
  exact ht

end VG.Proof.Rsa.X86.Recover
