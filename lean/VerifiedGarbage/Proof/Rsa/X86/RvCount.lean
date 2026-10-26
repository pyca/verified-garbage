module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Order.RelClasses
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Decrementing a public loop counter and setting the termination flag -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem KS.cntNext_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hc : sCnt ∈ ls)
    (lo : 1 ≤ V sCnt) (hi : V sCnt < 2 ^ 32) :
    WP isa (.block cntNext) s fun t =>
      KS g s0 A live AW liveW (upd V sCnt (V sCnt - 1)) (sCnt :: ls) t ∧
      t.zf = some (decide (V sCnt - 1 = 0)) := by
  unfold cntNext
  refine wp_movS (h.readSlot hc) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_subi fun v D _ flags => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : v.gpr .eax = BitVec.ofNat 32 (V sCnt - 1) := by
    rw [D.gpr, U.gpr]
    exact BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) lo
  refine WP.mono (hv.storeSlot (d := sCnt) (by decide) .eax) fun t ⟨ht, zt, _⟩ => ?_
  have number : (v.gpr .eax).toNat = V sCnt - 1 := by
    rw [value, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine ⟨number ▸ ht, ?_⟩
  rw [zt, flags, U.gpr, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl,
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) lo]
  congr 1
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]
  rfl

end VG.Proof.Rsa.X86.Recover
