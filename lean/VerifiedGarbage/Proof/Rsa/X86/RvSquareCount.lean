module
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.RvBase

import VerifiedGarbage.Proof.Rsa.X86.RvCount
import VerifiedGarbage.Proof.Rsa.X86.RvSlots
import VerifiedGarbage.Proof.Mont.X86.Instr
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The iteration number and countdown of the recovery squaring loop -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Recover
open VG VG.X86 VG.X86.Wp VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.Rsa.X86.Recover
open VG.Proof.Rsa.X86.Keys

theorem KS.sqNext_ok {g : Geo} {s0 s : State} {A : Nat → Nat} {live : List Nat}
    {AW : Nat → Nat} {liveW : List Nat} {V : Nat → Nat} {ls : List Nat}
    (h : KS g s0 A live AW liveW V ls s) (hk : sK ∈ ls) (hc : sCnt ∈ ls)
    (kb : V sK + 1 < 2 ^ 32) (lo : 1 ≤ V sCnt) (hi : V sCnt < 2 ^ 32) :
    WP isa (.block sqNext) s fun t =>
      KS g s0 A live AW liveW (upd (upd V sK (V sK + 1)) sCnt (V sCnt - 1))
        (sCnt :: sK :: ls) t ∧ t.zf = some (decide (V sCnt - 1 = 0)) := by
  unfold sqNext
  simp only [List.cons_append, List.nil_append]
  refine wp_movS (h.readSlot hk) fun u U _ => ?_
  have hu := h.of_rest U.keeps (by decide) U.mem
  refine wp_addS rfl fun v D _ => ?_
  have hv := hu.of_rest D.keeps (by decide) D.mem
  have value : (v.gpr .eax).toNat = V sK + 1 := by
    rw [D.gpr, U.gpr, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (V sK % 2 ^ 32 + 1) % 2 ^ 32 = _
    omega
  refine WP.block_append (WP.mono (hv.storeSlot (d := sK) (by decide) .eax)
    fun w ⟨hw, _, _⟩ => ?_)
  rw [value] at hw
  refine WP.mono (hw.cntNext_ok (by simp [hc])
    (by simpa only [upd_ne _ _ (by decide : sCnt ≠ sK)] using lo)
    (by simpa only [upd_ne _ _ (by decide : sCnt ≠ sK)] using hi)) fun t ht => ?_
  simpa only [upd_ne _ _ (by decide : sCnt ≠ sK)] using ht

end VG.Proof.Rsa.X86.Recover
