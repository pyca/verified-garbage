module
public import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcWord

import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcStore
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Bignum.AArch64.MulAdd
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec

@[expose] public section

namespace VG.Proof.Bignum.AArch64.BlockedRedc
open VG VG.AArch64 VG.Impl.Bignum.AArch64 VG.Proof.Bignum
open VG.Proof.Bignum.AArch64 VG.Proof.Ed25519.Word64
open VG.Proof.MlKem.AArch64 (Keep)

theorem captureCarry_ok {s : State} (h7 : s.gpr .x7 = 0) :
    WP isa (.block [.adc .x .x10 .x7 .x7]) s fun t =>
      (t.gpr .x10 = BitVec.ofNat 64 s.c.toNat ∧ t.mem = s.mem) ∧ Keep [.x10] s t := by
  refine WP.keep [.x10] ?_ rfl rfl rfl
  brun [h7]
  simp only [zero_add64]

/-- The last column incorporates the previous pending bit and saves the new
one; the full addition remains represented even for malformed inverses. -/
theorem finishBlock_ok {s : State} {B : Addr} {Z eT : Nat} {p : Bool}
    (hs : Scr s B Z) (h16 : s.gpr .x16 = off B eT) (hT : eT + 64 ≤ Z)
    (h10 : s.gpr .x10 = BitVec.ofNat 64 p.toNat) (h7 : s.gpr .x7 = 0) :
    WP isa (.block (VG.Impl.Bignum.AArch64.BlockedRedc.addMemory true ++
      ([.adc .x .x10 .x7 .x7] : List Instr) ++ VG.Impl.Bignum.AArch64.BlockedRedc.asStore)) s fun t =>
      wv t.mem B eT 8 + (2 ^ 64) ^ 8 * (t.gpr .x10).toNat =
        blockValue (accumulator s) + wv s.mem B eT 8 + p.toNat ∧
      (t.gpr .x10).toNat ≤ 1 ∧ Outside B eT 64 s.mem t.mem ∧
      Keep (VG.Impl.Bignum.AArch64.BlockedRedc.aa ++ ([.x1, .x10, .x13] : List Reg)) s t := by
  rewrite [List.append_assoc]
  apply WP.block_append
  refine WP.mono (addMemory_pending_value hs h16 hT h10) fun a ⟨⟨ha, ham⟩, ka⟩ => ?_
  apply WP.block_append
  refine WP.mono (captureCarry_ok ((ka.gpr .x7 (by decide)).trans h7))
    fun b ⟨⟨hb10, hbm⟩, kb⟩ => ?_
  have kab := ka.trans kb
  refine WP.mono (asStore_ok (hs.congr kab.wr)
    ((kab.gpr .x16 (by decide)).trans h16) hT) fun t ⟨htv, hto, kt, _⟩ => ?_
  have h10' := (kt.gpr .x10 (by decide)).trans hb10
  have hc : (t.gpr .x10).toNat = a.c.toNat := by
    have hn := congrArg BitVec.toNat h10'
    exact hn.trans (Nat.mod_eq_of_lt (by have := Bool.toNat_le a.c; omega))
  have hv := htv.trans (congrArg blockValue (keep_accumulator kb (by decide)))
  refine ⟨?_, ?_, ?_, ((kab.trans kt).mono (by decide))⟩
  · exact ((congrArg (· + (2 ^ 64) ^ 8 * (t.gpr .x10).toNat) hv).trans
      (congrArg (fun c => blockValue (accumulator a) + (2 ^ 64) ^ 8 * c) hc)).trans ha
  · exact Nat.le_trans (Nat.le_of_eq hc) (Bool.toNat_le a.c)
  · intro x hx
    exact (hto x hx).trans (congrArg (fun m : Mem => m x) (hbm.trans ham))

end VG.Proof.Bignum.AArch64.BlockedRedc
