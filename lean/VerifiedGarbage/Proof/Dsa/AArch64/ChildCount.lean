module
public import VerifiedGarbage.Impl.Dsa.AArch64.Core
public import VerifiedGarbage.Proof.Bignum.AArch64.Run

import VerifiedGarbage.Proof.Bignum.AArch64.MontMul
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import Mathlib.Tactic.Push
import Mathlib.Tactic.Attr.Core
public import Aesop.BuiltinRules
import Mathlib.Tactic.ToDual
import VerifiedGarbage.Proof.Framework.Contract

/-! # Public child width and workspace selection -/

@[expose] public section

namespace VG.Proof.Dsa.AArch64
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64
open VG.Impl.Dsa.Layout VG.Impl.Dsa.AArch64
open VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64

abbrev childCount (offset : Nat) : List Instr :=
  ([mov .x1 .x0, ldh .x12 argLen, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3] : List Instr) ++ Core.enter offset

theorem childCount_ok {s : State} {B : Addr} {Z offset len : Nat}
    (hs : Scr s B Z) (hdi : s.gpr .x0 = B) (hZ : pWorkspace ≤ Z)
    (ho : offset < 2 ^ 16) (hlen : len < 2 ^ 32)
    (hl : word s.mem B (8 * argLen) = BitVec.ofNat 64 len) :
    WP isa (.block (childCount offset)) s fun t =>
      t.gpr .x1 = B ∧ t.gpr .x0 = off B offset ∧ t.gpr .x12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem ∧ Keep [.x1, .x0, .x12, .x4] s t := by
  refine WP.mono (WP.keep [.x1, .x0, .x12, .x4] (Q := fun t =>
      t.gpr .x1 = B ∧ t.gpr .x0 = off B offset ∧ t.gpr .x12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem) ?_ rfl rfl rfl) fun t ⟨⟨hsi, hd, h12, hm⟩, hk⟩ => ⟨hsi, hd, h12, hm, hk⟩
  unfold childCount Core.enter
  simp only [List.cons_append, List.nil_append]
  have hoff : (BitVec.ofNat 16 offset).setWidth 64 = BitVec.ofNat 64 offset := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hwidth : (BitVec.ofNat 64 len + (7#64)) >>> 3 = BitVec.ofNat 64 ((len + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.shiftRight_eq_div_pow]
    omega
  brun [hdi, hl, hdr_enc (show argLen < 32 by decide), hoff, hwidth,
    hs.ld (Nat.le_trans (show 8 * argLen + 8 ≤ pWorkspace by decide) hZ)]

end VG.Proof.Dsa.AArch64
