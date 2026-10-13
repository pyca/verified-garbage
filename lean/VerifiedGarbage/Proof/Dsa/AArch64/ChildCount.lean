module

public import VerifiedGarbage.Proof.Dsa.AArch64.EnterLeave
public import VerifiedGarbage.Proof.Bignum.AArch64.PubSetup
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic
import VerifiedGarbage.Proof.Framework.AArch64.Call

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
      t.mem = s.mem ∧ Keep [.x1, .x0, .x12, .x3] s t := by
  refine WP.mono (WP.keep [.x1, .x0, .x12, .x3] (Q := fun t =>
      t.gpr .x1 = B ∧ t.gpr .x0 = off B offset ∧ t.gpr .x12 = BitVec.ofNat 64 ((len + 7) / 8) ∧
      t.mem = s.mem) ?_ rfl rfl rfl) fun t ⟨⟨hsi, hd, h12, hm⟩, hk⟩ => ⟨hsi, hd, h12, hm, hk⟩
  unfold childCount Core.enter
  simp only [List.cons_append, List.nil_append]
  brun [hdi, hl, hdr_enc (show argLen < 32 by decide),
    hs.ld (Nat.le_trans (show 8 * argLen + 8 ≤ pWorkspace by decide) hZ), shr3_w len hlen, movz_ofNat ho]

end VG.Proof.Dsa.AArch64
