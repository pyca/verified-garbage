module

public import VerifiedGarbage.Proof.RsaPss.AArch64.SignCall
public import VerifiedGarbage.Impl.RsaPss.AArch64.Encoding
public import VerifiedGarbage.Proof.MlKem.AArch64.Wp
import VerifiedGarbage.Proof.RsaPss.AArch64.MaskBits
import VerifiedGarbage.Proof.RsaPss.Params
import VerifiedGarbage.Proof.RsaPkcs1Sig.AArch64.Wp
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RSASSA-PSS on AArch64, around the encoding: the parameters

From the modulus' first byte `n₀ ≠ 0` in `x10` and its length `k` in `x23`,
`emBitsB` leaves `emBits = 8 (k - 1) + log₂ n₀` in `x24` (by `clz`),
`emLen = ⌈emBits / 8⌉` in `x25` and `lo = k - emLen` in `x26`
(`emBitsB_ok`); signing's `encArgs` then sets `encode`'s arguments
(`encArgs_ok`).
-/

@[expose] public section

namespace VG.Proof.RsaPss.AArch64

open VG VG.AArch64 VG.Impl.RsaPss.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep wp_nil wp_x wp_addImm wp_sub wp_lsr wp_lsl wp_movz wp_add wp_subImm wp_strb)
open VG.Proof.RsaPkcs1Sig.AArch64 (wp_ldrSp wp_mov)

theorem wp_clz {s : State} {is : List Instr} {Q : State → Prop} {d n : Reg}
    (k : ∀ s', Only [d] s s' → s'.gpr d = (s.gpr n).clz → WP isa (.block is) s' Q) :
    WP isa (.block (.clz .x d n :: is)) s Q :=
  wp_x (by simp [exec, State.read]) k

theorem clz_table : ∀ x < 256, x ≠ 0 →
    ∃ j < 8, 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) ∧ (BitVec.ofNat 64 x).clz = BitVec.ofNat 64 (63 - j) := by
  decide +kernel

theorem clz_val {x : Nat} (hx : x < 256) (h0 : x ≠ 0) :
    (BitVec.ofNat 64 x).clz = BitVec.ofNat 64 (63 - Nat.log2 x) := by
  obtain ⟨j, _, hl, hu, he⟩ := clz_table x hx h0
  rw [he, RsaPss.log2_eq h0 hl hu]

/-- `emBits` from the modulus' length and first byte. -/
def ebV (k x : Nat) : Nat := 8 * (k - 1) + Nat.log2 x

theorem shr3_ofNat {m : Nat} (hm : m < 2 ^ 64) : BitVec.ofNat 64 m >>> 3 = BitVec.ofNat 64 (m / 8) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (by omega)]

theorem emBitsB_ok {u : State} {k x : Nat} (hk1 : 1 ≤ k) (hk2 : k ≤ 1024) (hx : x < 256) (h0 : x ≠ 0)
    (h10 : u.gpr .x10 = BitVec.ofNat 64 x) (h23 : u.gpr .x23 = BitVec.ofNat 64 k) :
    WP isa (.block emBitsB) u fun u' => Only [.x9, .x24, .x25, .x26] u u' ∧
      u'.gpr .x24 = BitVec.ofNat 64 (ebV k x) ∧
      u'.gpr .x25 = BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)) ∧
      u'.gpr .x26 = BitVec.ofNat 64 (k - Spec.RsaPss.emLength (ebV k x)) := by
  have hl8 : Nat.log2 x < 8 := (Nat.log2_lt h0).mpr (by omega)
  have hel : Spec.RsaPss.emLength (ebV k x) ≤ k := by unfold Spec.RsaPss.emLength ebV; omega
  unfold emBitsB
  refine wp_clz fun u₁ o₁ e₁ => wp_lsl (by decide) fun u₂ o₂ e₂ => wp_addImm (by decide) fun u₃ o₃ e₃ =>
    wp_sub fun u₄ o₄ e₄ => wp_addImm (by decide) fun u₅ o₅ e₅ => wp_lsr (by decide) fun u₆ o₆ e₆ =>
    wp_sub fun u₇ o₇ e₇ => ?_
  have h24 : u₄.gpr .x24 = BitVec.ofNat 64 (ebV k x) := by
    rw [e₄, e₃, e₂, o₁.get .x23, h23, o₃.get .x9, o₂.get .x9, e₁, h10, clz_val hx h0,
      VG.Proof.RsaPss.AArch64.shl3_ofNat (by omega), BitVec.ofNat_add_ofNat, VG.Offset.ofNat_sub_ofNat (by omega)]
    unfold ebV; congr 1; omega
  have h25 : u₆.gpr .x25 = BitVec.ofNat 64 (Spec.RsaPss.emLength (ebV k x)) := by
    rw [e₆, e₅, h24, BitVec.ofNat_add_ofNat, shr3_ofNat (by unfold ebV; omega)]; rfl
  refine wp_nil ⟨(o₁.trans (o₂.trans (o₃.trans (o₄.trans (o₅.trans (o₆.trans o₇)))))).mono, ?_, ?_, ?_⟩
  · rw [o₇.get .x24, o₆.get .x24, o₅.get .x24, h24]
  · rw [o₇.get .x25, h25]
  · rw [e₇, o₆.get .x23, o₅.get .x23, o₄.get .x23, o₃.get .x23, o₂.get .x23, o₁.get .x23, h23, h25,
      VG.Offset.ofNat_sub_ofNat hel]

end VG.Proof.RsaPss.AArch64
