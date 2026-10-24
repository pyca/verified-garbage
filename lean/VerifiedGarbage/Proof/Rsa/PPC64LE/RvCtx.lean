module

public import VerifiedGarbage.Proof.Rsa.PPC64LE.RvFrame
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyOps
import VerifiedGarbage.Proof.Rsa.PPC64LE.KeyHalf
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.PPC64LE.Step

/-!
# `vg_rsa_recover_primes` on PPC64LE: the two views of the working space

`ctxW_ok`, `ctxw_ok`: from `w` digits to `W = 2 w + 2` and back, the
stride following; `zeroAll_ok`: every array zeroed.
-/

@[expose] public section

namespace VG.Proof.Rsa.PPC64LE.Recover

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.Rsa.PPC64LE.Keys
open VG.Impl.Rsa.PPC64LE.Recover (ctxW ctxw zeroAll nArr)
open VG.Proof.Rsa.KeyWorkspace (arr S)

theorem W_val (w : Nat) :
    BitVec.ofNat 64 w <<< 1 + BitVec.ofNat 64 2 = BitVec.ofNat 64 (2 * w + 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

theorem w_val (w : Nat) (hw : w ≤ 1024) :
    (BitVec.ofNat 64 (2 * w + 2) - 2#64) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  have e : BitVec.ofNat 64 (2 * w + 2) - 2#64 = BitVec.ofNat 64 (2 * w) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [e, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-- `ctxW`: `W = 2 w + 2` and its stride. -/
theorem ctxW_ok {s : State} {B : Addr} {Z w N N' : Nat} (h : Ws s B Z w N) (hW : 2 * w + 2 ≤ 1024)
    (fits : arr (2 * w + 2) N' ≤ Z) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z (2 * w + 2) N' → t.mem = s.mem → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ctxW ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r29, .r30] (Q := fun t => t.gpr .r29 = BitVec.ofNat 64 (2 * w + 2) ∧
    t.gpr .r30 = BitVec.ofNat 64 (S (2 * w + 2)) ∧ t.mem = s.mem) ?_ (by decide)) fun t ⟨⟨t29, t30, tm⟩, kt⟩ =>
      k t ⟨h.scr.congr kt.wr, fits, by omega, hW, t29, t30, (kt.gpr _ (by decide)).trans h.r31⟩ tm kt
  have := h.wle
  prun [ctxW, VG.Impl.Rsa.PPC64LE.Keys.stride, h.r29, W_val, stride_val]

/-- `ctxw`: back to `w` and its stride. -/
theorem ctxw_ok {s : State} {B : Addr} {Z w N N' : Nat} (h : Ws s B Z (2 * w + 2) N) (hw : 0 < w)
    (fits : arr w N' ≤ Z) {rest : List Instr} {Q : State → Prop}
    (k : ∀ t, Ws t B Z w N' → t.mem = s.mem → Keep [.r29, .r30] s t → WP isa (.block rest) t Q) :
    WP isa (.block (ctxw ++ rest)) s Q := by
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r29, .r30] (Q := fun t => t.gpr .r29 = BitVec.ofNat 64 w ∧
    t.gpr .r30 = BitVec.ofNat 64 (S w) ∧ t.mem = s.mem) ?_ (by decide)) fun t ⟨⟨t29, t30, tm⟩, kt⟩ =>
      k t ⟨h.scr.congr kt.wr, fits, hw, by have := h.wle; omega, t29, t30, (kt.gpr _ (by decide)).trans h.r31⟩ tm kt
  have := h.wle
  prun [ctxw, VG.Impl.Rsa.PPC64LE.Keys.stride, h.r29, w_val w (by omega), stride_val]

theorem digits_val (w : Nat) (hw : w ≤ 1024) :
    (BitVec.ofNat 64 44 * BitVec.ofNat 64 (S w)) >>> 2 = BitVec.ofNat 64 (nArr * (w + 2)) := by
  rw [← BitVec.ofNat_mul]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  simp only [S, nArr]
  rw [Nat.mod_eq_of_lt (show 44 * (4 * (w + 2)) < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 44 * (w + 2) < 2 ^ 64 by omega)]
  omega

/-- `zeroAll`: the digits of the arrays `0`–`nArr - 1` := 0. -/
theorem zeroAll_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (fits : arr w nArr ≤ Z) :
    WP isa zeroAll s fun t => Ws t B Z w N ∧ (∀ i < nArr * (w + 2), w32 t.mem B (160 + 4 * i) = 0) ∧
      Outside B 160 (4 * (nArr * (w + 2))) s.mem t.mem ∧ Keep opRegs s t := by
  have := h.wle
  rw [zeroAll, WP.seq_iff]
  refine WP.mono (WP.keep [.r8] (Q := fun t => t.gpr .r8 = BitVec.ofNat 64 (nArr * (w + 2)) ∧ t.mem = s.mem)
    (by prun [nArr, h.r30, digits_val w (by omega)]) (by decide)) fun u ⟨⟨u8, um⟩, ku⟩ => ?_
  refine WP.mono (zeroArrays_ok (h.of_keep ku) u8 (by simp only [nArr]; omega) (by simp only [nArr]; omega)
    (by
      have e : 160 + 4 * (nArr * (w + 2)) = arr w nArr := by
        simp only [arr, S, VG.Proof.Rsa.KeyWorkspace.hdr]; rw [Nat.mul_left_comm]
      rw [e]; exact fits))
    fun t ⟨ht, z, out, kt⟩ => ⟨ht, z, by rw [← um]; exact out, (ku.trans kt).mono⟩

end VG.Proof.Rsa.PPC64LE.Recover
