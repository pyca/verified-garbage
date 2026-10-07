import VerifiedGarbage.Proof.Rsa.AArch64.CvHead
import VerifiedGarbage.Proof.Rsa.AArch64.CkPieces

/-!
# `vg_rsa_check_key` on AArch64: the header

`head` sets up the layout of `W = 2 w + 2` words (`wW k`) for
`w = ⌈k / 8⌉`: `W`, the arrays' bases, the stride and the mask all ones
(`ckHead_ok`).
-/

namespace VG.Proof.Rsa.AArch64

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Rsa.AArch64.Keys VG.Impl.Rsa.AArch64.CheckKey
open VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

/-- The layout's width for a `k`-byte modulus. -/
abbrev wW (k : Nat) : Nat := 2 * wk k + 2

theorem wide_val {k : Nat} (hk : k < 2 ^ 32) :
    (BitVec.ofNat 64 k + 7#64) >>> 3 + (BitVec.ofNat 64 k + 7#64) >>> 3 + 2#64 = BitVec.ofNat 64 (wW k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, wW, wk]
  omega

/-- `W` into `x12` and its slot. -/
theorem ckWide_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk2 : k ≤ 1024)
    (hZ : 8 * 32 ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block [ldh .x3 Public.sK, .addImm .x .x12 .x3 7, .lsr .x .x12 .x12 3, .add .x .x12 .x12 .x12,
      .addImm .x .x12 .x12 2, sth .x12 sW]) s fun t =>
        (t.gpr .x12 = BitVec.ofNat 64 (wW k) ∧ t.mem = s.mem.writeW (off B (8 * sW)) (BitVec.ofNat 64 (wW k))) ∧
        Keep [.x3, .x12] s t := by
  have hn := hs.nowrap
  refine WP.keep [.x3, .x12] ?_ (by decide) (by decide) (by decide +kernel)
  brun [h0, hdr_enc (show Public.sK < 32 by decide), hdr_enc (show sW < 32 by decide),
    hs.ld (d := 8 * Public.sK) (by unfold Public.sK sFn; omega), hs.st (d := 8 * sW) (by unfold sW; omega), hK,
    wide_val (show k < 2 ^ 32 by omega)]

/-- `head`: `W`, the arrays' bases, the stride, and the mask all ones. -/
theorem ckHead_ok {s : State} {B : Addr} {Z k : Nat} (hs : Scr s B Z) (h0 : s.gpr .x0 = B) (hk1 : 64 ≤ k)
    (hk2 : k ≤ 1024) (hZ : 128 * k ≤ Z) (hK : word s.mem B (8 * Public.sK) = BitVec.ofNat 64 k) :
    WP isa (.block VG.Impl.Rsa.AArch64.CheckKey.head) s fun t =>
      Ws t B Z (wW k) ∧ word t.mem B (8 * Public.sMask) = mask true ∧
      Frm B [(8 * sW, 8), (8 * sArr 0, 64), (8 * sStride, 8), (8 * Public.sMask, 8)] s.mem t.mem ∧
      Keep [.x3, .x4, .x7, .x12] s t := by
  have hn := hs.nowrap
  have hZ16 : slot (wW k) 16 ≤ Z := by unfold slot hdrBytes wW wk; omega
  have h8 := hdr_lt_slot (wW k) 8 (show 31 < 32 by decide)
  have eW : sW = 6 := rfl
  have eA : sArr 0 = 8 := rfl
  have eS : sStride = 28 := rfl
  have eM : Public.sMask = 22 := rfl
  have hl8 : slot (wW k) 8 ≤ slot (wW k) 16 := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide)) _
  unfold VG.Impl.Rsa.AArch64.CheckKey.head
  rw [List.append_assoc, WP.block_append_iff]
  refine WP.mono (ckWide_ok hs h0 hk2 (by omega) hK) fun t₀ ⟨⟨h12₀, hm₀⟩, k₀⟩ => ?_
  have hs₀ := hs.congr k₀.wr
  have h0₀ : t₀.gpr .x0 = B := (k₀.gpr .x0 (by decide)).trans h0
  rw [WP.block_append_iff]
  refine WP.mono (setBases_ok hs₀ h0₀ h12₀ (by unfold sArr; omega)) fun t₁ ⟨hb₁, ho₁, k₁⟩ => ?_
  have k01 := k₀.trans k₁
  have h12 : t₁.gpr .x12 = BitVec.ofNat 64 (wW k) := (k₁.gpr .x12 (by decide)).trans h12₀
  have hs₁ := hs.congr k01.wr
  have h0₁ : t₁.gpr .x0 = B := (k01.gpr .x0 (by decide)).trans h0
  refine WP.mono (WP.keep [.x3, .x4, .x7] (Q := fun t => t.gpr .x7 = 0 ∧ t.mem = (t₁.mem.writeW (off B (8 * sStride))
      (BitVec.ofNat 64 (8 * (wW k + 2)))).writeW (off B (8 * Public.sMask)) (mask true)) (by
    brun [h0₁, h12, hdr_enc (show sStride < 32 by decide), hdr_enc (show Public.sMask < 32 by decide),
      hs₁.st (d := 8 * sStride) (by omega), hs₁.st (d := 8 * Public.sMask) (by omega),
      ofNat_add_ofNat, shl_ofNat (show (wW k + 2) * 2 ^ 3 < 2 ^ 64 by simp only [wW, wk]; omega)]
    rw [show (wW k + 2) * 2 ^ 3 = 8 * (wW k + 2) by omega]
    rfl) (by decide) (by decide) (by decide +kernel)) fun t ⟨⟨_, hm⟩, k₂⟩ => ?_
  have o1 := writeW_outside t₁.mem B (BitVec.ofNat 64 (8 * (wW k + 2))) (d := 8 * sStride) (by omega)
  have o2 := writeW_outside (t₁.mem.writeW (off B (8 * sStride)) (BitVec.ofNat 64 (8 * (wW k + 2)))) B (mask true)
    (d := 8 * Public.sMask) (by omega)
  have o0 := writeW_outside s.mem B (BitVec.ofNat 64 (wW k)) (d := 8 * sW) (by omega)
  rw [← hm₀] at o0
  have hw : ∀ i < 32, i ≠ sStride → i ≠ Public.sMask → word t.mem B (8 * i) = word t₁.mem B (8 * i) :=
    fun i hi h1 h2 => by rw [hm, o2.word (by omega) (by omega), o1.word (by omega) (by omega)]
  have hW₁ : word t₁.mem B (8 * sW) = BitVec.ofNat 64 (wW k) := by
    rw [ho₁.word (by unfold sW sArr; omega) (by omega), hm₀, word_writeW_self]
  refine ⟨⟨hs₁.congr k₂.wr, (k₂.gpr .x0 (by decide)).trans h0₁, ?_, ?_, fun j hj => ?_, hZ16,
    show 2 ≤ wW k by simp only [wW]; omega, show wW k < 2 ^ 24 by simp only [wW, wk]; omega⟩,
    by rw [hm, word_writeW_self], ?_, (k01.trans k₂).mono (by simp)⟩
  · rw [hw sW (by decide) (by decide) (by decide)]; exact hW₁
  · rw [hm, o2.word (by omega) (by omega), word_writeW_self]
  · rw [hw (sArr j) (by unfold sArr; omega) (by unfold sArr sStride sFn; omega)
      (by unfold sArr Public.sMask sFn; omega)]
    exact hb₁ j hj
  · intro x hx
    have a := hx (8 * sW, 8) (by simp)
    have b := hx (8 * sArr 0, 64) (by simp)
    have c := hx (8 * sStride, 8) (by simp)
    have d := hx (8 * Public.sMask, 8) (by simp)
    dsimp only at a b c d
    rw [hm, o2 x d, o1 x c, ho₁ x b, o0 x a]

end VG.Proof.Rsa.AArch64
