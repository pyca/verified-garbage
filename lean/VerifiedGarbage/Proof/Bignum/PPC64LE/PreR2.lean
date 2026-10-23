module

import VerifiedGarbage.Proof.Bignum.PPC64LE.MontRound
import VerifiedGarbage.Proof.Bignum.PPC64LE.MontFinish
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreDouble
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute
public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Mont.Words32

/-!
# The precomputed values of an RSA modulus on PPC64LE: `R² mod n`

`one_ok`: `x := 1`. `r2_ok`: `x := 2^(128 w) mod n`, by `128 w` doublings.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Precompute

/-- `one`, `x` at `dX` (`r5`) with `2 w` in `r11`: its `2 w` digits are 1. -/
theorem one_ok {s : State} {B : Addr} {Z dX w : Nat} (hs : Scr s B Z)
    (h5 : s.gpr .r5 = off B dX) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w)
    (hw' : w < 2 ^ 31) (hZ : dX + 8 * w ≤ Z) :
    WP isa one s fun t =>
      val32 t.mem B dX (2 * w) = 1 ∧ Mont.Outside B dX (8 * w) s.mem t.mem ∧ Keep [.r0, .r14, .r17] s t := by
  have hnw := hs.nowrap
  unfold one
  refine WP.seq ?_
  have hpre : WP isa (.block [.addi .r14 .r5 0]) s fun s₁ =>
      (s₁.gpr .r14 = off B dX ∧ s₁.mem = s.mem) ∧ Keep [.r14] s s₁ := by
    refine WP.keep _ ?_ (by decide)
    prun [h5]
  refine WP.mono hpre fun s₁ ⟨⟨i14, im⟩, k₁⟩ => ?_
  refine WP.seq (WP.mono (zeroWords_ok (hs.congr k₁.wr) i14 ((k₁.gpr _ (by decide)).trans h11)
    hw hw' hZ) fun s₂ ⟨⟨_, hz, out₂⟩, k₂⟩ => ?_)
  have k12 := k₁.trans k₂
  have hfin : WP isa (.block [.li .r0 1, .store .w .r0 .r5 0]) s₂ fun t =>
      (t.mem = s₂.mem.writeW (off B dX) ((1 : BitVec 64).setWidth 32)) ∧ Keep [.r0] s₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun [k12.gpr .r5 (by decide), h5, BitVec.add_zero, (hs.congr k12.wr).st (d := dX) (n := 4) (by omega)]
    rfl
  refine WP.mono hfin fun t ⟨tm, k₃⟩ => ⟨?_, ?_, (k12.trans k₃).mono⟩
  · have hz32 : ∀ j < 2 * w, w32 s₂.mem B (dX + 4 * j) = 0 := fun j hj => by
      have hword := word_eq_w32 s₂.mem B (dX + 8 * (j / 2))
      rw [hz (j / 2) (by omega)] at hword
      have : w32 s₂.mem B (dX + 8 * (j / 2)) = 0 ∧ w32 s₂.mem B (dX + 8 * (j / 2) + 4) = 0 := by
        rw [show (0 : BitVec 64).toNat = 0 from rfl] at hword; omega
      rcases Nat.mod_two_eq_zero_or_one j with h | h
      · rw [show dX + 4 * j = dX + 8 * (j / 2) by omega]; exact this.1
      · rw [show dX + 4 * j = dX + 8 * (j / 2) + 4 by omega]; exact this.2
    have ho := writeW32_outside s₂.mem B (d := dX) ((1 : BitVec 64).setWidth 32) (by omega)
    have e := val32_append (s₂.mem.writeW (off B dX) ((1 : BitVec 64).setWidth 32)) B dX 1 (2 * w - 1)
    rw [show 1 + (2 * w - 1) = 2 * w by omega] at e
    have hrest : val32 (s₂.mem.writeW (off B dX) ((1 : BitVec 64).setWidth 32)) B (dX + 4 * 1) (2 * w - 1) = 0 := by
      rw [ho.val32 (by omega) (by omega)]
      exact val32_zero fun j hj => by
        rw [show dX + 4 * 1 + 4 * j = dX + 4 * (j + 1) by omega]; exact hz32 _ (by omega)
    have h1 := val32_succ (s₂.mem.writeW (off B dX) ((1 : BitVec 64).setWidth 32)) B dX 0
    rw [show dX + 4 * 0 = dX from rfl, w32_write_self] at h1
    rw [tm, e, hrest, Nat.mul_zero, Nat.add_zero, h1]
    rfl
  · rw [tm]
    rw [im] at out₂
    exact out₂.trans
      ((writeW32_outside s₂.mem B (d := dX) _ (by omega)).mono (by omega) (by omega))

theorem shl6_ofNat (w : Nat) : BitVec.ofNat 64 (2 * w) <<< 6 = BitVec.ofNat 64 (128 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- `r2`, in the arrays of `vg_rsa_mont_mul` with `n > 1` in array 0: `x`
(array 1) `:= 2^(128 w) mod n`, changing only arrays 1–3. -/
theorem r2_ok {s : State} {B : Addr} {Z w : Nat} (hs : Scr s B Z)
    (h8 : s.gpr .r8 = off B (slot w 2)) (h9 : s.gpr .r9 = off B (slot w 3))
    (h10 : s.gpr .r10 = off B (slot w 0)) (h5 : s.gpr .r5 = off B (slot w 1))
    (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * w)) (hw : 1 ≤ w) (hw' : w < 2 ^ 31) (hZ : slot w 4 ≤ Z)
    (hN : 2 ≤ val32 s.mem B (slot w 0) (2 * w)) :
    WP isa r2 s fun t =>
      val32 t.mem B (slot w 1) (2 * w) = 2 ^ (128 * w) % val32 s.mem B (slot w 0) (2 * w) ∧
      Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
      Keep [.r0, .r3, .r4, .r14, .r15, .r16, .r17, .r20] s t := by
  have hnw := hs.nowrap
  have e : ∀ j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e4 := e 4
  unfold r2
  refine WP.seq (WP.mono (one_ok hs h5 h11 hw hw' (by omega)) fun s₁ ⟨h1, out₁, k₁⟩ => ?_)
  refine WP.seq ?_
  have hpre : WP isa (.block [.lsl .r4 .r11 6]) s₁ fun s₂ =>
      (s₂.gpr .r4 = BitVec.ofNat 64 (128 * w) ∧ s₂.mem = s₁.mem) ∧ Keep [.r4] s₁ s₂ := by
    refine WP.keep _ ?_ (by decide)
    prun [k₁.gpr .r11 (by decide), h11, shl6_ofNat]
  refine WP.mono hpre fun s₂ ⟨⟨i4, im⟩, k₂⟩ => ?_
  have k12 := k₁.trans k₂
  let N := val32 s.mem B (slot w 0) (2 * w)
  let Inv : Nat → State → Prop := fun i t =>
    val32 t.mem B (slot w 1) (2 * w) = 2 ^ i % N ∧ Mont.Outside B (slot w 1) (24 * (w + 2)) s.mem t.mem ∧
      Keep [.r0, .r3, .r4, .r14, .r15, .r16, .r17, .r20] s t
  refine wp_countdown (N := 128 * w) (by omega) (by omega) Inv (fun i _ t ⟨jv, jout, jk⟩ _ => ?_)
    ⟨by rw [im, h1, Nat.pow_zero, Nat.mod_eq_of_lt (by omega)],
      by rw [im]; exact out₁.mono (by omega) (by omega), k12.mono⟩ i4
  have hNt : val32 t.mem B (slot w 0) (2 * w) = N := jout.val32 (by omega) (by omega)
  refine WP.seq (WP.mono (doubleMod_ok (hs.congr jk.wr) (by rw [jk.gpr .r8 (by decide), h8])
    (by rw [jk.gpr .r9 (by decide), h9]) (by rw [jk.gpr .r10 (by decide), h10])
    (by rw [jk.gpr .r5 (by decide), h5]) (by rw [jk.gpr .r11 (by decide), h11]) hw hw' (by omega)
    (by rw [jv, hNt]; exact Nat.mod_lt _ (by omega))) fun t₂ ⟨hv, out₂, k₂⟩ => ?_)
  refine WP.mono (subi_ok t₂ .r4 (by decide)) fun t₃ e3 => ?_
  subst e3
  refine ⟨⟨?_, jout.trans out₂, ((jk.trans k₂).trans (Keep.write _ _ _)).mono⟩,
    by gsimp; rw [k₂.gpr .r4 (by decide)]⟩
  rw [mem_write, hv, jv, hNt, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.pow_succ, Nat.mul_comm]

end VG.Proof.Bignum.PPC64LE
