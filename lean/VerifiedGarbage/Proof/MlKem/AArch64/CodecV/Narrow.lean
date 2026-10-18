module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Lanes

/-!
# ML-KEM on AArch64: narrowing words to bytes

UZP1 of halfwords keeps the low halfword of each word (`narrow_h`), and UZP1 of bytes the low
byte of each halfword (`narrow_b`): together, the bytes of four registers of words less than
256, in order (`narrow4`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

theorem Lanes.chg {rs : List VReg} {s t : State} (c : VChg rs s t) {r : VReg} (hr : r ∉ rs)
    {f : Nat → Nat} (h : Lanes (s.v r) f) : Lanes (t.v r) f := by rw [c.get r hr]; exact h

theorem toNat_vhalf_word (x : BitVec 128) (j : Nat) : (vhalf x (2 * j)).toNat = (vword x j).toNat % 2 ^ 16 := by
  rw [← Ntt16.vword_lo, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]

theorem toNat_vbyte_half (x : BitVec 128) (j : Nat) : (vbyte x (2 * j)).toNat = (vhalf x j).toNat % 2 ^ 8 := by
  rw [Cbd16.half_bytes, BitVec.toNat_append, Nat.shiftLeft_eq]
  have := (vbyte x (2 * j)).isLt
  rw [Nat.or_comm, or_shift this]
  omega

/-- The halfwords of UZP1 of words. -/
theorem narrow_h {x y : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hy : Lanes y fun e => f (4 + e))
    {j : Nat} (hj : j < 8) : (vhalf (VPermOp.eval .uzp1 .h8 x y) j).toNat = f j % 2 ^ 16 := by
  rw [Ntt16.vhalf_perm_h8 _ _ _ hj]
  dsimp only
  split
  · rw [toNat_vhalf_word, hx j (by omega)]
  · rw [show 2 * j - 8 = 2 * (j - 4) by omega, toNat_vhalf_word, hy _ (by omega)]
    dsimp only
    rw [show 4 + (j - 4) = j by omega]

/-- The bytes of UZP1 of halfwords. -/
theorem narrow_b {x y : BitVec 128} {g : Nat → Nat} (hx : ∀ j < 8, (vhalf x j).toNat = g j)
    (hy : ∀ j < 8, (vhalf y j).toNat = g (8 + j)) {j : Nat} (hj : j < 16) :
    (vbyte (VPermOp.eval .uzp1 .b16 x y) j).toNat = g j % 2 ^ 8 := by
  rw [Blowfish.AArch64.vbyte_uzp1 _ _ hj]
  split
  · rw [toNat_vbyte_half, hx j (by omega)]
  · rw [show 2 * j - 16 = 2 * (j - 8) by omega, toNat_vbyte_half, hy _ (by omega),
      show 8 + (j - 8) = j by omega]

/-- The bytes of four registers of words less than 256. -/
theorem narrow4 {a b c d : BitVec 128} {f : Nat → Nat} (ha : Lanes a f) (hb : Lanes b fun e => f (4 + e))
    (hc : Lanes c fun e => f (8 + e)) (hd : Lanes d fun e => f (12 + e)) (hf : ∀ j < 16, f j < 256)
    {j : Nat} (hj : j < 16) :
    (vbyte (VPermOp.eval .uzp1 .b16 (VPermOp.eval .uzp1 .h8 a b) (VPermOp.eval .uzp1 .h8 c d)) j).toNat =
      f j := by
  rw [narrow_b (g := fun j => f j % 2 ^ 16) (fun j hj => narrow_h ha (hb.congr fun _ _ => rfl) hj)
    (fun j hj => narrow_h (f := fun e => f (8 + e)) hc
      (hd.congr fun e _ => by rw [← Nat.add_assoc]) hj) hj]
  have := hf j hj
  omega

/-- The low halfwords of UZP1 of words, from the first source alone. -/
theorem narrow_h_lo {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (y : BitVec 128) {j : Nat}
    (hj : j < 4) : (vhalf (VPermOp.eval .uzp1 .h8 x y) j).toNat = f j % 2 ^ 16 := by
  rw [Ntt16.vhalf_perm_h8 _ _ _ (by omega)]
  dsimp only
  rw [ite_eq_left hj, toNat_vhalf_word, hx j hj]

/-- The low bytes of UZP1 of halfwords, from the first source alone. -/
theorem narrow_b_lo {x : BitVec 128} {g : Nat → Nat} {n : Nat} (hn : n ≤ 8)
    (hx : ∀ j < n, (vhalf x j).toNat = g j) (y : BitVec 128) {j : Nat} (hj : j < n) :
    (vbyte (VPermOp.eval .uzp1 .b16 x y) j).toNat = g j % 2 ^ 8 := by
  rw [Blowfish.AArch64.vbyte_uzp1 _ _ (by omega), ite_eq_left (by omega), toNat_vbyte_half, hx j hj]

/-- The bytes of one register of words less than 256. -/
theorem narrow1 {x : BitVec 128} {f : Nat → Nat} (hx : Lanes x f) (hf : ∀ j < 4, f j < 256) {j : Nat}
    (hj : j < 4) :
    (vbyte (VPermOp.eval .uzp1 .b16 (VPermOp.eval .uzp1 .h8 x x) (VPermOp.eval .uzp1 .h8 x x)) j).toNat =
      f j := by
  rw [narrow_b_lo (n := 4) (g := fun j => f j % 2 ^ 16) (by decide) (fun j hj => narrow_h_lo hx x hj) _ hj]
  have := hf j hj
  omega

end VG.Proof.MlKem.AArch64.CodecV
