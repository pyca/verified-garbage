module

public import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Lane
import VerifiedGarbage.Proof.Framework.AArch64.StraightV

/-!
# ML-KEM on AArch64: doublewords of the vector codecs

Two words in a doubleword (`dpairV_ok`), as numbers (`DLanes`), and the bytes of a doubleword
(`toNat_vbyte_dword`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.CodecV

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem VG.Proof.MlKem.AArch64

/-- The doublewords of `x` are `g 0` and `g 1`. -/
def DLanes (x : BitVec 128) (g : Nat → Nat) : Prop := ∀ l < 2, (vdword x l).toNat = g l

theorem toNat_vword' (x : BitVec 128) (c : Nat) : (vword x c).toNat = x.toNat / 2 ^ (32 * c) % 2 ^ 32 := by
  simp [vword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem toNat_vdword' (x : BitVec 128) (e : Nat) : (vdword x e).toNat = x.toNat / 2 ^ (64 * e) % 2 ^ 64 := by
  simp [vdword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem vdword_words' (x : BitVec 128) (e : Nat) :
    (vdword x e).toNat = (vword x (2 * e)).toNat + 2 ^ 32 * (vword x (2 * e + 1)).toNat := by
  rw [toNat_vdword', toNat_vword', toNat_vword', show 32 * (2 * e) = 64 * e by omega,
    show 32 * (2 * e + 1) = 64 * e + 32 by omega, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize x.toNat / 2 ^ (64 * e) = n
  omega

/-- Byte `b` of doubleword `l`. -/
theorem toNat_vbyte_dword (x : BitVec 128) {l b : Nat} (hb : b < 8) :
    (vbyte x (8 * l + b)).toNat = (vdword x l).toNat / 2 ^ (8 * b) % 2 ^ 8 := by
  have : vbyte x (8 * l + b) = (vdword x l).extractLsb' (8 * b) 8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp [vbyte, vdword, hi, show 8 * b + i < 64 by omega, show 8 * (8 * l + b) + i = 64 * l + (8 * b + i) by omega]
  rw [this, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem not_shl_ones {sh : Nat} : ~~~(BitVec.allOnes 64 <<< sh) = BitVec.ofNat 64 (2 ^ sh - 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, hi, decide_true, Bool.true_and]
  by_cases h : i < sh <;> simp [h, show i - sh < 64 by omega]

/-- SLI of a doubleword. -/
theorem toNat_sli {a b : BitVec 64} {sh : Nat} (hsh : sh < 64) (hb : b.toNat * 2 ^ sh < 2 ^ 64) :
    ((a &&& ~~~(BitVec.allOnes 64 <<< sh)) ||| (b <<< sh)).toNat = a.toNat % 2 ^ sh + b.toNat * 2 ^ sh := by
  have hs : 2 ^ sh - 1 < 2 ^ 64 := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) hsh
    omega
  rw [not_shl_ones, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.and_two_pow_sub_one_eq_mod,
    or_shift (Nat.mod_lt _ (Nat.two_pow_pos sh))]

/-- The words of `d`, less than `2ᵇ`, paired in its doublewords. -/
theorem dpairV_ok {s : State} {b : Nat} {d : VReg} (hb : b < 32) (hd : d ≠ .v19) {p : Nat → Nat}
    (hx : Lanes (s.v d) p) (hp : ∀ e < 4, p e < 2 ^ b) :
    WP isa (.block (dpairV b d)) s fun t => VChg [.v19, d] s t ∧
      DLanes (t.v d) fun l => p (2 * l) + p (2 * l + 1) * 2 ^ b := by
  unfold dpairV
  refine wp_vop (eval_shift (by decide)) fun s1 h1 =>
    wp_vop (eval_shift (by simp only [VShiftOp.ok, VArr.esize]; simp; omega)) fun t h2 => wp_nil ⟨?_, ?_⟩
  · exact (h1.chg.trans h2.chg).mono (by
      intro r hr; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with h | h <;> simp [h])
  intro l hl
  rw [h2.v, h1.get d hd, h1.v, StraightV.vdword_map2 _ _ _ hl, StraightV.vdword_map2 _ _ _ hl]
  simp only [VShiftOp.eval]
  have w := vdword_words' (s.v d) l
  rw [hx _ (by omega), hx _ (by omega)] at w
  have hp0 := hp (2 * l) (by omega)
  have hp1 := hp (2 * l + 1) (by omega)
  have hb' : 2 ^ b ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  have u : ((vdword (s.v d) l) >>> 32).toNat = p (2 * l + 1) := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, w]; omega
  have hbb : 2 ^ b * 2 ^ b ≤ 2 ^ 64 := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
  have hlt : p (2 * l + 1) * 2 ^ b < 2 ^ 64 :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right hp1 (Nat.two_pow_pos b)) hbb
  rw [toNat_sli (by omega) (by rw [u]; exact hlt), u, w]
  have : 2 ^ 32 = 2 ^ b * 2 ^ (32 - b) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp0]

end VG.Proof.MlKem.AArch64.CodecV
