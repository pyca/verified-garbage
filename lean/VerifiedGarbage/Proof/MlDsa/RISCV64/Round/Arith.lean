module

public import VerifiedGarbage.Impl.MlDsa.RISCV64.Round
public import VerifiedGarbage.Proof.MlDsa.Round.Decompose

/-!
# ML-DSA on RISCV64: what the rounding code computes

The values the pieces of `Impl/MlDsa/RISCV64/Round.lean` leave, for a
coefficient `a < q` and `γ₂` in `gamma2s`:

* `fixup` leaves `fixk k u`: `u + k` if `u` is negative, `u` otherwise
  (`fixk_toNat`);
* `hbRaw g` leaves `hbr g a = ⌊(a + γ₂ - 1)/(2γ₂)⌋` (`hbr_toNat`, by `hbF_eq`
  of `Proof/MlDsa/Round/Decompose.lean`), and `hb g` its remainder modulo `m`
  (`hbv_toNat`);
* `power2Round`'s two values (`p2r1_toNat`, `p2r0_toNat`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.RISCV64.Round

open VG VG.RISCV64 VG.Impl.MlDsa.RISCV64.Round
open VG.Spec.MlDsa (q gamma2s)
open VG.Proof.MlDsa.Round (hbF hbM q_eq mem_gamma2s hbF_le hbF_eq)

/-- What `fixup u t rk` leaves for `k` in `rk`. -/
def fixk (k u : BitVec 64) : BitVec 64 := u + (u.sshiftRight 63 &&& k)

/-- The mask `fixup` adds: `k` if `u` is negative, else 0. -/
theorem fixk_eq (k u : BitVec 64) : fixk k u = u + (u >>> 63) * k := by
  unfold fixk
  cases hm : u.msb
  · have hu : u.toNat < 2 ^ 63 := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : u >>> 63 = 0#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_false hm, h0, BitVec.zero_and, BitVec.zero_mul]
  · have hu : 2 ^ 63 ≤ u.toNat := by
      have := BitVec.msb_eq_decide u; rw [hm] at this; simp at this; omega
    have h0 : (~~~u) >>> 63 = 0#64 := by bv_omega
    have h1 : u >>> 63 = 1#64 := by bv_omega
    rw [BitVec.sshiftRight_eq_of_msb_true hm, h0, BitVec.not_zero, BitVec.allOnes_and, h1, BitVec.one_mul]

theorem fixk_toNat {k : Nat} (hk : k < 2 ^ 62) {u : BitVec 64} (h : u.toNat < k ∨ 18446744073709551616 - k ≤ u.toNat) :
    (fixk (BitVec.ofNat 64 k) u).toNat = if u.toNat < k then u.toNat else u.toNat + k - 18446744073709551616 := by
  rw [fixk_eq]
  have hs : u >>> 63 = 0 ∨ u >>> 63 = 1 := by bv_omega
  rcases hs with hs | hs <;> rw [hs] <;> split <;> bv_omega

/-- `fixk k (x - k)` of `x < 2k`: `x` reduced modulo `k`. -/
theorem fixk_sub {k : Nat} (hk : 0 < k) (hk2 : k < 2 ^ 62) {x : BitVec 64} (hx : x.toNat < 2 * k) :
    (fixk (BitVec.ofNat 64 k) (x - BitVec.ofNat 64 k)).toNat = x.toNat % k := by
  rw [fixk_toNat hk2 (by bv_omega)]
  by_cases h : x.toNat < k
  · rw [Nat.mod_eq_of_lt h]; split <;> bv_omega
  · rw [show x.toNat % k = x.toNat - k by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]
    split <;> bv_omega

/-- `fixk k (a - b)`: `a - b` if it is not negative, else `a + k - b`. -/
theorem fixk_diff {k : Nat} (hk2 : k < 2 ^ 62) {a b : BitVec 64} (ha : a.toNat < 2 ^ 62) (hb : b.toNat ≤ a.toNat + k)
    (hb' : b.toNat < 2 ^ 62) :
    (fixk (BitVec.ofNat 64 k) (a - b)).toNat = if a.toNat < b.toNat then a.toNat + k - b.toNat else a.toNat - b.toNat := by
  rw [fixk_eq]
  have hs : (a - b) >>> 63 = 0 ∨ (a - b) >>> 63 = 1 := by bv_omega
  rcases hs with hs | hs <;> rw [hs] <;> split <;> bv_omega

/-- `loadImm` of `4095`, as instructions with their immediates. -/
theorem loadImm_4095 (r : Reg) : VG.Impl.MlDsa.RISCV64.Arith.loadImm r 4095 = [.lui r 1, .addi r r (-1)] := by
  simp only [VG.Impl.MlDsa.RISCV64.Arith.loadImm, VG.Impl.MlDsa.RISCV64.Arith.hi20]; rfl

/-! ## `Decompose` -/

/-- What `hbRaw g d` leaves for `a` in `d`. -/
def hbr (g : Nat) (a : BitVec 64) : BitVec 64 :=
  ((a + 127) >>> 7 * BitVec.ofNat 64 (dMul g) + BitVec.ofNat 64 (dAdd g)) >>> dShift g

/-- What `hb g d t` leaves for `a` in `d`. -/
def hbv (g : Nat) (a : BitVec 64) : BitVec 64 :=
  fixk (BitVec.ofNat 64 (dMod g)) (hbr g a - BitVec.ofNat 64 (dMod g))

theorem dMod_eq {g : Nat} (hg : g ∈ gamma2s) : dMod g = hbM g := by
  rcases mem_gamma2s hg with rfl | rfl <;> rfl

theorem dMod_pos {g : Nat} (hg : g ∈ gamma2s) : 0 < dMod g ∧ dMod g < 64 := by
  rcases mem_gamma2s hg with rfl | rfl <;> decide

theorem dShift_lt (g : Nat) : dShift g < 64 := by
  unfold dShift; split <;> decide

theorem dMul_eq {g : Nat} (hg : g ∈ gamma2s) :
    dMul g = VG.Proof.MlDsa.Round.hbMul g ∧ dAdd g = VG.Proof.MlDsa.Round.hbAdd g ∧
      dShift g = VG.Proof.MlDsa.Round.hbShift g ∧ dMul g ≤ 11275 ∧ dAdd g ≤ 2 ^ 23 := by
  rcases mem_gamma2s hg with rfl | rfl <;> decide

theorem hbr_toNat {g : Nat} (hg : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < q) :
    (hbr g a).toNat = hbF g a.toNat := by
  rw [hbF_eq hg ha]
  rw [q_eq] at ha
  obtain ⟨e1, e2, e3, b1, b2⟩ := dMul_eq hg
  have h1 : (a + 127).toNat = a.toNat + 127 := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by rw [show (127 : BitVec 64).toNat = 127 from rfl]; omega)
  have h2 : ((a + 127) >>> 7).toNat = (a.toNat + 127) / 128 := by
    rw [BitVec.toNat_ushiftRight, h1, Nat.shiftRight_eq_div_pow]
  have h3 : ((a + 127) >>> 7 * BitVec.ofNat 64 (dMul g)).toNat = (a.toNat + 127) / 128 * dMul g := by
    rw [BitVec.toNat_mul, h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : dMul g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul (Nat.le_refl _) b1) (by omega))
  have h4 : ((a + 127) >>> 7 * BitVec.ofNat 64 (dMul g) + BitVec.ofNat 64 (dAdd g)).toNat =
      (a.toNat + 127) / 128 * dMul g + dAdd g := by
    rw [BitVec.toNat_add, h3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : dAdd g < 2 ^ 64)]
    exact Nat.mod_eq_of_lt (by
      have := Nat.mul_le_mul (Nat.le_refl ((a.toNat + 127) / 128)) b1
      omega)
  unfold hbr
  rw [BitVec.toNat_ushiftRight, h4, Nat.shiftRight_eq_div_pow, e1, e2, e3]

theorem hbv_toNat {g : Nat} (hg : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < q) :
    (hbv g a).toNat = hbF g a.toNat % hbM g := by
  have hf := hbF_le hg ha
  have hr := hbr_toNat hg ha
  obtain ⟨m0, m64⟩ := dMod_pos hg
  have hm := dMod_eq hg
  unfold hbv
  rw [← hm, ← hr, fixk_sub m0 (by omega) (by rw [hr]; omega)]

theorem hbv_lt {g : Nat} (hg : g ∈ gamma2s) {a : BitVec 64} (ha : a.toNat < q) : (hbv g a).toNat < 64 := by
  rw [hbv_toNat hg ha, ← dMod_eq hg]
  exact Nat.lt_trans (Nat.mod_lt _ (dMod_pos hg).1) (dMod_pos hg).2

end VG.Proof.MlDsa.RISCV64.Round
