module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The RSA private-key operation on PPC64LE: a prime's working space

`words_ok`: `max(2, ⌈len / 8⌉)` (`wsWords`). `setupP_ok`: the registers of
a prime's working space, from its base and length in the header.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem words_val {u : Nat} (hu : 1 ≤ u) (hu' : u < 2 ^ 62) :
    BitVec.ofNat 64 u + (BitVec.ofNat 64 u - BitVec.ofNat 64 2) >>> 63 = BitVec.ofNat 64 (max 2 u) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  rcases (show u = 1 ∨ 2 ≤ u by omega_arith) with rfl | h
  · decide
  · rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 2 < 2 ^ 64 by decide),
      show 2 ^ 64 - 2 + u = (u - 2) + 2 ^ 64 by omega_arith, Nat.add_mod_right,
      Nat.mod_eq_of_lt (show u - 2 < 2 ^ 64 by omega_arith), Nat.div_eq_of_lt (show u - 2 < 2 ^ 63 by omega_arith),
      Nat.add_zero, Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show max 2 u < 2 ^ 64 by omega_arith)]
    omega_arith

/-- `words r4 r3`, `len ≥ 1` in `r3`: `r4 := wsWords len`. -/
theorem words_ok {s : State} {len : Nat} (h3 : s.gpr .r3 = BitVec.ofNat 64 len) (hl : 1 ≤ len)
    (hl' : len < 2 ^ 60) :
    WP isa (.block (words .r4 .r3)) s fun t =>
      (t.gpr .r4 = BitVec.ofNat 64 (wsWords len) ∧ t.mem = s.mem) ∧ Keep [.r4, .r0] s t := by
  refine WP.keep _ ?_ (by decide)
  have e : (BitVec.ofNat 64 len + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((len + 7) / 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show len < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 7 < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show len + 7 < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
  prun [words, h3, e]
  exact words_val (by omega_arith) (by omega_arith)

theorem wsWords_lt {len : Nat} (hl' : len < 2 ^ 60) : wsWords len < 2 ^ 58 := by unfold wsWords; omega_arith

theorem shl_ofNat {w k : Nat} (h : w * 2 ^ k < 2 ^ 64) : BitVec.ofNat 64 w <<< k = BitVec.ofNat 64 (w * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (show w < 2 ^ 64 from Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) h),
    Nat.mod_eq_of_lt h]

/-- `area r3`, a working space's base in `r3` and its words in `r4`. -/
theorem area_ok {s : State} {A : Addr} {w : Nat} (h3 : s.gpr .r3 = A) (h4 : s.gpr .r4 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 58) :
    WP isa (.block (area .r3)) s fun t =>
      (t.gpr .r10 = off A (slot w 0) ∧ t.gpr .r21 = off A (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.mem = s.mem) ∧
      Keep [.r10, .r21, .r29, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  have e0 : off A (slot w 0) = A + BitVec.ofNat 64 256 := by
    simp only [off, slot, Nat.zero_mul, Nat.add_zero]; rfl
  have e29 : BitVec.ofNat 64 (w * 2 ^ 3) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]; congr 1; omega_arith
  prun [area, h3, h4, hdrBytes, shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega_arith),
    shl_ofNat (show w * 2 ^ 1 < 2 ^ 64 by omega_arith), BitVec.add_zero]
  exact ⟨e0.symm, e0.symm, e29, by congr 1; omega_arith⟩

/-- `setupP oB oLen`: a prime's working space at `off BX oA` (the header's
word `oB`) for its length `len` (word `oLen`). -/
theorem setupP_ok {s : State} {BX : Addr} {Z oA len oB oLen : Nat} (hs : Scr s BX Z) (h23 : s.gpr .r23 = BX)
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hZ : 256 ≤ Z)
    (hB : word s.mem BX oB = off BX oA) (hL : word s.mem BX oLen = BitVec.ofNat 64 len) (hl : 1 ≤ len)
    (hl' : len < 2 ^ 60) :
    WP isa (.block (setupP oB oLen)) s fun t =>
      (t.gpr .r10 = off (off BX oA) (slot (wsWords len) 0) ∧ t.gpr .r21 = off (off BX oA) (slot (wsWords len) 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (wsWords len + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords len) ∧
        t.gpr .r4 = BitVec.ofNat 64 (wsWords len) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r3, .r4, .r10, .r11, .r21, .r29] s t := by
  unfold setupP
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = BitVec.ofNat 64 len ∧ t.mem = s.mem) (by
    prun [h23, exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oLen < 2 ^ 15 by omega_arith, show oLen % 4 = 0 by omega_arith⟩,
      hs.ld (show oLen + 8 ≤ Z by omega_arith)]
    exact hL) rfl) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (words_ok a3 hl hl') fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r3] (Q := fun t => t.gpr .r3 = off BX oA ∧ t.mem = s.mem) (by
    prun [(k12.gpr _ (by decide)).trans h23,
      exec_load_d (show Reg.r23 ≠ .r0 by decide) ⟨show oB < 2 ^ 15 by omega_arith, show oB % 4 = 0 by omega_arith⟩,
      (hs.congr k12.wr).ld (show oB + 8 ≤ Z by omega_arith), m2, m1]
    exact hB) rfl) fun s₃ ⟨⟨a3', m3⟩, k3⟩ => ?_
  refine WP.mono (area_ok a3' ((k3.gpr _ (by decide)).trans a4) (wsWords_lt hl'))
    fun t ⟨⟨t10, t21, t29, t11, tm⟩, k4⟩ => ⟨⟨t10, t21, t29, t11, ?_, by rw [tm, m3]⟩, ((k12.trans k3).trans k4).mono⟩
  rw [k4.gpr _ (by decide), k3.gpr _ (by decide), a4]

/-- `area r23`, the working space at `r23`, its words in `r4`. -/
theorem area23_ok {s : State} {A : Addr} {w : Nat} (h23 : s.gpr .r23 = A) (h4 : s.gpr .r4 = BitVec.ofNat 64 w)
    (hw : w < 2 ^ 58) :
    WP isa (.block (area .r23)) s fun t =>
      (t.gpr .r10 = off A (slot w 0) ∧ t.gpr .r21 = off A (slot w 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (w + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * w) ∧ t.mem = s.mem) ∧
      Keep [.r10, .r21, .r29, .r11] s t := by
  refine WP.keep _ ?_ (by decide)
  have e0 : off A (slot w 0) = A + BitVec.ofNat 64 256 := by
    simp only [off, slot, Nat.zero_mul, Nat.add_zero]; rfl
  have e29 : BitVec.ofNat 64 (w * 2 ^ 3) + BitVec.ofNat 64 16 = BitVec.ofNat 64 (8 * (w + 2)) := by
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add]; congr 1; omega_arith
  prun [area, h23, h4, hdrBytes, shl_ofNat (show w * 2 ^ 3 < 2 ^ 64 by omega_arith),
    shl_ofNat (show w * 2 ^ 1 < 2 ^ 64 by omega_arith), BitVec.add_zero]
  exact ⟨e0.symm, e0.symm, e29, by congr 1; omega_arith⟩

/-- `setupX`, `k` in `r6`, the working space at `r23` with `p`'s length in
its header: `X`'s registers (`w_X = 2 ⌈k / 8⌉` words) and the bases of `P`
and `Q`, after `X` and after `P`, in the header. -/
theorem setupX_ok {s : State} {S : Addr} {Z k pL : Nat} (hs : Scr s S Z) (hZ : 256 ≤ Z) (h23 : s.gpr .r23 = S)
    (h6 : s.gpr .r6 = BitVec.ofNat 64 k) (hk : k ≤ 1024) (hPL : word s.mem S oPLen = BitVec.ofNat 64 pL)
    (hp : 1 ≤ pL) (hp' : pL < 2 ^ 60) :
    WP isa (.block setupX) s fun t =>
      (t.gpr .r10 = off S (slot (2 * ((k + 7) / 8)) 0) ∧ t.gpr .r21 = off S (slot (2 * ((k + 7) / 8)) 0) ∧
        t.gpr .r29 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)) ∧
        t.gpr .r11 = BitVec.ofNat 64 (2 * (2 * ((k + 7) / 8))) ∧
        t.gpr .r27 = off S (slot (2 * ((k + 7) / 8)) 0) ∧ t.gpr .r28 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)) ∧
        word t.mem S oBP = off S (slot (2 * ((k + 7) / 8)) 8) ∧
        word t.mem S oBQ = off S (slot (2 * ((k + 7) / 8)) 8 + slot (wsWords pL) 8) ∧
        Outside S 96 16 s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r5, .r10, .r11, .r21, .r27, .r28, .r29] s t := by
  have hn := hs.nowrap
  unfold setupX
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r4] (Q := fun t => t.gpr .r4 = BitVec.ofNat 64 (2 * ((k + 7) / 8)) ∧ t.mem = s.mem)
    (by
      have e1 : (BitVec.ofNat 64 k + BitVec.ofNat 64 7) >>> 3 = BitVec.ofNat 64 ((k + 7) / 8) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ushiftRight, BitVec.toNat_add, Nat.shiftRight_eq_div_pow]
        simp only [BitVec.toNat_ofNat]
        omega_arith
      prun [h6, e1, shl_ofNat (show (k + 7) / 8 * 2 ^ 1 < 2 ^ 64 by omega_arith)]
      congr 1; omega_arith) (by decide)) fun s₁ ⟨⟨a4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (area23_ok ((k1.gpr _ (by decide)).trans h23) a4 (by omega_arith)) fun s₂ ⟨⟨a10, a21, a29, a11, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have hm2 : s₂.mem = s.mem := by rw [m2, m1]
  rw [WP.block_append_iff]
  have e5 : off S (slot (2 * ((k + 7) / 8)) 0) + BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2) * 2 ^ 3) =
      off S (slot (2 * ((k + 7) / 8)) 8) := by
    rw [off_add, show (2 : Nat) ^ 3 = 8 from rfl]; unfold slot
    rw [show hdrBytes + 0 * (8 * (2 * ((k + 7) / 8) + 2)) + 8 * (2 * ((k + 7) / 8) + 2) * 8 =
      hdrBytes + 8 * (8 * (2 * ((k + 7) / 8) + 2)) by omega_arith]
  have hPL' : (s₂.mem.writeW (S + BitVec.ofNat 64 96) (off S (slot (2 * ((k + 7) / 8)) 8))).readW
      (S + BitVec.ofNat 64 40) 64 = BitVec.ofNat 64 pL := by
    rw [Mem.readW_writeW_sep (Offset.sep S (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), hm2]; exact hPL
  refine WP.mono (WP.keep [.r27, .r28, .r5, .r3] (Q := fun t =>
    t.gpr .r27 = off S (slot (2 * ((k + 7) / 8)) 0) ∧ t.gpr .r28 = BitVec.ofNat 64 (8 * (2 * ((k + 7) / 8) + 2)) ∧
    t.gpr .r5 = off S (slot (2 * ((k + 7) / 8)) 8) ∧ t.gpr .r3 = BitVec.ofNat 64 pL ∧
    t.mem = s₂.mem.writeW (off S 96) (off S (slot (2 * ((k + 7) / 8)) 8))) (by
      prun [a10, a29, (k12.gpr .r23 (by decide)).trans h23, oBP, oPLen,
        shl_ofNat (show 8 * (2 * ((k + 7) / 8) + 2) * 2 ^ 3 < 2 ^ 64 by omega_arith), e5,
        (hs.congr k12.wr).st (show 96 + 8 ≤ Z by omega_arith), (hs.congr k12.wr).ld (show 40 + 8 ≤ Z by omega_arith),
        hPL', BitVec.add_zero]) (by decide)) fun s₃ ⟨⟨a27, a28, a5, a3, m3⟩, k3⟩ => ?_
  have k13 := k12.trans k3
  rw [WP.block_append_iff]
  refine WP.mono (words_ok a3 hp hp') fun s₄ ⟨⟨b4, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  have e3 : ((BitVec.ofNat 64 (wsWords pL * 2 ^ 3) + BitVec.ofNat 64 16) <<< 3) + BitVec.ofNat 64 256 =
      BitVec.ofNat 64 (slot (wsWords pL) 8) := by
    have : wsWords pL < 2 ^ 57 + 1 := by unfold wsWords; omega_arith
    rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 16 from rfl, ← BitVec.ofNat_add,
      shl_ofNat (show (wsWords pL * 2 ^ 3 + 16) * 2 ^ 3 < 2 ^ 64 by omega_arith), ← BitVec.ofNat_add]
    congr 1; unfold slot hdrBytes; omega_arith
  have e5' : off S (slot (2 * ((k + 7) / 8)) 8) + BitVec.ofNat 64 (slot (wsWords pL) 8) =
      off S (slot (2 * ((k + 7) / 8)) 8 + slot (wsWords pL) 8) := off_add _ _ _
  refine WP.mono (WP.keep [.r3, .r5] (Q := fun t => t.mem = s₄.mem.writeW (S + BitVec.ofNat 64 104)
      (off S (slot (2 * ((k + 7) / 8)) 8 + slot (wsWords pL) 8))) (by
    prun [b4, (k4.gpr .r5 (by decide)).trans a5, (k14.gpr .r23 (by decide)).trans h23, oBQ, hdrBytes,
      shl_ofNat (show wsWords pL * 2 ^ 3 < 2 ^ 64 by have := wsWords_lt hp'; omega_arith), e3, e5',
      (hs.congr k14.wr).st (show 104 + 8 ≤ Z by omega_arith)]) (by decide)) fun t ⟨tm, k5⟩ => ?_
  have k15 := k14.trans k5
  have g : ∀ r ∈ [Reg.r10, .r21, .r29, .r11, .r27, .r28], t.gpr r = s₃.gpr r := fun r hr =>
    (k5.gpr r (by revert r hr; decide)).trans (k4.gpr r (by revert r hr; decide))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, k15.mono⟩
  · rw [g _ (by decide), k3.gpr _ (by decide), a10]
  · rw [g _ (by decide), k3.gpr _ (by decide), a21]
  · rw [g _ (by decide), k3.gpr _ (by decide), a29]
  · rw [g _ (by decide), k3.gpr _ (by decide), a11]
  · rw [g _ (by decide), a27]
  · rw [g _ (by decide), a28]
  · show t.mem.readW (S + BitVec.ofNat 64 96) 64 = _
    rw [tm, Mem.readW_writeW_sep (Offset.sep S (by omega_arith) (by omega_arith) (by omega_arith)) (by decide), m4, m3,
      Mem.readW_writeW_self64]
  · show t.mem.readW (S + BitVec.ofNat 64 104) 64 = _
    rw [tm, Mem.readW_writeW_self64]
  · rw [tm, m4, m3, hm2]
    exact ((writeW_outside s.mem S (d := 96) _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((writeW_outside _ S (d := 104) _ (by omega_arith)).mono (by omega_arith) (by omega_arith))

end VG.Proof.Bignum.PPC64LE.Crt
