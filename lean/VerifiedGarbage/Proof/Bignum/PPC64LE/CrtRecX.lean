module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.Run
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Crt
public import VerifiedGarbage.Proof.Bignum.Words
public import VerifiedGarbage.Proof.Bignum.Layout
public import VerifiedGarbage.Proof.Bignum.CrtFrame
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtSetup
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtAdd
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCheck
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtExport
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.PPC64LE.Isa
import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtCopy
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad

/-! ### `Bignum.PPC64LE.CrtRecX1`, which this module and modules that import it used -/

section

/-!
# The RSA private-key operation on PPC64LE: `h` and `m₂` into `X`

`xfer_ok`: a prime's array 4 into `X`'s array `j`, zero-extended.
`blkP_ok`, `blkQ_ok`: the registers for it, for `p` and for `q`.
`exportM2_ok`: `m₂` into `X`'s array 6, for its reduction modulo `p`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem x11_val {w : Nat} (hw : w < 2 ^ 31) :
    (BitVec.ofNat 64 (8 * (w + 2)) - BitVec.ofNat 64 16) >>> 2 = BitVec.ofNat 64 (2 * w) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, Nat.shiftRight_eq_div_pow]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 8 * (w + 2) < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 16 < 2 ^ 64 by decide),
    show 2 ^ 64 - 16 + 8 * (w + 2) = 8 * w + 2 ^ 64 by omega_arith, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show 8 * w < 2 ^ 64 by omega_arith), Nat.mod_eq_of_lt (show 2 * w < 2 ^ 64 by omega_arith)]
  omega_arith

/-- Three programs then a fourth, regrouped. -/
theorem wp_reassoc3 {a b c d : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq (.seq a (.seq b c)) d) s Q) : WP isa (.seq a (.seq b (.seq c d))) s Q := by
  obtain ⟨t, s', hx, hq⟩ := h
  cases hx with
  | seq h1 h2 =>
    cases h1 with
    | seq ha hbc =>
      cases hbc with
      | seq hb hc => exact ⟨_, _, .seq ha (.seq hb (.seq hc h2)), hq⟩

/-- `zeroWords`, `xb r14 j`, `r11 := r22`, `copyN`: `w_A` words of a prime's
array 4 (`r15`) into `X`'s array `j` (`r14`), zero-extended to `w_X` words
(`r11`), for `2 w_A` in `r22`. -/
theorem xfer_ok {s : State} {BX : Addr} {Z oA wA wX j : Nat} (hs : Scr s BX Z) (hA : oA + slot wA 24 ≤ Z)
    (hXA : slot wX 8 ≤ oA) (hj : j < 8) (hw1 : 1 ≤ wA) (hwx : wA ≤ wX) (hwX : wX < 2 ^ 31)
    (h14 : s.gpr .r14 = off BX (slot wX j)) (h11 : s.gpr .r11 = BitVec.ofNat 64 (2 * wX))
    (h22 : s.gpr .r22 = BitVec.ofNat 64 (2 * wA)) (h15 : s.gpr .r15 = off (off BX oA) (slot wA 4))
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) :
    WP isa (.seq Precompute.zeroWords (.seq (.block (xb .r14 j ++ ([.addi .r11 .r22 0] : List Instr))) copyN)) s fun t =>
      (val32 t.mem BX (slot wX j) (2 * wX) = val32 s.mem (off BX oA) (slot wA 4) (2 * wA) ∧
        Outside BX (slot wX j) (8 * wX) s.mem t.mem) ∧ Keep [.r0, .r11, .r14, .r15, .r17] s t := by
  have hn := hs.nowrap
  have e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  have eA4 := e wA 4; have eA8 := e wA 24
  have sXj := slot_le (w := wX) hj
  refine WP.seq (WP.mono (zeroWords_ok hs h14 h11 (by omega_arith) hwX (by omega_arith)) fun s₁ ⟨⟨_, hz, out1⟩, k1⟩ => ?_)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r14) (by decide) (by decide) ((k1.gpr _ (by decide)).trans h27)
    ((k1.gpr _ (by decide)).trans h28) j) fun s₂ ⟨⟨a14, m2⟩, k2⟩ => ?_
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t.mem = s₂.mem)
    (by prun [(k2.gpr .r22 (by decide)).trans ((k1.gpr .r22 (by decide)).trans h22), BitVec.add_zero])
    (by decide)) fun s₃ ⟨⟨a11, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (copySub_ok (a := oA + slot wA 4) (b := slot wX j) (w := wA) (hs.congr k13.wr)
    (by rw [k13.gpr _ (by decide), h15, off_off]) ((k3.gpr _ (by decide)).trans a14) a11 hw1
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)) fun t ⟨⟨hw, out4⟩, k4⟩ => ⟨⟨?_, ?_⟩, (k13.trans k4).mono⟩
  · rw [m3, m2] at hw out4
    have hsrc : ∀ i < wA, word s₁.mem BX (oA + slot wA 4 + 8 * i) = word s.mem BX (oA + slot wA 4 + 8 * i) :=
      fun i hi => out1.word (Or.inr (by omega_arith)) (by omega_arith)
    have hsplit := wv_add t.mem BX (slot wX j) wA (wX - wA)
    rw [show wA + (wX - wA) = wX by omega_arith] at hsplit
    have hlo : wv t.mem BX (slot wX j) wA = wv s.mem BX (oA + slot wA 4) wA :=
      wv_congr2 fun i hi => (hw i hi).trans (hsrc i hi)
    have hhi : wv t.mem BX (slot wX j + 8 * wA) (wX - wA) = 0 := (wv_eq_zero_iff _ _ _ _).mpr fun q hq => by
      rw [out4.word (Or.inr (by omega_arith)) (by omega_arith), show slot wX j + 8 * wA + 8 * q = slot wX j + 8 * (wA + q) by omega_arith]
      exact hz _ (by omega_arith)
    rw [Pre.val32_eq_wv, Pre.val32_eq_wv, wv_off, hsplit, hlo, hhi, Nat.mul_zero, Nat.add_zero]
  · rw [m3, m2] at out4
    exact out1.trans (out4.mono (by omega_arith) (by omega_arith))

/-- `r22 := r11`, `p`'s form: `2 w_A` in both, `w_A` in `r4`. -/
theorem midP_ok {t : State} {wA : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * wA))
    (h4 : t.gpr .r4 = BitVec.ofNat 64 wA) (hw : wA < 2 ^ 58) :
    WP isa (.block [.addi .r22 .r11 0, .lsl .r11 .r4 1]) t fun t' =>
      (t'.gpr .r22 = BitVec.ofNat 64 (2 * wA) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t'.mem = t.mem) ∧
        Keep [.r11, .r22] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [h11, h4, shl_ofNat (show wA * 2 ^ 1 < 2 ^ 64 by omega_arith), BitVec.add_zero]
  congr 1; omega_arith

/-- `r22 := r11`, `q`'s form. -/
theorem midQ_ok {t : State} {wA : Nat} (h11 : t.gpr .r11 = BitVec.ofNat 64 (2 * wA)) :
    WP isa (.block [.addi .r22 .r11 0]) t fun t' =>
      (t'.gpr .r22 = BitVec.ofNat 64 (2 * wA) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wA) ∧ t'.mem = t.mem) ∧
        Keep [.r11, .r22] t t' := by
  refine WP.keep _ ?_ (by decide)
  prun [h11, BitVec.add_zero]

/-- The registers for `xfer`: a prime's working space at `off BX oA` (the
header's word `oB`, its length at `oLen`), its array 4 in `r15`, `X`'s array
`j` in `r14`, `2 w_X` in `r11`, `2 w_A` in `r22`. -/
theorem blk_ok {s : State} {BX : Addr} {Z oA len oB oLen wX j : Nat} (mid : List Instr)
    (hmid : ∀ t : State, t.gpr .r11 = BitVec.ofNat 64 (2 * wsWords len) →
      t.gpr .r4 = BitVec.ofNat 64 (wsWords len) → WP isa (.block mid) t fun t' =>
        (t'.gpr .r22 = BitVec.ofNat 64 (2 * wsWords len) ∧ t'.gpr .r11 = BitVec.ofNat 64 (2 * wsWords len) ∧
          t'.mem = t.mem) ∧ Keep [.r11, .r22] t t')
    (hs : Scr s BX Z) (h23 : s.gpr .r23 = BX)
    (hoB : oB + 8 ≤ 256 ∧ oB % 8 = 0) (hoL : oLen + 8 ≤ 256 ∧ oLen % 8 = 0) (hZ : 256 ≤ Z)
    (hB : word s.mem BX oB = off BX oA) (hL : word s.mem BX oLen = BitVec.ofNat 64 len) (hl : 1 ≤ len)
    (hl' : len < 2 ^ 60) (hwX : wX < 2 ^ 31)
    (h27 : s.gpr .r27 = off BX (slot wX 0)) (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2))) :
    WP isa (.block (setupP oB oLen ++ PublicChecked.base .r15 4 ++ mid ++ xb .r14 j ++
      ([.addi .r11 .r28 0, .subi .r11 .r11 16, .lsr .d .r11 .r11 2] : List Instr))) s fun t =>
      (t.gpr .r14 = off BX (slot wX j) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧
        t.gpr .r22 = BitVec.ofNat 64 (2 * wsWords len) ∧ t.gpr .r15 = off (off BX oA) (slot (wsWords len) 4) ∧
        t.mem = s.mem) ∧ Keep [.r0, .r3, .r4, .r10, .r11, .r14, .r15, .r21, .r22, .r29] s t := by
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (setupP_ok hs h23 hoB hoL hZ hB hL hl hl') fun s₁ ⟨⟨a10, _, a29, a11, a4, m1⟩, k1⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r15) (by decide) (by decide) a10 a29 4) fun s₂ ⟨⟨a15, m2⟩, k2⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (hmid s₂ ((k2.gpr _ (by decide)).trans a11) ((k2.gpr _ (by decide)).trans a4))
    fun s₃ ⟨⟨a22, _, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r14) (by decide) (by decide) ((k13.gpr _ (by decide)).trans h27)
    ((k13.gpr _ (by decide)).trans h28) j) fun s₄ ⟨⟨a14, m4⟩, k4⟩ => ?_
  have k14 := k13.trans k4
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r28 (by decide)).trans h28, BitVec.add_zero, x11_val hwX]) (by decide))
    fun t ⟨⟨t11, tm⟩, k5⟩ => ⟨⟨(k5.gpr _ (by decide)).trans a14, t11,
      (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans a22),
      (k5.gpr _ (by decide)).trans ((k4.gpr _ (by decide)).trans ((k3.gpr _ (by decide)).trans a15)),
      by rw [tm, m4, m3, m2, m1]⟩, (k14.trans k5).mono⟩

/-- `exportM2`: `m₂`, `q`'s array 4 (at the header's `oBQ`, `q_len` in the
header), into `X`'s array 6, zero-extended to `X`'s words. -/
theorem exportM2_ok {s : State} {BX : Addr} {Z oQ qL wX : Nat}
    (hs : Scr s BX Z) (hQZ : oQ + slot (wsWords qL) 24 ≤ Z) (hXQ : slot wX 8 ≤ oQ)
    (hwQ : wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hq1 : 1 ≤ qL) (hq' : qL < 2 ^ 60) :
    WP isa exportM2 s fun t =>
      (val32 t.mem BX (slot wX 6) (2 * wX) = val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) ∧
        Outside BX (slot wX 6) (8 * wX) s.mem t.mem) ∧
      Keep [.r0, .r3, .r4, .r10, .r11, .r14, .r15, .r17, .r21, .r22, .r29] s t := by
  have hn := hs.nowrap
  have hZ : 256 ≤ Z := by have := slot_le (w := wX) (j := 0) (by decide); unfold slot at *; omega_arith
  unfold exportM2
  refine WP.seq (WP.mono (blk_ok (j := 6) (oA := oQ) _ (fun t h11 _ => midQ_ok h11) hs h23
    (by decide) (by decide) hZ hBQ hQL hq1 hq' hwX h27 h28) fun s₁ ⟨⟨b14, b11, b22, b15, m1⟩, k1⟩ => ?_)
  refine WP.mono (xfer_ok (hs.congr k1.wr) hQZ hXQ (by decide) (by unfold wsWords; omega_arith) hwQ hwX b14 b11
    b22 b15 ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28))
    fun t ⟨⟨v6, out⟩, k2⟩ => ⟨⟨by rw [v6, m1], by rw [← m1]; exact out⟩, (k1.trans k2).mono⟩

end VG.Proof.Bignum.PPC64LE.Crt

end

end

/-!
# The RSA private-key operation on PPC64LE: `m = q h + m₂`

`recombineX_ok`: `h` (`p`'s array 4) and `m₂` (`q`'s array 4) into `X`'s
arrays 7 and 6, `q h` (with `q` in `X`'s array 5) exactly, by a Montgomery
multiplication modulo `2^(64 w_X) - 1`, and `m₂` added, into array 4.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Crt

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.Crt
open VG.Proof.Bignum.PPC64LE

theorem prod_bound {x y z A B : Nat} (hA : 2 ≤ A) (hy : y < B) (hx : x < A) (hz : z < B) :
    y * x + z + 2 ≤ B * A := by
  obtain h1 : y * x ≤ (B - 1) * (A - 1) := Nat.mul_le_mul (by omega_arith) (by omega_arith)
  obtain h2 : (B - 1) * (A - 1) + (B - 1) = (B - 1) * A := by
    rw [Nat.mul_sub_one]; have := Nat.le_mul_of_pos_right (B - 1) (show 0 < A by omega_arith); omega_arith
  obtain h3 : (B - 1) * A + A = B * A := by
    rw [Nat.sub_one_mul]; have : A ≤ B * A := Nat.le_mul_of_pos_left A (by omega_arith); omega_arith
  omega_arith

theorem val32_off_eq {m m' : Mem} {B : Addr} {o d w a n : Nat} (h : Outside B a n m m')
    (hd : o + d + 8 * w ≤ a ∨ a + n ≤ o + d) (hd' : o + d + 8 * w ≤ 2 ^ 64) :
    val32 m' (off B o) d (2 * w) = val32 m (off B o) d (2 * w) := by
  rw [Pre.val32_eq_wv, Pre.val32_eq_wv, wv_off, wv_off, h.wv hd hd']

/-- The registers `recombineX` writes. -/
def recXRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r21,
    .r22, .r24, .r29]

/-- `recombineX`: for `h` in `p`'s array 4 and `m₂` in `q`'s (their working
spaces at `off BX oP` and `off BX oQ`, from the header with their lengths),
`q` in `X`'s array 5 (`w_X` words, at least `w_P + w_Q`) and
`M = 2^(64 w_X) - 1` in its array 0: `q h + m₂` into `X`'s array 4. -/
theorem recombineX_ok {s : State} {BX : Addr} {Z oP oQ pL qL wX Qv H M2 : Nat}
    (hs : Scr s BX Z) (hPZ : oP + slot (wsWords pL) 24 ≤ Z) (hXP : slot wX 8 ≤ oP)
    (hQZ : oQ + slot (wsWords qL) 24 ≤ Z) (hXQ : slot wX 8 ≤ oQ)
    (hpq : wsWords pL + wsWords qL ≤ wX) (hwX : wX < 2 ^ 31)
    (h23 : s.gpr .r23 = BX) (h27 : s.gpr .r27 = off BX (slot wX 0))
    (h28 : s.gpr .r28 = BitVec.ofNat 64 (8 * (wX + 2)))
    (hBP : word s.mem BX oBP = off BX oP) (hPL : word s.mem BX oPLen = BitVec.ofNat 64 pL)
    (hBQ : word s.mem BX oBQ = off BX oQ) (hQL : word s.mem BX oQLen = BitVec.ofNat 64 qL)
    (hp1 : 1 ≤ pL) (hp' : pL < 2 ^ 60) (hq1 : 1 ≤ qL) (hq' : qL < 2 ^ 60)
    (hM : val32 s.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1)
    (hM0 : word s.mem BX (slot wX 0) = BitVec.allOnes 64)
    (hq : val32 s.mem BX (slot wX 5) (2 * wX) = Qv) (hqb : Qv < 2 ^ (64 * wsWords qL))
    (hH : val32 s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL) = H)
    (hm2 : val32 s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL) = M2) :
    WP isa recombineX s fun t =>
      (val32 t.mem BX (slot wX 4) (2 * wX) = Qv * H + M2 ∧
        Outs BX [(slot wX 2, 8 * (wX + 2)), (slot wX 3, 8 * (wX + 2)), (slot wX 4, 8 * (wX + 2)),
          (slot wX 6, 8 * (wX + 2)), (slot wX 7, 8 * (wX + 2))] s.mem t.mem) ∧ Keep recXRegs s t := by
  have hn := hs.nowrap
  obtain e : ∀ w j, slot w j = hdrBytes + j * (8 * (w + 2)) := fun _ _ => rfl
  have hh : hdrBytes = 256 := rfl
  obtain eX0 := e wX 0; have eX2 := e wX 2; have eX3 := e wX 3; have eX4 := e wX 4; have eX5 := e wX 5
  obtain eX6 := e wX 6; have eX7 := e wX 7; have eX8 := e wX 8
  obtain eP4 := e (wsWords pL) 4; have eP8 := e (wsWords pL) 24
  obtain eQ4 := e (wsWords qL) 4; have eQ8 := e (wsWords qL) 24
  obtain hwP : 2 ≤ wsWords pL := by unfold wsWords; omega_arith
  obtain hwQ : 2 ≤ wsWords qL := by unfold wsWords; omega_arith
  unfold recombineX
  -- `h` into array 7.
  refine WP.seq (WP.mono (blk_ok (j := 7) (oA := oP) _ (fun t h11 h4 => midP_ok h11 h4 (wsWords_lt hp')) hs h23
    (by decide) (by decide) (by omega_arith) hBP hPL hp1 hp' hwX h27 h28) fun s₁ ⟨⟨a14, a11, a22, a15, m1⟩, k1⟩ => ?_)
  refine wp_reassoc3 (WP.seq (WP.mono (xfer_ok (hs.congr k1.wr) hPZ hXP (by decide) (by omega_arith) (by omega_arith) hwX a14 a11 a22
    a15 ((k1.gpr _ (by decide)).trans h27) ((k1.gpr _ (by decide)).trans h28))
    fun s₂ ⟨⟨v7, out2⟩, k2⟩ => ?_))
  obtain k12 := k1.trans k2
  rw [m1, hH] at v7
  rw [m1] at out2
  obtain hdr2 : ∀ d, d + 8 ≤ 256 → word s₂.mem BX d = word s.mem BX d := fun d hd =>
    out2.word (Or.inl (by omega_arith)) (by omega_arith)
  -- `m₂` into array 6.
  refine WP.seq (WP.mono (blk_ok (j := 6) (oA := oQ) _ (fun t h11 _ => midQ_ok h11) (hs.congr k12.wr)
    ((k12.gpr _ (by decide)).trans h23) (by decide) (by decide) (by omega_arith)
    (by rw [hdr2 _ (by decide)]; exact hBQ) (by rw [hdr2 _ (by decide)]; exact hQL) hq1 hq' hwX
    ((k12.gpr _ (by decide)).trans h27) ((k12.gpr _ (by decide)).trans h28))
    fun s₃ ⟨⟨b14, b11, b22, b15, m3⟩, k3⟩ => ?_)
  obtain k13 := k12.trans k3
  refine wp_reassoc3 (WP.seq (WP.mono (xfer_ok (hs.congr k13.wr) hQZ hXQ (by decide) (by omega_arith) (by omega_arith) hwX b14 b11 b22
    b15 ((k13.gpr _ (by decide)).trans h27) ((k13.gpr _ (by decide)).trans h28))
    fun s₄ ⟨⟨v6, out4⟩, k4⟩ => ?_))
  obtain k14 := k13.trans k4
  rw [m3, val32_off_eq out2 (Or.inr (by omega_arith)) (by omega_arith), hm2] at v6
  rw [m3] at out4
  -- What arrays 0, 5 and 7 hold.
  obtain o4' : Mont.Outside BX (slot wX 6) (8 * wX) s₂.mem s₄.mem := fun x hx => out4 x hx
  obtain o2' : Mont.Outside BX (slot wX 7) (8 * wX) s.mem s₂.mem := fun x hx => out2 x hx
  obtain v0 : val32 s₄.mem BX (slot wX 0) (2 * wX) = 2 ^ (64 * wX) - 1 := by
    rw [o4'.val32 (Or.inl (by omega_arith))
      (by omega_arith), o2'.val32
      (Or.inl (by omega_arith)) (by omega_arith), hM]
  obtain w0 : word s₄.mem BX (slot wX 0) = BitVec.allOnes 64 := by
    rw [out4.word (Or.inl (by omega_arith)) (by omega_arith), out2.word (Or.inl (by omega_arith)) (by omega_arith), hM0]
  obtain v5 : val32 s₄.mem BX (slot wX 5) (2 * wX) = Qv := by
    rw [o4'.val32 (Or.inl (by omega_arith))
      (by omega_arith), o2'.val32
      (Or.inl (by omega_arith)) (by omega_arith), hq]
  obtain v7' : val32 s₄.mem BX (slot wX 7) (2 * wX) = H := by
    rw [o4'.val32 (Or.inr (by omega_arith))
      (by omega_arith), v7]
  -- The bound of `q h + m₂`.
  obtain hHb : H < 2 ^ (64 * wsWords pL) := by
    have := val32_lt s.mem (off BX oP) (slot (wsWords pL) 4) (2 * wsWords pL)
    rw [hH, show 32 * (2 * wsWords pL) = 64 * wsWords pL by omega_arith] at this; exact this
  obtain hM2b : M2 < 2 ^ (64 * wsWords qL) := by
    have := val32_lt s.mem (off BX oQ) (slot (wsWords qL) 4) (2 * wsWords qL)
    rw [hm2, show 32 * (2 * wsWords qL) = 64 * wsWords qL by omega_arith] at this; exact this
  obtain hA2 : 2 ≤ 2 ^ (64 * wsWords pL) := Nat.one_lt_two_pow (by omega_arith)
  obtain hB2 : 2 ≤ 2 ^ (64 * wsWords qL) := Nat.one_lt_two_pow (by omega_arith)
  obtain hAB : 2 ^ (64 * wsWords qL) * 2 ^ (64 * wsWords pL) ≤ 2 ^ (64 * wX) := by
    rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  obtain hbound := prod_bound hA2 hqb hHb hM2b
  obtain hAX : 2 ^ (64 * wsWords pL) * 2 ≤ 2 ^ (64 * wX) :=
    Nat.le_trans (by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ hB2) hAB
  -- `M`'s registers, `r12 := 1`.
  refine WP.seq (WP.mono (WP.keep [.r10, .r21, .r29, .r11, .r12] (Q := fun t =>
    t.gpr .r10 = off BX (slot wX 0) ∧ t.gpr .r21 = off BX (slot wX 0) ∧
      t.gpr .r29 = BitVec.ofNat 64 (8 * (wX + 2)) ∧ t.gpr .r11 = BitVec.ofNat 64 (2 * wX) ∧
      t.gpr .r12 = 1#64 ∧ t.mem = s₄.mem)
    (by prun [(k14.gpr .r27 (by decide)).trans h27, (k14.gpr .r28 (by decide)).trans h28, BitVec.add_zero,
      x11_val hwX]) (by decide)) fun s₅ ⟨⟨c10, _, c29, c11, c12, m5⟩, k5⟩ => ?_)
  obtain k15 := k14.trans k5
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 4) (a := 5) (b := 7) (hs.congr k15.wr) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega_arith) hwX (by omega_arith) c10 c29 c11
    (by rw [c12]; decide) (by rw [m5, c12, w32_ones w0]; decide) (by rw [m5, v7', v0]; omega_arith))
    fun s₆ ⟨⟨l4, e4, o6⟩, k6⟩ => ?_)
  obtain k16 := k15.trans k6
  rw [m5, v0] at l4 e4
  rw [m5] at o6
  rw [v5, v7'] at e4
  obtain x4 : val32 s₆.mem BX (slot wX 4) (2 * wX) = Qv * H :=
    mont_exact (by have := Nat.one_le_two_pow (n := 64 * wX); omega_arith) l4 (by omega_arith) e4
  obtain x6 : val32 s₆.mem BX (slot wX 6) (2 * wX) = M2 := by
    rw [o6.val32 (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith) (by omega_arith), v6]
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r15) (by decide) (by decide) ((k16.gpr _ (by decide)).trans h27)
    ((k16.gpr _ (by decide)).trans h28) 4) fun s₇ ⟨⟨a15', m7⟩, k7⟩ => ?_
  obtain k17 := k16.trans k7
  rw [WP.block_append_iff]
  refine WP.mono (xb_ok (rd := .r16) (by decide) (by decide) ((k17.gpr _ (by decide)).trans h27)
    ((k17.gpr _ (by decide)).trans h28) 6) fun s₈ ⟨⟨a16', m8⟩, k8⟩ => ?_
  obtain k18 := k17.trans k8
  refine WP.mono (WP.keep [.r20] (Q := fun t => t.gpr .r20 = BitVec.ofNat 64 0 -
      BitVec.ofNat 64 (if true then 1 else 0) ∧ t.mem = s₈.mem) (by prun) (by decide))
    fun s₉ ⟨⟨a20, m9⟩, k9⟩ => ?_
  obtain k19 := k18.trans k9
  obtain hm9 : s₉.mem = s₆.mem := by rw [m9, m8, m7]
  refine WP.mono (addMask_ok (b := true) (n := 2 * wX) (dT := slot wX 4) (dM := slot wX 6) (hs.congr k19.wr)
    ((k9.gpr _ (by decide)).trans ((k8.gpr _ (by decide)).trans a15')) ((k9.gpr _ (by decide)).trans a16')
    ((((k7.trans k8).trans k9).gpr _ (by decide)).trans ((k6.gpr _ (by decide)).trans c11)) a20 (by omega_arith) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith)) fun t ⟨hT, outT, kT⟩ => ⟨⟨?_, ?_⟩, (k19.trans kT).mono⟩
  · rw [hT, hm9, x4, x6]
    simp only [↓reduceIte]
    rw [show 32 * (2 * wX) = 64 * wX by omega_arith, Nat.mod_eq_of_lt (by omega_arith)]
  · intro x hx
    rw [hm9] at outT
    obtain h2 := hx _ (List.mem_cons_self ..)
    obtain h3 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    obtain h4 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    obtain h6 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
    obtain h7 := hx _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
    simp only at h2 h3 h4 h6 h7
    have h6' : ofs BX x < slot wX 6 ∨ slot wX 6 + 8 * (wX + 2) ≤ ofs BX x := h6
    have h7' : ofs BX x < slot wX 7 ∨ slot wX 7 + 8 * (wX + 2) ≤ ofs BX x := h7
    rw [outT x (by omega_arith), o6 x (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only <;> omega_arith), out4 x (by omega_arith), out2 x (by omega_arith)]

end VG.Proof.Bignum.PPC64LE.Crt
