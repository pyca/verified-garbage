module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
public import VerifiedGarbage.Proof.Bignum.PPC64LE.ModArithReduce
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Framework.PPC64LE.Step
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: the digest's length, and the comparison

* `digestLen_ok`: the header's word `hDlen` := `min(digest_len, q's
  significant octets)`;
* `compare_ok`: in the Q space, `v mod q` (`reduce` of the buffer's `p_len`
  octets) compared with r, under the mask in `r26`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

theorem shr6_zero {D : Nat} (hD : D < 2 ^ 64) : BitVec.ofNat 64 D >>> 6 = 0 ↔ D < 64 := by
  have z : (0 : BitVec 64).toNat = 0 := rfl
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hD] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hD]
    omega

theorem sub_sign_zero {a D : Nat} (ha : a ≤ 32) (hD : D < 64) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 D) >>> 63 = 0 ↔ D ≤ a := by
  have z : (0 : BitVec 64).toNat = 0 := rfl
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow] at this
    by_contra hc
    rw [Nat.mod_eq_of_lt (show D < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show D < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]
    rw [show 2 ^ 64 - D + a = (a - D) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- `digestLen`: the header's word `hDlen` := `min(D, qb)`. -/
theorem digestLen_ok {s : State} {L : Lay} {D qb : Nat} (hL : L.Ok) (hs : ScrL s L) (h21 : s.gpr .r21 = L.S)
    (hD : word s.mem L.S hDlen = BitVec.ofNat 64 D) (hDlt : D < 2 ^ 64)
    (hQ : word s.mem L.S hQb = BitVec.ofNat 64 qb) (hqb : qb ≤ 32) :
    WP isa digestLen s fun t =>
      (word t.mem L.S hDlen = BitVec.ofNat 64 (min D qb) ∧ Outside L.S hDlen 8 s.mem t.mem) ∧
        Keep [.r0, .r3, .r4] s t := by
  have r56 := hdr_rd hL hs (d := 56) (by decide)
  have r72 := hdr_rd hL hs (d := 72) (by decide)
  have v56 : s.mem.readW (L.S + BitVec.ofNat 64 56) 64 = BitVec.ofNat 64 D := hD
  have v72 : s.mem.readW (L.S + BitVec.ofNat 64 72) 64 = BitVec.ofNat 64 qb := hQ
  have w56 : InRegions s.wr (L.S + BitVec.ofNat 64 56) 8 :=
    hs.st (show 56 + 8 ≤ L.Z by have := hL.z256; omega)
  have hnw := hL.nowrap
  have hz := hL.z256
  -- The store of `qb`, when `D` is not the minimum.
  have hstore : ∀ u : State, u.gpr .r21 = L.S → u.gpr .r4 = BitVec.ofNat 64 qb → u.mem = s.mem →
      u.wr = s.wr → qb ≤ D → Keep [.r0, .r3, .r4] s u →
      WP isa (.block [.store .d .r4 .r21 hDlen]) u fun t =>
        (word t.mem L.S hDlen = BitVec.ofNat 64 (min D qb) ∧ Outside L.S hDlen 8 s.mem t.mem) ∧
          Keep [.r0, .r3, .r4] s t := by
    intro u u21 u4 um uw hle ku
    rw [Nat.min_eq_right hle]
    refine WP.mono (WP.keep [] (Q := fun t => t.mem = s.mem.writeW (off L.S 56) (BitVec.ofNat 64 qb)) ?_
      (by decide)) fun t ⟨tm, kt⟩ => ⟨⟨?_, ?_⟩, (ku.trans kt).mono (by decide)⟩
    · have w56' : InRegions u.wr (L.S + BitVec.ofNat 64 56) 8 := by rw [uw]; exact w56
      prun [u21, u4, um, w56', hDlen]
    · rw [tm]; exact word_writeW_self _ _ _ _
    · rw [tm]; exact writeW_outside s.mem L.S (d := 56) _ (by omega)
  unfold digestLen
  refine WP.seq (WP.mono (WP.keep [.r0, .r3, .r4] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64 D ∧
      u.gpr .r4 = BitVec.ofNat 64 qb ∧ u.gpr .r0 = BitVec.ofNat 64 D >>> 6 ∧ u.mem = s.mem)
      (by prun [h21, r56, r72, v56, v72, hDlen, hQb]) (by decide)) fun s₁ ⟨⟨a3, a4, a0, m1⟩, k1⟩ => ?_)
  refine WP.ite (s₁.gpr .r0 == 0) (eval_zero _ _) (fun hb => ?_) (fun hb => ?_)
  · have hlt : D < 64 := (shr6_zero hDlt).mp (by rw [← a0]; simpa using hb)
    refine WP.seq (WP.mono (WP.keep [.r0] (Q := fun u =>
        u.gpr .r0 = (BitVec.ofNat 64 qb - BitVec.ofNat 64 D) >>> 63 ∧ u.mem = s₁.mem)
        (by prun [a3, a4]) (by decide)) fun s₂ ⟨⟨b0, m2⟩, k2⟩ => ?_)
    refine WP.ite (s₂.gpr .r0 == 0) (eval_zero _ _) (fun hb' => ?_) (fun hb' => ?_)
    · have hle : D ≤ qb := (sub_sign_zero hqb hlt).mp (by rw [← b0]; simpa using hb')
      refine wp_nil ⟨⟨?_, by rw [m2, m1]; exact Outside.refl _ _ _ _⟩, (k1.trans k2).mono (by decide)⟩
      rw [m2, m1, Nat.min_eq_left hle]; exact hD
    · have hle : qb ≤ D := by
        have := mt (sub_sign_zero hqb hlt).mpr (by rw [← b0]; simpa using hb')
        omega
      exact hstore s₂ ((k1.trans k2).gpr .r21 (by decide) |>.trans h21) ((k2.gpr .r4 (by decide)).trans a4)
        (by rw [m2, m1]) (k1.trans k2).wr hle ((k1.trans k2).mono (by decide))
  · have hle : qb ≤ D := by
      have := mt (shr6_zero hDlt).mpr (by rw [← a0]; simpa using hb)
      omega
    exact hstore s₁ ((k1.gpr .r21 (by decide)).trans h21) a4 m1 k1.wr hle (k1.mono (by decide))

end VG.Proof.Dsa.PPC64LE

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

theorem mask_bit (c b : Bool) :
    mask c &&& mask b &&& BitVec.ofNat 64 1 = BitVec.ofNat 64 (if c = true ∧ b = true then 1 else 0) := by
  cases c <;> cases b <;> rfl

/-- The registers `compare` writes. -/
def cmpRegs : List Reg :=
  enterRegs ++ [.r30, .r31] ++ ModArith.redRegs ++ [.r5, .r8, .r9] ++ [.r6, .r12] ++ loadRegs ++
    eqRegs .r3 ++ [.r0, .r3]

/-- `compare`: `r3 := 1` if `v mod q = r` (`v` the buffer's `p_len` octets)
and `b` (the mask in `r26`), else 0. -/
theorem compare_ok {s : State} {L : Lay} {key sig dig : Addr} {b : Bool} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) (hsg : Src s L sig (2 * L.ql))
    (hq : 0 < arrQ s.mem L 0) (h26 : s.gpr .r26 = mask b) :
    WP isa Verify.compare s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 =
          rOf s.mem L sig ∧ b = true then 1 else 0) ∧ Body L s.mem t.mem) ∧ Keep cmpRegs s t := by
  have hql := hL.ql
  have hpl := hL.pl
  have e71 : slot 4 1 = 304 := rfl
  have e75 : slot 4 5 = 496 := rfl
  unfold Verify.compare
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hh h21) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have r32 := hdr_rd hL hs (d := 32) (by decide)
  have r8 := hdr_rd hL hs (d := 8) (by decide)
  have v32 : s.mem.readW (L.S + BitVec.ofNat 64 32) 64 = L.Buf := hh.buf
  have v8 : s.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := hh.pl
  refine WP.mono (WP.keep [.r30, .r31] (Q := fun u => u.gpr .r30 = L.Buf ∧ u.gpr .r31 = BitVec.ofNat 64 L.pl ∧
      u.mem = s₁.mem) (by
        have r32' : InRegions (s₁.rd ++ s₁.wr) (L.S + BitVec.ofNat 64 32) 8 := by rw [k1.rd, k1.wr]; exact r32
        have r8' : InRegions (s₁.rd ++ s₁.wr) (L.S + BitVec.ofNat 64 8) 8 := by rw [k1.rd, k1.wr]; exact r8
        have v32' : s₁.mem.readW (L.S + BitVec.ofNat 64 32) 64 = L.Buf := by rw [m1]; exact v32
        have v8' : s₁.mem.readW (L.S + BitVec.ofNat 64 8) 64 = BitVec.ofNat 64 L.pl := by rw [m1]; exact v8
        prun [q1.h21, r32', r8', v32', v8', hBuf, hP]) (by decide))
    fun s₂ ⟨⟨a30, a31, m2⟩, k2⟩ => ?_
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  have e2 := q1.env
  refine WP.seq (WP.mono (ModArith.reduce_ok (B := L.Q) (Z := 1600) (w := 4) (D := L.Buf) (L := L.pl) (e2.hs.congr k2.wr) (by decide) (by decide)
    (by decide) ((k2.gpr .r10 (by decide)).trans e2.h10) ((k2.gpr .r29 (by decide)).trans e2.h29)
    ((k2.gpr .r11 (by decide)).trans e2.h11) (by rw [m2]; exact (show 0 < arr s₁.mem L.Q 4 0 by rw [m1]; exact hq))
    (by rw [a30]; exact (BitVec.add_zero _).symm) a31 (by omega) (by omega)
    (fun i hi => by
      rw [k12.rd, k12.wr]
      exact (ScrL.bufN hs hL (n := L.pl) (by omega)).ld (show i + 1 ≤ L.pl by omega))
    (buf_apartQ L (by omega))) fun s₃ ⟨⟨v1, o3⟩, k3⟩ => ?_)
  rw [m21] at v1
  have k13 := k12.trans k3
  have o3' : Outside L.Q (slot 4 1) (24 * (4 + 2)) s.mem s₃.mem := by rw [← m21]; exact o3
  have qa3 : QArr L s.mem s₃.mem := QArr.of o3' (by rw [e71]) (by rw [e71]; decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.r31] (Q := fun u => u.gpr .r31 = L.Q ∧ u.mem = s₃.mem)
      (by prun [((k2.trans k3).gpr .r23 (by decide)).trans q1.h23, BitVec.add_zero]) (by decide))
    fun s₄ ⟨⟨a31', m4⟩, k4⟩ => ?_
  have q4 : InQ s₄ L := ⟨⟨e2.hs.congr (k2.trans (k3.trans k4)).wr,
    ((k3.trans k4).gpr .r10 (by decide)).trans ((k2.gpr .r10 (by decide)).trans e2.h10),
    ((k2.trans (k3.trans k4)).gpr .r29 (by decide)).trans e2.h29,
    ((k2.trans (k3.trans k4)).gpr .r11 (by decide)).trans e2.h11, a31', by decide, by decide, by decide⟩,
    ((k2.trans (k3.trans k4)).gpr .r21 (by decide)).trans q1.h21,
    ((k2.trans (k3.trans k4)).gpr .r23 (by decide)).trans q1.h23⟩
  have Q4 : QS s₄ L key sig dig := ⟨q4, hs.congr (k13.trans k4).wr, hh.body (by rw [m4]; exact qa3.qbody.body hL) hL⟩
  refine WP.mono (ptrR_ok Q4.regs) fun s₅ ⟨⟨b12, b6, m5⟩, k5⟩ => ?_
  have Q5 := Q4.step k5 (by decide)
  have k15 := (k13.trans k4).trans k5
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q5 hL (by decide) (by decide)
      ((hsg.keep k15.rd k15.wr).sub (o := 0) (k := L.ql) (by omega)) (by rw [b12, off, BitVec.add_zero]) b6
      (by omega) (by omega)) fun s₆ ⟨⟨Q6, v5, _, o6, qa6⟩, k6⟩ => ?_)
  refine WP.seq (WP.mono (eqMask_ok Q6.inq.env .r3 (a := 1) (b := 5) (by decide) (by decide))
    fun s₇ ⟨⟨c3, m7⟩, k7⟩ => ?_)
  have k17 := (k15.trans k6).trans k7
  refine WP.mono (WP.keep [.r0, .r3] (Q := fun u => u.gpr .r3 = BitVec.ofNat 64
      (if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 = rOf s.mem L sig ∧ b = true
        then 1 else 0) ∧ u.mem = s₇.mem) ?_ (by decide))
    fun t ⟨⟨t3, mt⟩, kt⟩ => ⟨⟨t3, ?_⟩, (k17.trans kt).mono (by decide)⟩
  · have a1 : val32 s₆.mem L.Q (slot 4 1) (2 * 4) =
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.pl) % arrQ s.mem L 0 := by
      rw [Outside.val32 o6 (by rw [e71, e75]; omega) (by decide), m5, m4, v1]
    have a5 : val32 s₆.mem L.Q (slot 4 5) (2 * 4) = rOf s.mem L sig := by
      have := v5
      rw [arrQ, arr] at this
      rw [this, m5, m4, (hsg.sub (o := 0) (k := L.ql) (by omega)).bytes (qa3.qbody.body hL) hL.z256]
      simp only [rOf, off, BitVec.add_zero]
    have b26 : s₇.gpr .r26 = mask b := (k17.gpr .r26 (by decide)).trans h26
    rw [a1, a5] at c3
    prun [c3, b26, mask_bit]
    simp only [decide_eq_true_eq]
  · rw [mt, m7]
    exact ((qa3.trans (by rw [← m4, ← m5]; exact qa6)).qbody.body hL)

end VG.Proof.Dsa.PPC64LE
