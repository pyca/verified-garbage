module

import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ
import VerifiedGarbage.Proof.Dsa.PPC64LE.Comb.Pow
import VerifiedGarbage.Proof.Dsa.PPC64LE.Elem.Basic
import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMinv
import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx

/-!
# DSA verification on PPC64LE: `g^u1 y^u2 mod p`

`combine_ok`: into the P space (p in array 0, `R² mod p` in array 8), `g^u1
mod p` (kept in array 9) and `y^u2 mod p`, for the exponents `u1` and `u2`
of the buffer's first and second `q_len` octets, and their product modulo p
to the buffer's first `p_len` octets. The Q space is kept.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- A change in the P space's arrays keeps the Q space. -/
theorem comb_pbody_keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : PBody L m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  intro x hx
  have hlt := (x - L.Q).isLt
  have hq : ofs L.Q x < 1600 := by simp only [ofs] at hx ⊢; omega
  have := (Offset.lt_iff x L.S (d := L.qOff) (n := 1600) (by simp only [Lay.bOff] at hb; omega)).mp hq
  have : 256 ≤ L.qOff := by simp only [Lay.qOff, Lay.slot_eq]; omega
  exact h x (Or.inr (by simp only [ofs] at this ⊢; omega))

/-- A change in the buffer keeps the Q space. -/
theorem combBufKeepQ {L : Lay} {m m' : Mem} {n : Nat} (h : Outside L.Buf 0 n m m') (hn : n ≤ 2 ^ 64 - 1600) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hlt := (x - L.Q).isLt
  have hq : ofs L.Q x < 1600 := by simp only [ofs] at hx ⊢; omega
  refine h x (Or.inr ?_)
  rw [buf_eq]
  simp only [ofs, off] at hq ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- The buffer's bytes are past the P space, as `storeBE` needs. -/
theorem combBufPastP {L : Lay} (hL : L.Ok) : ∀ x, ofs L.Buf x < L.pl → L.qOff ≤ ofs L.S x := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  intro x hx
  have := (Offset.lt_iff x L.S (d := L.bOff) (n := L.pl) (by omega)).mp hx
  simp only [Lay.bOff] at this
  simp only [ofs]
  omega

/-- Two Montgomery multiplications: `[5] R ≡ y (R² mod p)` and `[7] R ≡ g [5]`
give `[7] = g y mod p`. -/
theorem combMont {p R V5 V7 G Y : Nat} (hR : Nat.Coprime R p) (h5 : V5 * R % p = Y * (R * R % p) % p)
    (h7 : V7 * R % p = G * V5 % p) (hlt : V7 < p) : V7 = G * Y % p := by
  have e5 : V5 % p = Y * R % p := VG.Proof.Bignum.mont_cancel hR (by
    rw [h5, Nat.mul_mod_mod, Nat.mul_assoc])
  have e7 : V7 % p = G * Y % p := VG.Proof.Bignum.mont_cancel hR (by
    rw [h7, Nat.mul_mod, e5, ← Nat.mul_mod, Nat.mul_assoc])
  rw [← e7, Nat.mod_eq_of_lt hlt]

/-- The registers `combine` writes. -/
def combRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22,
    .r23, .r24, .r25, .r29, .r30, .r31]

/-- `combine`: `g^u1 y^u2 mod p` to the buffer's first `p_len` octets. -/
theorem combine_ok {s : State} {L : Lay} {key sig dig : Addr} {p : Nat} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig dig) (hk : Src s L key (3 * L.pl + L.ql))
    (hp0 : arrP s.mem L 0 = p) (hp : 2 ≤ p) (hpo : p % 2 = 1) (hrr : arrP s.mem L 8 = 2 ^ (128 * L.wp) % p) :
    WP isa combine s fun t =>
      (Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.pl) =
          gOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) % p *
            (yOf s.mem L key ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (off L.Buf L.ql) L.ql) % p) % p ∧
        InP t L ∧ Body L s.mem t.mem ∧ Outside L.Q 1600 (2 ^ 64 - 1600) s.mem t.mem) ∧ Keep combRegs s t := by
  have hZ := hL.hdr
  have hw := hL.wp_ge
  have hw8 := hL.wp_eq
  have hnw := hL.nowrap
  have hql := hL.ql
  have hpl := hL.pl
  have hbe := hL.buf_end
  have hqZ : L.qOff + 1600 ≤ L.Z := by simp only [Lay.bOff] at hbe; omega
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have e0 := Lay.slot_eq L.wp 0; have e1 := Lay.slot_eq L.wp 1; have e2 := Lay.slot_eq L.wp 2
  have e3 := Lay.slot_eq L.wp 3
  have e4 := Lay.slot_eq L.wp 4; have e5 := Lay.slot_eq L.wp 5; have e6 := Lay.slot_eq L.wp 6
  have e7 := Lay.slot_eq L.wp 7; have e8 := Lay.slot_eq L.wp 8; have e9 := Lay.slot_eq L.wp 9
  have e28 := Lay.slot_eq L.wp 28
  unfold combine
  -- Into the P space; g's octets and the buffer.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (enterP_ok hL hs hr) fun s₁ ⟨⟨in1, m1⟩, k1⟩ => ?_
  refine WP.mono (ptrG_ok (hr.keep k1)) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
  refine WP.mono (bufBase_ok hL (hr.keep (k1.trans k2)) (rd := .r24) (t := .r0) (by decide))
    fun s₃ ⟨⟨a24, m3⟩, k3⟩ => ?_
  replace a24 : s₃.gpr .r24 = off L.Buf 0 := by rw [a24, off, BitVec.add_zero]
  have k13 := (k1.trans k2).trans k3
  have hm3 : s₃.mem = s.mem := by rw [m3, m2, m1]
  have in3 : InP s₃ L := in1.keep (k2.trans k3) (by decide)
  -- `g^u1 mod p` into array 4.
  refine WP.seq (WP.mono (combPowP_ok (o := 0) (p := p) hL (hs.congr k13.wr) (hr.keep k13) in3
    ((hk.keep k13.rd k13.wr).sub (o := L.pl + L.ql) (k := L.pl) (by omega))
    ((k3.gpr .r12 (by decide)).trans a12) a24 (by omega) (by rw [hm3]; exact hp0) hp hpo
    (by rw [hm3]; exact hrr)) fun s₄ ⟨⟨v4, in4, o4⟩, k4⟩ => ?_)
  rw [hm3] at v4 o4
  -- Into array 9.
  refine WP.seq (WP.mono (copy_ok in4.env (o := 9) (a := 4) (by decide) (by decide) (by decide))
    fun s₅ ⟨⟨v9, o5⟩, k5⟩ => ?_)
  have pb5 : PArr L s.mem s₅.mem := (o4.mono (by omega) (by omega)).trans (o5.mono (by omega) (by omega))
  have k15 := (k13.trans k4).trans k5
  -- The second exponent and y's octets.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (ptrBuf2_ok hL (hr.keep k15)) fun s₆ ⟨⟨b12, b6, m6⟩, k6⟩ => ?_
  refine WP.mono (WP.keep [.r24] (Q := fun t => t.gpr .r24 = off L.Buf L.ql ∧ t.mem = s₆.mem)
    (by prun [b12, BitVec.add_zero]) (by decide)) fun s₇ ⟨⟨c24, m7⟩, k7⟩ => ?_
  refine WP.mono (ptrY_ok (hr.keep ((k15.trans k6).trans k7))) fun s₈ ⟨⟨d12, d6, m8⟩, k8⟩ => ?_
  have k58 := (k6.trans k7).trans k8
  have k18 := k15.trans k58
  have hm8 : s₈.mem = s₅.mem := by rw [m8, m7, m6]
  have in8 : InP s₈ L := (in4.keep k5 (by decide)).keep k58 (by decide)
  have a0 : arrP s₈.mem L 0 = p := by
    rw [hm8, arrP, arr, Outside.val32 pb5 (by omega) (by omega)]; exact hp0
  have a8 : arrP s₈.mem L 8 = 2 ^ (128 * L.wp) % p := by
    rw [hm8, arrP, arr, Outside.val32 o5 (by omega) (by omega), Outside.val32 o4 (by omega) (by omega)]
    exact hrr
  have pb8 : PArr L s.mem s₈.mem := by rw [hm8]; exact pb5
  -- `y^u2 mod p` into array 4.
  refine WP.seq (WP.mono (combPowP_ok (o := L.ql) (p := p) hL (hs.congr k18.wr) (hr.keep k18) in8
    ((hk.keep k18.rd k18.wr).sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)) d12
    ((k8.gpr .r24 (by decide)).trans c24) (by omega) a0 hp hpo a8) fun s₉ ⟨⟨w4, in9, o9⟩, k9⟩ => ?_)
  rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes (pb8.pbody.body hL) hZ,
    combBufBytes hL pb8 (by omega) (o := L.ql) (k := L.ql) (by omega)] at w4
  -- `R² mod p` into array 1, and `-p⁻¹`.
  refine WP.seq (WP.mono (copy_ok in9.env (o := 1) (a := 8) (by decide) (by decide) (by decide))
    fun s₁₀ ⟨⟨v1, o10⟩, k10⟩ => ?_)
  have en10 := in9.env.keep k10 (by decide)
  have p10 : val32 s₁₀.mem L.S (slot L.wp 0) (2 * L.wp) = p := by
    rw [Outside.val32 o10 (by omega) (by omega), Outside.val32 o9 (by omega) (by omega)]; exact a0
  have hlow : (word s₁₀.mem L.S (slot L.wp 0)).toNat % 2 = 1 := by
    have h1 := word_eq_w32 s₁₀.mem L.S (slot L.wp 0)
    have h2 : val32 s₁₀.mem L.S (slot L.wp 0) (2 * L.wp - 1 + 1) =
        w32 s₁₀.mem L.S (slot L.wp 0) + 2 ^ 32 * val32 s₁₀.mem L.S (slot L.wp 0 + 4) (2 * L.wp - 1) := rfl
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * L.wp), p10] at h2
    omega
  refine WP.seq (WP.mono (Pub.minv_ok en10.hs en10.h10 (by omega) hlow) fun s₁₁ ⟨⟨r12lt, r12inv, m11⟩, k11⟩ => ?_)
  have en11 := en10.keep k11 (by decide)
  rw [← m11] at r12inv
  have p11 : val32 s₁₁.mem L.S (slot L.wp 0) (2 * L.wp) = p := by rw [m11]; exact p10
  have r11 : val32 s₁₁.mem L.S (slot L.wp 1) (2 * L.wp) = 2 ^ (128 * L.wp) % p := by
    rw [m11]
    show arr s₁₀.mem L.S L.wp 1 = _
    rw [v1, arr, Outside.val32 o9 (by omega) (by omega)]; exact a8
  have y11 : val32 s₁₁.mem L.S (slot L.wp 4) (2 * L.wp) = arrP s₉.mem L 4 := by
    rw [m11, Outside.val32 o10 (by omega) (by omega)]
  -- `[5] R ≡ y R² (mod p)`.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 5) (a := 4) (b := 1) en11.hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) en11.h10 en11.h29 en11.h11
    r12lt r12inv (by rw [r11, p11]; exact Nat.mod_lt _ (by omega))) fun s₁₂ ⟨⟨lt5, eq5, o12⟩, k12⟩ => ?_)
  rw [p11, r11, y11] at eq5
  rw [p11] at lt5
  have o12' : Outside L.S (slot L.wp 2) (slot L.wp 6 - slot L.wp 2) s₁₁.mem s₁₂.mem := outs_within o12
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega)
  have en12 := en11.keep k12 (by decide)
  -- `g` into array 6.
  refine WP.seq (WP.mono (copy_ok en12 (o := 6) (a := 9) (by decide) (by decide) (by decide))
    fun s₁₃ ⟨⟨v6, o13⟩, k13'⟩ => ?_)
  have en13 := en12.keep k13' (by decide)
  have p13 : val32 s₁₃.mem L.S (slot L.wp 0) (2 * L.wp) = p := by
    rw [Outside.val32 o13 (by omega) (by omega), Outside.val32 o12' (by omega) (by omega)]; exact p11
  have five13 : val32 s₁₃.mem L.S (slot L.wp 5) (2 * L.wp) = val32 s₁₂.mem L.S (slot L.wp 5) (2 * L.wp) :=
    Outside.val32 o13 (by omega) (by omega)
  have g13 : val32 s₁₃.mem L.S (slot L.wp 6) (2 * L.wp) = arrP s₄.mem L 4 := by
    show arr s₁₃.mem L.S L.wp 6 = _
    rw [v6, arr, Outside.val32 o12' (by omega) (by omega), m11, Outside.val32 o10 (by omega) (by omega),
      Outside.val32 o9 (by omega) (by omega), hm8]
    exact v9
  have w13 : w32 s₁₃.mem L.S (slot L.wp 0) = w32 s₁₁.mem L.S (slot L.wp 0) := by
    rw [Outside.w32 o13 (by omega) (by omega), Outside.w32 o12' (by omega) (by omega)]
  -- `[7] R ≡ g [5] (mod p)`.
  refine WP.seq (WP.mono (Pub.montOp_ok (o := 7) (a := 6) (b := 5) en13.hs (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by omega) en13.h10 en13.h29 en13.h11
    ((k13'.gpr .r12 (by decide)).trans ((k12.gpr .r12 (by decide)).trans rfl) ▸ r12lt)
    (by rw [w13, k13'.gpr .r12 (by decide), k12.gpr .r12 (by decide)]; exact r12inv)
    (by rw [five13, p13]; exact lt5)) fun s₁₄ ⟨⟨lt7, eq7, o14⟩, k14⟩ => ?_)
  rw [p13, g13, five13] at eq7
  rw [p13] at lt7
  have o14' : Outside L.S (slot L.wp 2) (slot L.wp 8 - slot L.wp 2) s₁₃.mem s₁₄.mem := outs_within o14
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; intro r hr
        rcases hr with rfl | rfl | rfl <;> dsimp only <;> omega)
  have en14 := en13.keep k14 (by decide)
  have v7 : val32 s₁₄.mem L.S (slot L.wp 7) (2 * L.wp) = arrP s₄.mem L 4 * arrP s₉.mem L 4 % p := by
    have hR := VG.Proof.Bignum.coprime_pow2 hpo (64 * L.wp)
    have hRR : (2 : Nat) ^ (64 * L.wp) * 2 ^ (64 * L.wp) = 2 ^ (128 * L.wp) := by
      rw [← Nat.pow_add]; congr 1; omega
    rw [← hRR] at eq5
    exact combMont hR eq5 eq7 lt7
  have pb14 : PArr L s.mem s₁₄.mem :=
    ((((pb8.trans (o9.mono (by omega) (by omega))).trans (o10.mono (by omega) (by omega))).trans
      (by rw [← m11]; exact o12'.mono (by omega) (by omega))).trans (o13.mono (by omega) (by omega))).trans
      (o14'.mono (by omega) (by omega))
  have k114 := (((((k18.trans k9).trans k10).trans k11).trans k12).trans k13').trans k14
  have hs14 : ScrL s₁₄ L := hs.congr k114.wr
  -- To the buffer.
  have hr14 := hr.keep k114
  refine WP.seq (WP.mono (show WP isa (.block (bufBase .r12 .r0 ++ getP .r6)) s₁₄ fun t =>
      (t.gpr .r12 = L.Buf ∧ t.gpr .r6 = BitVec.ofNat 64 L.pl ∧ t.mem = s₁₄.mem) ∧ Keep [.r12, .r0, .r6] s₁₄ t by
      rw [WP.block_append_iff]
      exact WP.mono (bufBase_ok hL hr14 (by decide)) fun u ⟨⟨a, mu⟩, ku⟩ =>
        WP.mono (getP_ok (hr14.keep ku) .r6) fun v ⟨⟨b, mv⟩, kv⟩ =>
          ⟨⟨(kv.gpr .r12 (by decide)).trans a, b, mv.trans mu⟩, (ku.trans kv).mono (by decide)⟩)
    fun s₁₅ ⟨⟨c12, c6, m15⟩, k15'⟩ => ?_)
  refine WP.mono (storeBE_ok (j := 7) (O := L.Buf) (k := L.pl) (en14.keep k15' (by decide)) (by decide)
    (ScrL.bufN (hs14.congr k15'.wr) hL (by omega)) c12 c6 (by omega) (by omega) (combBufPastP hL))
    fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m15] at vt ot
  have hplt : p < 2 ^ (8 * L.pl) := by
    rw [← p13, ← hw8, show 8 * (8 * L.wp) = 32 * (2 * L.wp) by omega]; exact val32_lt _ _ _ _
  have k10t := (((((k10.trans k11).trans k12).trans k13').trans k14).trans k15').trans kt
  have kc : Keep combRegs s t :=
    (((((((((((((((k1.mono (rs' := combRegs) (by decide)).trans' (k2.mono (by decide))).trans'
      (k3.mono (by decide))).trans' (k4.mono (by decide))).trans' (k5.mono (by decide))).trans'
      (k6.mono (by decide))).trans' (k7.mono (by decide))).trans' (k8.mono (by decide))).trans'
      (k9.mono (by decide))).trans' (k10.mono (by decide))).trans' (k11.mono (by decide))).trans'
      (k12.mono (by decide))).trans' (k13'.mono (by decide))).trans' (k14.mono (by decide))).trans'
      (k15'.mono (by decide))).trans' (kt.mono (by decide))
  refine ⟨⟨?_, ⟨en14.keep (k15'.trans kt) (by decide), (k10t.gpr .r21 (by decide)).trans in9.h21,
      (k10t.gpr .r23 (by decide)).trans in9.h23⟩,
    (pb14.pbody.body hL).trans (Body.ofBuf hL ot (by omega)),
    (comb_pbody_keepQ hL pb14.pbody).trans (combBufKeepQ ot (by omega))⟩, kc⟩
  rw [vt, read_low (w := L.wp) _ _ (by omega) (by omega), v7, v4, w4]
  rw [show off L.Buf 0 = L.Buf from BitVec.add_zero _]
  rfl

end VG.Proof.Dsa.PPC64LE
