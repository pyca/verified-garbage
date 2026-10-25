module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyBody
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.KeyPair
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Gk
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Sign
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.R
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Inverse
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.S
import VerifiedGarbage.Proof.Dsa.PPC64LE.Sign.Output
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets

/-!
# DSA signing on PPC64LE: after the check of the key

`sbody_ok`: `Sign.body` writes to `out` r's and s's `q_len` octets, most
significant first, and leaves 1 in `r3`, exactly when `0 < x < q`,
`0 < k < q`, `g^x mod p = y`, `r ≠ 0` and `s ≠ 0` (`SignOk`), for
`r = (g^k mod p) mod q` (`sigR`) and `s = k^(q − 2) (z + x r) mod q`
(`sigS`), z the digest's first `min(digest_len, bitLength q / 8)` octets;
else zeros and 0. Memory changes only in `scratch`, apart from the saved
registers, and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Sign
open VG.Proof.Bignum (slot)

/-- r, from the key and the nonce. -/
def sigR (p q g k : Nat) : Nat := g ^ k % p % q

/-- s, from x, the nonce, the digest's scalar and r. -/
def sigS (q x k z r : Nat) : Nat := k ^ (q - 2) % q * ((z % q + x * r % q) % q) % q

/-- The checks of signing past the public key's. -/
def SignOk (p q g y x k z : Nat) : Prop :=
  (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ sigR p q g k ≠ 0 ∧ sigS q x k z (sigR p q g k) ≠ 0

instance (p q g y x k z : Nat) : Decidable (SignOk p q g y x k z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A change past `scratch`'s header keeps its word `hOut`. -/
theorem Body.hOut {L : Lay} {m m' : Mem} (h : Body L m m') : word m' L.S hOut = word m L.S hOut :=
  Outside.word h (Or.inl (by decide)) (by decide)

/-- A change past `scratch`'s header keeps its word `hMask`. -/
theorem Body.hMask {L : Lay} {m m' : Mem} (h : Body L m m') : word m' L.S hMask = word m L.S hMask :=
  Outside.word h (Or.inl (by decide)) (by decide)

/-- `2^bitLength q ≤ 2 q`. -/
theorem pow_bitLength_le {q : Nat} (hq : q ≠ 0) : 2 ^ Spec.Dsa.bitLength q ≤ 2 * q := by
  simp only [Spec.Dsa.bitLength, hq, ite_false]
  rw [Nat.pow_succ]
  have := Nat.log2_self_le hq
  omega_arith

theorem encodeBE_zero (n : Nat) : Spec.Dsa.encodeBE n 0 = List.replicate n 0 := by
  rw [VG.Proof.Dsa.encodeBE_i2osp, VG.Proof.Bignum.i2osp_zero']

/-- Two values' octets, one after the other. -/
theorem out_bytes {m : Mem} {out : Addr} {ql a b : Nat} (ha : a < 256 ^ ql) (hb : b < 256 ^ ql)
    (h1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m out ql) = a)
    (h2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off out ql) ql) = b) :
    Spec.Rsa.bytesAt m out (2 * ql) = Spec.Dsa.encodeBE ql a ++ Spec.Dsa.encodeBE ql b := by
  have e1 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := 0) (len := ql) (by omega_arith)
  have e2 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := ql) (len := ql) (by omega_arith)
  simp only [List.drop_zero, BitVec.add_zero] at e1
  rw [List.take_of_length_le (by simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega_arith)] at e2
  rw [← List.take_append_drop ql (Spec.Rsa.bytesAt m out (2 * ql)), e1, e2,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) ha).mpr h1.symm,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) hb).mpr h2.symm]

/-- q fits in its `q_len` octets. -/
theorem qOf_lt {s₀ s : State} {L : Lay} {key : Addr} (hkp : Kept L s₀.mem s.mem)
    (hk : Src s L key (3 * L.pl + L.ql)) : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
  rw [← (key_kept hk hkp.out).2.1, qOf, ← VG.Proof.Bignum.pow256_eq]
  have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
  rwa [VG.Proof.Bignum.bytesAt_length] at this

/-- `Sign.body` up to `output` (here any `c`): `sValue` leaves r in the Q
space's array 9, s in its array 6, and in the header's word `hMask` the mask
of the checks but `s ≠ 0`, keeping `hOut`. -/
theorem sprefix_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hw : word s.mem L.S hOut = out)
    (hcont : ∀ t, QS t L key nonce dig → Kept L s.mem t.mem → word t.mem L.S hOut = out →
      word t.mem L.S hMask = mask (decide (gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key =
          yOf s₀.mem L key) &&
        decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < qOf s₀.mem L key) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key) ∧
          sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) ≠ 0)) →
      arrQ t.mem L 9 = sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) →
      arrQ t.mem L 6 = sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
        (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)) →
      Keep bodyRegs s t → WP isa c t Q) :
    WP isa (.seq keyPair (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
      (.seq sValue c))))))) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  have hw16 := hL.wp_ge
  have hw8 := hL.wp_eq
  have hbe := hL.buf_end
  have hq28 : L.qOff = slot L.wp 28 := rfl
  have hqZ : slot L.wp 28 + 1600 ≤ L.Z := by simp only [Lay.bOff, Lay.qOff] at hbe; omega_arith
  have e8 := Lay.slot_eq L.wp 8; have e28 := Lay.slot_eq L.wp 28
  obtain ⟨ip, scr, regs, p0, -, p8, q0, -, r2⟩ := hc
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega_arith)
  obtain ⟨-, -, eg, ey⟩ := key_kept hk3 hkp.out
  have hqlt := qOf_lt hkp hk3
  unfold KeyOk at hK
  generalize pOf s₀.mem L key = p at hK p0 p8 hcont
  generalize qOf s₀.mem L key = q at hK q0 r2 hqlt hcont
  generalize gOf s₀.mem L key = g at hK eg hcont
  generalize yOf s₀.mem L key = y at hK ey hcont
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hq8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
    have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega_arith
  generalize Spec.Dsa.bitLength q / 8 = n at r2 hq8 hcont
  have hnq : n ≤ L.ql := by
    have hq0 : q ≠ 0 := by omega_arith
    have hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega_arith
  -- The values read from outside `scratch`, kept.
  have hdgn : Src s L dig (min d n) := hdg.take (Nat.min_le_left _ _)
  have vals : ∀ {m : Mem}, Kept L s.mem m → xOf m L key = xOf s.mem L key ∧ kOf m L nonce = kOf s.mem L nonce ∧
      gOf m L key = g ∧ Spec.Rsa.bytesAt m dig (min d n) = Spec.Rsa.bytesAt s.mem dig (min d n) := fun hm =>
    ⟨by simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega_arith)).kept hm.out],
      by simp only [kOf]; rw [hn.kept hm.out], (key_kept hk3 hm.out).2.2.1.trans eg, hdgn.kept hm.out⟩
  generalize hX : xOf s.mem L key = X at vals hcont
  generalize kOf s.mem L nonce = K at vals hcont
  -- The mask of `g^x mod p = y`.
  refine WP.seq (WP.mono (keyPair_ok (p := p) hL scr regs ip hk p0 (by omega_arith) hpo p8)
    fun s₁ ⟨⟨mx₁, ip₁, o₁, p0₁, _, sav₁, hout₁⟩, k₁⟩ => ?_)
  rw [eg, ey, hX] at mx₁
  have K₁ : Kept L s.mem s₁.mem := ⟨o₁.mono (Nat.zero_le _) (by omega_arith), sav₁⟩
  have q0₁ : arrQ s₁.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (keepQ_of hL fun x hx => o₁ x (Or.inr (by omega_arith))) (by decide) (by decide)]
    exact q0
  have p8₁ : arrP s₁.mem L 8 = arrP s.mem L 8 :=
    Outside.val32 o₁ (Or.inr (by omega_arith)) (by omega_arith)
  -- `g^k mod p` to the buffer.
  refine WP.seq (WP.mono (gk_ok (p := p) hL (scr.congr k₁.wr) (regs.keep k₁) ip₁ (hk.keep k₁.rd k₁.wr)
      (hn.keep k₁.rd k₁.wr) (p0₁.trans p0) (by omega_arith) hpo (p8₁.trans p8))
    fun s₂ ⟨⟨gk₂, _, B₂, Qk₂, _, _, _⟩, k₂⟩ => ?_)
  rw [(vals K₁).2.2.1, (vals K₁).2.1] at gk₂
  have K₂ := K₁.trans (Kept.ofBody hL B₂)
  have k₁₂ := k₁.trans k₂
  have q0₂ : arrQ s₂.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₂ (by decide) (by decide)]; exact q0₁
  have mx₂ : word s₂.mem L.S hMask = mask (decide (g ^ X % p = y)) := (Body.hMask B₂).trans mx₁
  have hout₂ : word s₂.mem L.S hOut = out := ((Body.hOut B₂).trans hout₁).trans hw
  -- r, and the masks of the ranges.
  refine WP.seq (WP.mono (rRanges_ok hL (scr.congr k₁₂.wr) ((regs.keep k₁).keep k₂) (hk.keep k₁₂.rd k₁₂.wr)
      (hn.keep k₁₂.rd k₁₂.wr) (by rw [q0₂]; omega_arith) mx₂)
    fun s₃ ⟨⟨Q₃, r9₃, m₃, mf, fa, fb⟩, k₃⟩ => ?_)
  rw [q0₂, gk₂] at r9₃
  rw [q0₂, gk₂, (vals K₂).1, (vals K₂).2.1] at m₃
  have qa₃ : QArr L s₂.mem mf := QArr.of fa (Nat.le_refl _) (by decide)
  have K₃ := (K₂.trans (Kept.ofBody hL (qa₃.qbody.body hL))).trans (Kept.ofMask hL fb)
  have k₁₃ := k₁₂.trans k₃
  have q0₃ : arrQ s₃.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (mask_keepQ hL fb) (by decide) (by decide)]; exact qa₃.arr0.trans q0₂
  have hout₃ : word s₃.mem L.S hOut = out := by
    rw [Outside.word fb (Or.inr (by decide)) (by decide), Body.hOut (qa₃.qbody.body hL)]; exact hout₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ_ok Q₃ (by rw [q0₃]; omega_arith)) fun s₄ ⟨⟨Q₄, h8₄, qa₄, a9₄⟩, k₄⟩ => ?_)
  rw [q0₃] at h8₄
  have q0₄ : arrQ s₄.mem L 0 = q := qa₄.arr0.trans q0₃
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok Q₄ hL (by rw [q0₄]; omega_arith) (by rw [q0₄]; exact hqlt))
    fun s₅ ⟨⟨Q₅, bq₅, a8₅, qb₅, a9₅⟩, k₅⟩ => ?_)
  rw [q0₄] at bq₅
  have q0₅ : arrQ s₅.mem L 0 = q := qb₅.arr0.trans q0₄
  have B₃₅ : Body L s₃.mem s₅.mem := (qa₄.qbody.body hL).trans (qb₅.body hL)
  have K₅ := K₃.trans (Kept.ofBody hL B₃₅)
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  -- `w = k^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverseK_ok Q₅ hL (hn.keep k₁₅.rd k₁₅.wr) (by rw [q0₅]; omega_arith) (by rw [q0₅]; exact hqo)
      (by rw [a8₅, h8₄, q0₅])) fun s₆ ⟨⟨Q₆, w4₆, a8₆, qa₆, a9₆⟩, k₆⟩ => ?_)
  rw [q0₅, bq₅, (vals K₅).2.1] at w4₆
  have q0₆ : arrQ s₆.mem L 0 = q := qa₆.arr0.trans q0₅
  have B₃₆ := B₃₅.trans (qa₆.qbody.body hL)
  have K₆ := K₃.trans (Kept.ofBody hL B₃₆)
  have k₁₆ := k₁₅.trans k₆
  have r9₆ : arrQ s₆.mem L 9 = g ^ K % p % q := a9₆.trans (a9₅.trans (a9₄.trans r9₃))
  -- s.
  have hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₆.mem dig (min d n)) < 2 * arrQ s₆.mem L 0 := by
    rw [(vals K₆).2.2.2, q0₆]
    refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
    rw [VG.Proof.Bignum.bytesAt_length]
    refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right d n)) ?_
    have := pow_bitLength_le (q := q) (by omega_arith)
    rw [hq8, Nat.pow_mul] at this
    exact this
  refine WP.seq (WP.mono (sValue_ok Q₆ hL ((k₁₆.gpr .r2 (by decide)).trans r2) hnq hd
      (hdgn.keep k₁₆.rd k₁₆.wr) (hk.keep k₁₆.rd k₁₆.wr) (by rw [q0₆]; omega_arith) (by rw [q0₆]; exact hqo)
      (by rw [a8₆, a8₅, h8₄, q0₆]) (by rw [w4₆, q0₆]; exact Nat.mod_lt _ (by omega_arith))
      (by rw [r9₆, q0₆]; exact Nat.mod_lt _ (by omega_arith)) hz)
    fun s₇ ⟨⟨Q₇, s6₇, a9₇, qa₇⟩, k₇⟩ => ?_)
  rw [q0₆, w4₆, r9₆, (vals K₆).1, (vals K₆).2.2.2] at s6₇
  have B₃₇ := B₃₆.trans (qa₇.qbody.body hL)
  exact hcont s₇ Q₇ (K₃.trans (Kept.ofBody hL B₃₇)) ((Body.hOut B₃₇).trans hout₃) ((Body.hMask B₃₇).trans m₃)
    (a9₇.trans r9₆) s6₇ (keep_but21 (k₁₆.trans k₇) (by decide) (by decide))

theorem sbody_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key nonce dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d)
    (hw : word s.mem L.S hOut = out) (ho : Scr s out (2 * L.ql)) (hos : Src s L out (2 * L.ql)) :
    WP isa Sign.body s fun t =>
      (Spec.Rsa.bytesAt t.mem out (2 * L.ql) =
          (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
              (xOf s.mem L key) (kOf s.mem L nonce)
              (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            then Spec.Dsa.encodeBE L.ql (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
                (kOf s.mem L nonce)) ++
              Spec.Dsa.encodeBE L.ql (sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
                (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
                (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)))
            else List.replicate (2 * L.ql) 0) ∧
        t.gpr .r3 = BitVec.ofNat 64 (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
            (yOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
          then 1 else 0) ∧
        (∃ m, Kept L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧
        Keep bodyRegs s t := by
  have hqlt := qOf_lt hkp (hk.take (by omega_arith))
  have scr := hc.scr
  unfold Sign.body
  refine sprefix_ok hL hK hc hkp hk hn hd hdg hw fun s₇ Q₇ K₇ hout₇ m₇ r9₇ s6₇ k₁₇ => ?_
  unfold KeyOk at hK
  generalize pOf s₀.mem L key = p at hK m₇ r9₇ s6₇ ⊢
  generalize qOf s₀.mem L key = q at hK hqlt m₇ r9₇ s6₇ ⊢
  generalize gOf s₀.mem L key = g at hK m₇ r9₇ s6₇ ⊢
  generalize yOf s₀.mem L key = y at hK m₇ ⊢
  generalize xOf s.mem L key = X at m₇ s6₇ ⊢
  generalize kOf s.mem L nonce = K at m₇ r9₇ s6₇ ⊢
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength q / 8))) = Z at s6₇ ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  -- The output.
  have hrq : sigR p q g K < q := Nat.mod_lt _ (by omega_arith)
  have hsq : sigS q X K Z (sigR p q g K) < q := Nat.mod_lt _ (by omega_arith)
  refine WP.mono (output_ok hL Q₇ hout₇ m₇
      (ho.congr k₁₇.wr) (hos.keep k₁₇.rd k₁₇.wr) (by rw [r9₇]; omega_arith) (by rw [s6₇]; omega_arith))
    fun t ⟨⟨o1, o2, t3, mo, qo, oo⟩, kt⟩ => ?_
  rw [r9₇, s6₇] at o1
  rw [s6₇] at o2 t3
  have hcb : (decide (g ^ X % p = y) && decide ((0 < K ∧ K < q) ∧ (0 < X ∧ X < q) ∧ sigR p q g K ≠ 0) &&
      decide (sigS q X K Z (sigR p q g K) ≠ 0)) = decide (SignOk p q g y X K Z) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold SignOk sigR
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨h3, h2, h1, h4, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h3, h2, h1, h4⟩, h5⟩
  rw [hcb] at o1 o2 t3
  have h256 : ∀ v, v < q → v < 256 ^ L.ql := fun v hv => by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; omega_arith
  refine ⟨⟨?_, ?_, ⟨mo, K₇.trans (Kept.ofBody hL (qo.qbody.body hL)), oo⟩,
    (kt.gpr .r21 (by decide)).trans Q₇.inq.h21, scr.congr (k₁₇.trans kt).wr⟩,
    keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩
  · by_cases hc : SignOk p q g y X K Z
    · simp only [hc, decide_true, ite_true] at o1 o2 ⊢
      exact out_bytes (h256 _ hrq) (h256 _ hsq) o1 o2
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at o1 o2 ⊢
      rw [out_bytes (Nat.pow_pos (by decide : 0 < 256)) (Nat.pow_pos (by decide : 0 < 256)) o1 o2, encodeBE_zero,
        List.replicate_append_replicate, Nat.two_mul]
  · rw [t3]
    simp only [decide_eq_true_eq]

end VG.Proof.Dsa.PPC64LE
