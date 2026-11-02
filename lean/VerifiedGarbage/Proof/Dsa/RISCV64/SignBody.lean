module

public import VerifiedGarbage.Proof.Dsa.RISCV64.SignGk
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignR
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignInverse
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignS
public import VerifiedGarbage.Proof.Dsa.RISCV64.SignOutput
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA signing on RISC-V: after the check of the key

As on PPC64LE (`Proof/Dsa/PPC64LE/Sign/Body.lean`). `sbody_ok`: `Sign.body`
writes to `out` r's and s's `q_len` octets, most significant first, and
leaves 1 in `a0`, exactly when `0 < x < q`, `0 < k < q`, `g^x mod p = y`,
`r ≠ 0` and `s ≠ 0` (`SignOk`), for `r = (g^k mod p) mod q` (`sigR`) and
`s = k^(q − 2) (z + x r) mod q` (`sigS`), z the digest's first
`min(digest_len, bitLength q / 8)` octets; else zeros and 0. Memory changes
only in `scratch`'s `hMask` and past its header (`BKept`), and in `out`.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Sign
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- r, from the key and the nonce. -/
def sigR (p q g k : Nat) : Nat := g ^ k % p % q

/-- s, from x, the nonce, the digest's scalar and r. -/
def sigS (q x k z r : Nat) : Nat := k ^ (q - 2) % q * ((z % q + x * r % q) % q) % q

/-- The checks of signing past the public key's. -/
def SignOk (p q g y x k z : Nat) : Prop :=
  (0 < x ∧ x < q) ∧ (0 < k ∧ k < q) ∧ g ^ x % p = y ∧ sigR p q g k ≠ 0 ∧ sigS q x k z (sigR p q g k) ≠ 0

instance (p q g y x k z : Nat) : Decidable (SignOk p q g y x k z) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `2^bitLength q ≤ 2 q`. -/
theorem pow_bitLength_le {q : Nat} (hq : q ≠ 0) : 2 ^ Spec.Dsa.bitLength q ≤ 2 * q := by
  simp only [Spec.Dsa.bitLength, hq, ite_false]
  rw [Nat.pow_succ]
  have := Nat.log2_self_le hq
  omega

theorem encodeBE_zero (n : Nat) : Spec.Dsa.encodeBE n 0 = List.replicate n 0 := by
  rw [VG.Proof.Dsa.encodeBE_i2osp, VG.Proof.Bignum.i2osp_zero']

/-- Two values' octets, one after the other. -/
theorem out_bytes {m : Mem} {out : Addr} {ql a b : Nat} (ha : a < 256 ^ ql) (hb : b < 256 ^ ql)
    (h1 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m out ql) = a)
    (h2 : Spec.Rsa.os2ip (Spec.Rsa.bytesAt m (off out ql) ql) = b) :
    Spec.Rsa.bytesAt m out (2 * ql) = Spec.Dsa.encodeBE ql a ++ Spec.Dsa.encodeBE ql b := by
  have e1 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := 0) (len := ql) (by omega)
  have e2 := VG.Proof.Dsa.bytesAt_slice m out (total := 2 * ql) (offset := ql) (len := ql) (by omega)
  simp only [List.drop_zero, BitVec.add_zero] at e1
  rw [List.take_of_length_le (by simp only [List.length_drop, VG.Proof.Bignum.bytesAt_length]; omega)] at e2
  rw [← List.take_append_drop ql (Spec.Rsa.bytesAt m out (2 * ql)), e1, e2,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) ha).mpr h1.symm,
    (VG.Proof.Dsa.encodeBE_eq_bytes (VG.Proof.Bignum.bytesAt_length _ _ _) hb).mpr h2.symm]

/-- `Regs` through a change in `hMask` and past the header. -/
theorem Regs.ofBKept {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : Regs s L key sig)
    (k : Keep rs s t) (hb : BKept L s.mem t.mem) (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  h.keepHdr k (hb.word (by decide) (by decide)) hr

theorem mask_keepQ' {L : Lay} (hL : L.Ok) {m m₁ m' : Mem} (h₁ : QArr L m m₁) (h₂ : Outside L.S hMask 8 m₁ m') :
    arrQ m' L 0 = arrQ m L 0 :=
  (keepQ_arr0 hL (mask_keepQ hL h₂)).trans (h₁.arr0 hL)

/-- `rrQ_ok`, and arrays 25–27 kept. -/
theorem rrQ25_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) :
    WP isa Verify.rrQ s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧
        (∀ j < 28, 25 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep rrQRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e25 := Lay.slot_eq L.wq 25
  have e28 := Lay.slot_eq L.wq 28
  unfold Verify.rrQ
  have hodd : (word s.mem L.Q (slot L.wq 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wq) (by omega)]; exact hqo
  refine WP.seq (WP.mono (minv_ok e.hs e.a7 (slot_al _ _) (by omega) hodd) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  have e1' := e.keep k1
  refine WP.mono (rr_ok e1' (by rw [m1]; exact hq)) fun t ⟨⟨_, r24, o⟩, kt⟩ => ?_
  rw [m1] at r24 o
  have qa : QArr L s.mem t.mem := QArr.of o (by omega) (by omega)
  refine ⟨⟨h.step (k1.trans kt) (qa.body hL), ?_, r24, fun j hj hj25 => ?_, qa⟩, k1.trans kt⟩
  · show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o.word (by omega) (by omega), kt.gpr (by decide)]
    exact i1
  · have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj25
    exact o.wordsVal (Or.inr (by omega)) (by omega)

/-- The registers of `Sign.body` up to `output`. -/
def sprefixRegs : List Reg :=
  keyPairRegs ++ gkRegs ++ rRangesRegs ++ rrQRegs ++ qm2Regs ++ invRegs ++ sValueRegs

/-- `Sign.body` up to `output` (here any `c`): `sValue` leaves r in the Q
space's array 25, s in its array 6, and in the header's word `hMask` the mask
of the checks but `s ≠ 0`. -/
theorem sprefix_ok {s₀ s : State} {L : Lay} {key nonce dig : Addr} {d : Nat} {c : Prog isa}
    {Q : State → Prop}
    (hL : L.Ok) (hK : ParamsOk s₀.mem L key) (hc : Checked s₀ s L key nonce d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig)
    (hcont : ∀ t, QS t L key nonce → BKept L s.mem t.mem →
      word t.mem L.S hMask = mask (decide (gOf s₀.mem L key ^ xOf s.mem L key % pOf s₀.mem L key =
          yOf s₀.mem L key) &&
        decide ((0 < kOf s.mem L nonce ∧ kOf s.mem L nonce < qOf s₀.mem L key) ∧
          (0 < xOf s.mem L key ∧ xOf s.mem L key < qOf s₀.mem L key) ∧
          sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) ≠ 0)) →
      arrQ t.mem L 25 = sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce) →
      arrQ t.mem L 6 = sigS (qOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
        (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
        (sigR (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (kOf s.mem L nonce)) →
      Keep sprefixRegs s t → WP isa c t Q) :
    WP isa (.seq keyPair (.seq gk (.seq rRanges (.seq Verify.rrQ (.seq Verify.qMinus2 (.seq inverseK
      (.seq sValue c))))))) s Q := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  obtain ⟨ip, scr, regs, p0, -, inv, p24, q0, -, lens⟩ := hc
  have hk3 : Src s L key (3 * L.pl + L.ql) := hk.take (by omega)
  have hk2 : Src s L key (2 * L.pl + L.ql) := hk.take (by omega)
  obtain ⟨-, eq, eg⟩ := params_kept hk2 hkp
  have ey := y_kept hk3 hkp
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  unfold ParamsOk at hK
  generalize pOf s₀.mem L key = p at hK p0 p24 hcont
  generalize qOf s₀.mem L key = q at hK q0 lens hqlt hcont
  generalize gOf s₀.mem L key = g at hK eg hcont
  generalize yOf s₀.mem L key = y at ey hcont
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hq8 : Spec.Dsa.bitLength q = 8 * (Spec.Dsa.bitLength q / 8) := by
    have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega
  have hnq : Spec.Dsa.bitLength q / 8 ≤ L.ql := q_bits (by omega) hqlt
  generalize Spec.Dsa.bitLength q / 8 = n at lens hq8 hnq hcont
  -- The values read from outside `scratch`, kept.
  have hdgn : Src s L dig (min d n) := hdg.take (Nat.min_le_left _ _)
  have vals : ∀ {m : Mem}, BKept L s.mem m → xOf m L key = xOf s.mem L key ∧ kOf m L nonce = kOf s.mem L nonce ∧
      gOf m L key = g ∧ yOf m L key = y ∧ Spec.Rsa.bytesAt m dig (min d n) = Spec.Rsa.bytesAt s.mem dig (min d n) :=
    fun hm => ⟨by simp only [xOf]; rw [(hk.sub (o := 3 * L.pl + L.ql) (k := L.ql) (by omega)).bytes hm.out (by omega)],
      by simp only [kOf]; rw [hn.bytes hm.out (by omega)],
      by simp only [gOf]; rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega)).bytes hm.out (by omega)]; exact eg,
      by simp only [yOf]; rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes hm.out (by omega)]; exact ey,
      hdgn.bytes hm.out (by omega)⟩
  generalize hX : xOf s.mem L key = X at vals hcont
  generalize kOf s.mem L nonce = K at vals hcont
  -- The mask of `g^x mod p = y`.
  refine WP.seq (WP.mono (keyPair_ok (p := p) hL scr regs ip inv hk p0 (by omega) hpo p24)
    fun s₁ ⟨⟨mx₁, ip₁, i₁, m₁, o₁, w₁⟩, k₁⟩ => ?_)
  rw [(vals (BKept.refl _ _)).2.2.1, (vals (BKept.refl _ _)).2.2.2.1, hX] at mx₁
  have K₁ : BKept L s.mem s₁.mem := (BKept.ofBody hL (PLow.body hL o₁)).trans (BKept.ofMask hL w₁)
  have q0₁ : arrQ s₁.mem L 0 = q := by
    rw [keepQ_arr0 hL (mask_keepQ hL w₁), keepQ_arr0 hL (PLow.keepQ hL o₁)]; exact q0
  have p0₁ : arrP s₁.mem L 0 = p := by rw [mask_arrP hL w₁ 0 (by decide), PLow.arr hL o₁ (by decide) (.inl rfl)]; exact p0
  have p24₁ : arrP s₁.mem L 24 = 2 ^ (128 * L.wp) % p := by
    rw [mask_arrP hL w₁ 24 (by decide), PLow.arr hL o₁ (by decide) (.inr (by decide))]; exact p24
  have hr₁ := regs.ofBKept k₁ K₁
  -- `g^k mod p` to the buffer.
  refine WP.seq (WP.mono (gk_ok (p := p) hL (scr.congr k₁.2.2) hr₁ ip₁ i₁ (hk2.keep k₁.2.1 k₁.2.2)
      (hn.keep k₁.2.1 k₁.2.2) p0₁ (by omega) hpo p24₁)
    fun s₂ ⟨⟨gk₂, _, _, m₂, o₂, b₂⟩, k₂⟩ => ?_)
  rw [(vals K₁).2.2.1, (vals K₁).2.1] at gk₂
  have B₂ : Body L s₁.mem s₂.mem := (PLow.body hL o₂).trans (Body.ofBuf hL b₂ (by omega))
  have K₂ := K₁.trans (BKept.ofBody hL B₂)
  have k₁₂ := k₁.trans k₂
  have q0₂ : arrQ s₂.mem L 0 = q := by
    rw [keepQ_arr0 hL (bufKeepQ b₂ (by omega)), keepQ_arr0 hL (PLow.keepQ hL o₂)]; exact q0₁
  have mx₂ : word s₂.mem L.S hMask = mask (decide (g ^ X % p = y)) := (B₂.word (by decide)).trans mx₁
  -- r, and the masks of the ranges.
  refine WP.seq (WP.mono (rRanges_ok hL (scr.congr k₁₂.2.2) (regs.ofBKept k₁₂ K₂) (hk.keep k₁₂.2.1 k₁₂.2.2)
      (hn.keep k₁₂.2.1 k₁₂.2.2) (by rw [q0₂]; omega) mx₂)
    fun s₃ ⟨⟨Q₃, r25₃, m₃, mf, fa, fb⟩, k₃⟩ => ?_)
  rw [q0₂, gk₂] at r25₃
  rw [q0₂, gk₂, (vals K₂).1, (vals K₂).2.1] at m₃
  have K₃ := (K₂.trans (BKept.ofBody hL (fa.body hL))).trans (BKept.ofMask hL fb)
  have k₁₃ := k₁₂.trans k₃
  have q0₃ : arrQ s₃.mem L 0 = q := (mask_keepQ' hL fa fb).trans q0₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ25_ok hL Q₃ (by rw [q0₃]; omega) (by rw [q0₃]; exact hqo))
    fun s₄ ⟨⟨Q₄, I₄, h24₄, a25₄, qa₄⟩, k₄⟩ => ?_)
  rw [q0₃] at h24₄
  have q0₄ : arrQ s₄.mem L 0 = q := (qa₄.arr0 hL).trans q0₃
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok hL Q₄ (by rw [q0₄]; omega) (by rw [q0₄]; exact hqlt))
    fun s₅ ⟨⟨Q₅, bq₅, kj₅, w0₅, qb₅⟩, k₅⟩ => ?_)
  rw [q0₄] at bq₅
  have q0₅ : arrQ s₅.mem L 0 = q := (kj₅ 0 (by decide) (by decide)).trans q0₄
  have I₅ : QInv s₅ L := I₄.keepW w0₅ (k₅.gpr (by decide))
  have K₅ := K₃.trans (BKept.ofBody hL ((qa₄.body hL).trans (qb₅.body hL)))
  have k₁₅ := (k₁₃.trans k₄).trans k₅
  -- `w = k^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverseK_ok hL Q₅ I₅ (hn.keep k₁₅.2.1 k₁₅.2.2) (by rw [q0₅]; omega)
      (by rw [q0₅]; exact hqo) (by rw [q0₅, kj₅ 24 (by decide) (by decide)]; exact h24₄))
    fun s₆ ⟨⟨Q₆, I₆, w4₆, k24₆, qa₆⟩, k₆⟩ => ?_)
  rw [q0₅, bq₅, (vals K₅).2.1] at w4₆
  have q0₆ : arrQ s₆.mem L 0 = q := (qa₆.arr0 hL).trans q0₅
  have K₆ := K₅.trans (BKept.ofBody hL (qa₆.body hL))
  have k₁₆ := k₁₅.trans k₆
  have r25₆ : arrQ s₆.mem L 25 = g ^ K % p % q :=
    (k24₆ 25 (by decide) (by decide)).trans ((kj₅ 25 (by decide) (by decide)).trans
      ((a25₄ 25 (by decide) (by decide)).trans r25₃))
  -- s.
  have hz : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s₆.mem dig (min d n)) < 2 * arrQ s₆.mem L 0 := by
    rw [(vals K₆).2.2.2.2, q0₆]
    refine Nat.lt_of_lt_of_le (VG.Proof.Dsa.decodeBE_lt _) ?_
    rw [VG.Proof.Bignum.bytesAt_length]
    refine Nat.le_trans (Nat.pow_le_pow_right (by decide) (Nat.min_le_right d n)) ?_
    have := pow_bitLength_le (q := q) (by omega)
    rw [hq8, Nat.pow_mul] at this
    exact this
  refine WP.seq (WP.mono (sValue_ok hL Q₆ I₆ (by rw [K₆.word (by decide) (by decide)]; exact hdg8)
      (by rw [K₆.word (by decide) (by decide)]; exact lens) hnq hd
      (hdgn.keep k₁₆.2.1 k₁₆.2.2) (hk.keep k₁₆.2.1 k₁₆.2.2) (by rw [q0₆]; omega) (by rw [q0₆]; exact hqo)
      (by rw [k24₆ 24 (by decide) (by decide), kj₅ 24 (by decide) (by decide), h24₄, q0₆])
      (by rw [w4₆, q0₆]; exact Nat.mod_lt _ (by omega))
      (by rw [r25₆, q0₆]; exact Nat.mod_lt _ (by omega)) hz)
    fun s₇ ⟨⟨Q₇, _, s6₇, a25₇, qa₇⟩, k₇⟩ => ?_)
  rw [q0₆, w4₆, r25₆, (vals K₆).1, (vals K₆).2.2.2.2] at s6₇
  exact hcont s₇ Q₇ (K₆.trans (BKept.ofBody hL (qa₇.body hL))) (((qa₄.body hL).trans
    ((qb₅.body hL).trans ((qa₆.body hL).trans (qa₇.body hL)))).word (by decide) |>.trans m₃)
    (a25₇.trans r25₆) s6₇ (by
      have := k₁₆.trans k₇; simp only [sprefixRegs, List.append_assoc] at this ⊢; exact this)

/-- The registers `Sign.body` writes. -/
def sbodyRegs : List Reg := sprefixRegs ++ outputRegs

theorem sbody_ok {s₀ s : State} {L : Lay} {key nonce dig out : Addr} {d : Nat}
    (hL : L.Ok) (hK : ParamsOk s₀.mem L key) (hc : Checked s₀ s L key nonce d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + 2 * L.ql)) (hn : Src s L nonce L.ql)
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig)
    (hw : word s.mem L.S Sign.hOut = out) (hout : ∀ i < 2 * L.ql, InRegions s.wr (off out i) 1)
    (hno : out.toNat + 2 * L.ql ≤ 2 ^ 64) (hos : Src s L out (2 * L.ql)) :
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
        t.gpr .a0 = BitVec.ofNat 64 (if SignOk (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key)
            (yOf s₀.mem L key) (xOf s.mem L key) (kOf s.mem L nonce)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
          then 1 else 0) ∧
        (∃ m, BKept L s.mem m ∧ Outside out 0 (2 * L.ql) m t.mem) ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧
        Keep sbodyRegs s t := by
  have scr := hc.scr
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    have eq := (params_kept (hk.take (k := 2 * L.pl + L.ql) (by omega)) hkp).2.1
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  unfold Sign.body
  refine sprefix_ok hL hK hc hkp hk hn hd hdg hdg8 fun s₇ Q₇ K₇ m₇ r25₇ s6₇ k₁₇ => ?_
  unfold ParamsOk at hK
  generalize pOf s₀.mem L key = p at hK m₇ r25₇ s6₇ ⊢
  generalize qOf s₀.mem L key = q at hK hqlt m₇ r25₇ s6₇ ⊢
  generalize gOf s₀.mem L key = g at hK m₇ r25₇ s6₇ ⊢
  generalize yOf s₀.mem L key = y at m₇ ⊢
  generalize xOf s.mem L key = X at m₇ s6₇ ⊢
  generalize kOf s.mem L nonce = K at m₇ r25₇ s6₇ ⊢
  generalize Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d (Spec.Dsa.bitLength q / 8))) = Z at s6₇ ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  -- The output.
  have hrq : sigR p q g K < q := Nat.mod_lt _ (by omega)
  have hsq : sigS q X K Z (sigR p q g K) < q := Nat.mod_lt _ (by omega)
  refine WP.mono (output_ok hL Q₇ (by rw [K₇.word (by decide) (by decide)]; exact hw) m₇
      (fun i hi => by rw [k₁₇.2.2]; exact hout i hi) hno (hos.keep k₁₇.2.1 k₁₇.2.2)
      (by rw [r25₇]; omega) (by rw [s6₇]; omega))
    fun t ⟨⟨o1, o2, t0, mo, qo, oo⟩, kt⟩ => ?_
  rw [r25₇, s6₇] at o1
  rw [s6₇] at o2 t0
  have hcb : (decide (g ^ X % p = y) && decide ((0 < K ∧ K < q) ∧ (0 < X ∧ X < q) ∧ sigR p q g K ≠ 0) &&
      decide (sigS q X K Z (sigR p q g K) ≠ 0)) = decide (SignOk p q g y X K Z) := by
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    unfold SignOk sigR
    constructor
    · rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩; exact ⟨h3, h2, h1, h4, h5⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨⟨h3, h2, h1, h4⟩, h5⟩
  rw [hcb] at o1 o2 t0
  have h256 : ∀ v, v < q → v < 256 ^ L.ql := fun v hv => by
    rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; omega
  have kall := k₁₇.trans kt
  refine ⟨⟨?_, ?_, ⟨mo, K₇.trans (BKept.ofBody hL (qo.body hL)), oo⟩,
    (kt.gpr (by decide)).trans Q₇.regs.s6, scr.congr kall.2.2⟩, ?_⟩
  · by_cases hc : SignOk p q g y X K Z
    · simp only [hc, decide_true, ite_true] at o1 o2 ⊢
      exact out_bytes (h256 _ hrq) (h256 _ hsq) o1 o2
    · simp only [hc, decide_false, Bool.false_eq_true, ite_false] at o1 o2 ⊢
      rw [out_bytes (Nat.pow_pos (by decide : 0 < 256)) (Nat.pow_pos (by decide : 0 < 256)) o1 o2, encodeBE_zero,
        List.replicate_append_replicate, Nat.two_mul]
  · rw [t0]
    simp only [decide_eq_true_eq]
  · exact kall

end VG.Proof.Dsa.RISCV64
