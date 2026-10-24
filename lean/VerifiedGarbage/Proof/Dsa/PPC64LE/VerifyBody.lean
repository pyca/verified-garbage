module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyProd
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyEnd
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: after the check of the key

`body_ok`: `Verify.body` leaves in `r3` 1 exactly when r and s are in
`(0, q)` and `(g^u1 y^u2 mod p) mod q = r`, for `w = s^(q − 2) mod q`,
`u1 = z w mod q` and `u2 = r w mod q` (`vComp`), z the digest's first
`min(digest_len, bitLength q / 8)` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- The value verification compares with r. -/
def vComp (p q g y z r s : Nat) : Nat :=
  (g ^ (z * (s ^ (q - 2) % q) % q) % p * (y ^ (r * (s ^ (q - 2) % q) % q) % p) % p) % q

/-- Memory that changed only at offsets below `qOff` of `scratch` keeps the Q space. -/
theorem keepQ_of {L : Lay} (hL : L.Ok) {m m' : Mem} (h : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  have hlt := (x - L.S).isLt
  have hlt' := (x - L.Q).isLt
  refine h x ?_
  simp only [ofs, Lay.Q, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · exact hd
  · rw [Nat.mod_eq_of_lt (by omega)] at hx; omega

/-- A change in the Q space's arrays or the buffer keeps the P space. -/
theorem QBuf.keepP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    Outside L.S (L.qOff + slot 4 1) (1600 + 2 * L.pl - slot 4 1) m m' := by
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  exact outside_shift (B := L.S) (a := L.qOff) h (by have := hL.pl; rw [show slot 4 1 = 304 from rfl]; omega)
    (by omega)

theorem QBuf.arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') {j : Nat} (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  exact Outside.val32 (h.keepP hL) (Or.inl (by simp only [Lay.qOff] at *; omega))
    (by have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at *; omega)

theorem QBuf.ptop {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    word m' L.S (slot L.wp 0 + 8 * L.wp) = word m L.S (slot L.wp 0 + 8 * L.wp) := by
  have := slot_lt (w := L.wp) (show 0 < 28 by decide)
  exact Outside.word (h.keepP hL) (Or.inl (by simp only [Lay.qOff] at *; omega))
    (by have := hL.nowrap; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at *; omega)

/-- A buffer's first `min n k` octets. -/
theorem bytesAt_take (m : Mem) (D : Addr) (n k : Nat) :
    (Spec.Rsa.bytesAt m D n).take k = Spec.Rsa.bytesAt m D (min n k) := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_comm]


/-- The first octets of a buffer apart from `scratch`. -/
theorem Src.take {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) {k : Nat} (hk : k ≤ n) :
    Src s L D k :=
  ⟨fun i hi => h.rd i (by omega), fun i hi => h.sep i (by omega)⟩

/-- The change of the digest's length in the header. -/
theorem Kept.ofDl {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hDlen 8 m m') : Kept L m m' :=
  ⟨h.mono (by decide) (by have := hL.z256; simp only [hDlen]; omega), fun i hi =>
    Outside.word h (Or.inr (by simp only [saveOff, hDlen]; omega))
      (by have := hL.nowrap; have := hL.z256; simp only [saveOff]; omega)⟩

/-- The signature's and the digest's values, kept. -/
theorem sig_kept {s : State} {L : Lay} {sig dig : Addr} {D : Nat} (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) {m m' : Mem} (h : Kept L m m') (hZ : 72 ≤ L.Z) {k : Nat} (hk : k ≤ D) :
    rOf m' L sig = rOf m L sig ∧ sOf m' L sig = sOf m L sig ∧
      Spec.Rsa.bytesAt m' dig k = Spec.Rsa.bytesAt m dig k := by
  refine ⟨?_, ?_, (hdg.take hk).kept h hZ⟩
  · have e := (hsg.sub (o := 0) (k := L.ql) (by omega)).kept h hZ
    simp only [off, BitVec.add_zero] at e
    simp only [rOf]; rw [e]
  · simp only [sOf]; rw [(hsg.sub (o := L.ql) (k := L.ql) (by omega)).kept h hZ]

/-- Every register but `r2` (the TOC pointer, never written) and `r21` (which keeps `S`). -/
def notR21 : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem keep_but21 {rs : List Reg} {s t : State} (h : Keep rs s t) (hr : Reg.r21 ∉ rs) (hr2 : Reg.r2 ∉ rs) :
    Keep notR21 s t :=
  h.mono fun r hm => by
    have : r ≠ .r21 := fun e => hr (e ▸ hm)
    have : r ≠ .r2 := fun e => hr2 (e ▸ hm)
    cases r <;> simp_all [notR21]

/-- The registers `Verify.body` writes: all but `r21`. -/
abbrev bodyRegs : List Reg := notR21

theorem body_ok {s₀ s : State} {L : Lay} {key sig dig : Addr} {D : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key sig dig)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + L.ql)) (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) (hD : word s.mem L.S hDlen = BitVec.ofNat 64 D) (hDlt : D < 2 ^ 64) :
    WP isa Verify.body s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < qOf s₀.mem L key) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < qOf s₀.mem L key)) ∧
          vComp (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig
              (min D (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            (rOf s.mem L sig) (sOf s.mem L sig) = rOf s.mem L sig then 1 else 0) ∧
        Kept L s.mem t.mem ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  obtain ⟨ip, scr, hdr, p0, ptop, p8, q0, qtop, qbw, -⟩ := hc
  obtain ⟨ep, eq, eg, ey⟩ := key_kept hk hkp (by omega)
  unfold KeyOk at hK
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p8 ⊢
  generalize hq : qOf s₀.mem L key = q at hK q0 qbw hqlt ⊢
  generalize hgg : gOf s₀.mem L key = g at hK ⊢
  generalize hyy : yOf s₀.mem L key = y at hK ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hqb : Spec.Dsa.bitLength q ≤ 256 := by have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega
  generalize hn : Spec.Dsa.bitLength q / 8 = n at qbw ⊢
  have hnq : n ≤ L.ql := by
    have hq0 : q ≠ 0 := by omega
    have hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega
  have hn32 : n ≤ 32 := by omega
  unfold Verify.body
  refine WP.seq (WP.mono (digestLen_ok hL scr ip.h21 hD hDlt qbw hn32) fun s₁ ⟨⟨d1, o1⟩, k1⟩ => ?_)
  have K₁ := Kept.ofDl hL o1
  have Q₁ : Outside L.Q 1600 (2 ^ 64 - 1600) s.mem s₁.mem := keepQ_of hL fun x hx => o1 x (Or.inr (by
    have := L.qOff; simp only [hDlen, Lay.qOff, Lay.slot_eq] at hx ⊢; omega))
  have q0₁ : arrQ s₁.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Q₁ (by decide) (by decide)]; exact q0
  have p0₁ : arrP s₁.mem L 0 = p := by
    rw [arrP, arr, Outside.val32 o1 (by simp only [hDlen, Lay.slot_eq]; omega)
      (by have := hL.wp_ge; simp only [Lay.slot_eq]; omega)]
    exact p0
  have p8₁ : arrP s₁.mem L 8 = 2 ^ (128 * L.wp) % p := by
    rw [arrP, arr, Outside.val32 o1 (by simp only [hDlen, Lay.slot_eq]; omega)
      (by have := hL.wp_ge; simp only [Lay.slot_eq]; omega)]
    exact p8
  have hdr₁ := hdr.kept K₁ hL
  have scr₁ : ScrL s₁ L := scr.congr k1.wr
  have h21₁ : s₁.gpr .r21 = L.S := (k1.gpr .r21 (by decide)).trans ip.h21
  have sv₁ := sig_kept hsg hdg K₁ (by omega) (Nat.zero_le D)
  -- r and s in range.
  refine WP.seq (WP.mono (ranges_ok hL scr₁ hdr₁ h21₁ (hsg.keep k1.rd k1.wr))
    fun s₂ ⟨⟨Q₂, r5₂, m26, qa₂⟩, k₂⟩ => ?_)
  rw [q0₁, sv₁.1, sv₁.2.1] at m26
  have k₁₂ := k1.trans k₂
  have q0₂ : arrQ s₂.mem L 0 = q := qa₂.arr0.trans q0₁
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ_ok Q₂ (by rw [q0₂]; omega)) fun s₃ ⟨⟨Q₃, h8₃, qa₃⟩, k₃⟩ => ?_)
  rw [q0₂] at h8₃
  have q0₃ : arrQ s₃.mem L 0 = q := qa₃.arr0.trans q0₂
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok Q₃ hL (by rw [q0₃]; omega) (by rw [q0₃]; exact hqlt))
    fun s₄ ⟨⟨Q₄, bq₄, a8₄, qb₄⟩, k₄⟩ => ?_)
  rw [q0₃] at bq₄
  have q0₄ : arrQ s₄.mem L 0 = q := qb₄.arr0.trans q0₃
  have k₁₄ := (k₁₂.trans k₃).trans k₄
  have B₁₄ : Body L s₁.mem s₄.mem := ((qa₂.qbody.body hL).trans (qa₃.qbody.body hL)).trans (qb₄.body hL)
  have K₄ := K₁.trans (Kept.ofBody hL B₁₄)
  -- `w = s^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverse_ok Q₄ hL (hsg.keep k₁₄.rd k₁₄.wr) (by rw [q0₄]; omega) (by rw [q0₄]; exact hqo)
      (by rw [a8₄, h8₃, q0₄])) fun s₅ ⟨⟨Q₅, w4₅, a8₅, qa₅⟩, k₅⟩ => ?_)
  rw [q0₄, bq₄, (sig_kept hsg hdg K₄ (by omega) (Nat.zero_le D)).2.1] at w4₅
  have q0₅ : arrQ s₅.mem L 0 = q := qa₅.arr0.trans q0₄
  have k₁₅ := k₁₄.trans k₅
  have B₁₅ := B₁₄.trans (qa₅.qbody.body hL)
  have K₅ := K₁.trans (Kept.ofBody hL B₁₅)
  have hD₅ : word s₅.mem L.S hDlen = BitVec.ofNat 64 (min D n) := by
    rw [Outside.word B₁₅ (Or.inl (by decide)) (by simp only [hDlen]; omega)]; exact d1
  -- `u1`, `u2`.
  refine WP.seq (WP.mono (products_ok Q₅ hL (hsg.keep k₁₅.rd k₁₅.wr) ((hdg.keep k₁₅.rd k₁₅.wr).take (Nat.min_le_left D n))
      (by omega) hD₅ (by rw [q0₅]; omega) (by rw [q0₅]; exact hqo) (by rw [q0₅]; exact hqlt)
      (by rw [a8₅, a8₄, h8₃, q0₅]) w4₅ (by rw [q0₅]; exact Nat.mod_lt _ (by omega)))
    fun s₆ ⟨⟨Q₆, u1₆, u2₆, qb₆⟩, k₆⟩ => ?_)
  rw [q0₅, (sig_kept hsg hdg K₅ (by omega) (Nat.min_le_left D n)).2.2] at u1₆
  rw [q0₅, (sig_kept hsg hdg K₅ (by omega) (Nat.zero_le D)).1] at u2₆
  have k₁₆ := k₁₅.trans k₆
  have qb₁₆ : QBuf L s₁.mem s₆.mem :=
    (((qa₂.qbuf.trans qa₃.qbuf).trans qb₄).trans qa₅.qbuf).trans qb₆
  have B₁₆ := B₁₅.trans (qb₆.body hL)
  have K₆ := K₁.trans (Kept.ofBody hL B₁₆)
  obtain ⟨ep₆, -, eg₆, ey₆⟩ := key_kept hk (hkp.trans K₆) (by omega)
  -- `g^u1 y^u2 mod p`.
  refine WP.seq (WP.mono (combine_ok hL Q₆.scr Q₆.hdr Q₆.inq.h21 (hk.keep k₁₆.rd k₁₆.wr)
      ((qb₁₆.arrP hL (by decide)).trans p0₁) (by omega) hpo ((qb₁₆.arrP hL (by decide)).trans p8₁))
    fun s₇ ⟨⟨v₇, ip₇, B₇, Qk₇⟩, k₇⟩ => ?_)
  rw [u1₆, u2₆, eg₆, ey₆, hgg, hyy] at v₇
  have k₁₇ := k₁₆.trans k₇
  have q0₇ : arrQ s₇.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₇ (by decide) (by decide)]; exact qb₁₆.arr0.trans q0₁
  have K₇ := K₆.trans (Kept.ofBody hL B₇)
  -- The comparison.
  refine WP.mono (compare_ok hL (scr.congr k₁₇.wr) (hdr.kept (K₁.trans (Kept.ofBody hL (B₁₆.trans B₇))) hL)
      ip₇.h21 (hsg.keep k₁₇.rd k₁₇.wr) (by rw [q0₇]; omega)
      (((k₃.trans k₄).trans k₅ |>.trans k₆ |>.trans k₇).gpr .r26 (by decide) |>.trans m26))
    fun t ⟨⟨r3, Bt⟩, kt⟩ => ?_
  rw [q0₇, v₇, (sig_kept hsg hdg K₇ (by omega) (Nat.zero_le D)).1] at r3
  refine ⟨⟨?_, K₁.trans (Kept.ofBody hL ((B₁₆.trans B₇).trans Bt)), (kt.gpr .r21 (by decide)).trans ip₇.h21,
    scr.congr (k₁₇.trans kt).wr⟩, keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩
  rw [r3]
  refine congrArg (BitVec.ofNat 64) (ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl))
  unfold vComp
  rw [decide_eq_true_eq]
  exact and_comm

end VG.Proof.Dsa.PPC64LE
