module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.CheckKey
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyProd
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyComb
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyEnd
import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyInv
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.PPC64LE.RegUpd
public import VerifiedGarbage.Impl.Dsa.PPC64LE.Verify
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ctx
public import VerifiedGarbage.Proof.Dsa.PPC64LE.VerifyQ

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

/-- The store of the mask in the header. -/
theorem Kept.ofMask {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') : Kept L m m' :=
  ⟨h.mono (Nat.zero_le _) (by have := hL.z256; simp only [hMask]; omega), fun i hi =>
    Outside.word h (Or.inr (by simp only [saveOff, hMask]; omega))
      (by have := hL.nowrap; have := hL.z256; simp only [saveOff]; omega)⟩

/-- The signature's and the digest's values, kept. -/
theorem sig_kept {s : State} {L : Lay} {sig dig : Addr} {D : Nat} (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) {m m' : Mem} (h : Outside L.S 0 L.Z m m') {k : Nat} (hk : k ≤ D) :
    rOf m' L sig = rOf m L sig ∧ sOf m' L sig = sOf m L sig ∧
      Spec.Rsa.bytesAt m' dig k = Spec.Rsa.bytesAt m dig k := by
  refine ⟨?_, ?_, (hdg.take hk).kept h⟩
  · have e := (hsg.sub (o := 0) (k := L.ql) (by omega)).kept h
    simp only [off, BitVec.add_zero] at e
    simp only [rOf]; rw [e]
  · simp only [sOf]; rw [(hsg.sub (o := L.ql) (k := L.ql) (by omega)).kept h]

/-- Every register but `r2` (the lengths) and `r21` (which keeps `S`). -/
def notR21 : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .r14, .r15, .r16, .r17, .r18, .r19, .r20,
    .r22, .r23, .r24, .r25, .r26, .r27, .r28, .r29, .r30, .r31]

theorem keep_but21 {rs : List Reg} {s t : State} (h : Keep rs s t) (hr : Reg.r21 ∉ rs) (hr2 : Reg.r2 ∉ rs) :
    Keep notR21 s t :=
  h.mono fun r hm => by
    have : r ≠ .r21 := fun e => hr (e ▸ hm)
    have : r ≠ .r2 := fun e => hr2 (e ▸ hm)
    cases r <;> simp_all [notR21]

/-- The registers `Verify.body` writes: all but `r2` and `r21`. -/
abbrev bodyRegs : List Reg := notR21

/-- The store of the mask keeps the P space's arrays. -/
theorem mask_arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') {j : Nat} (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have := slot_lt (w := L.wp) hj
  have := hL.wp_ge
  have := hL.nowrap
  have := hL.buf_end
  simp only [Lay.bOff, Lay.qOff] at *
  exact Outside.val32 h (Or.inr (by simp only [hMask, Lay.slot_eq] at *; omega)) (by omega)

/-- The store of the mask keeps the Q space. -/
theorem mask_keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' :=
  keepQ_of hL fun x hx => h x (Or.inr (by simp only [hMask, Lay.qOff, Lay.slot_eq] at hx ⊢; omega))

theorem body_ok {s₀ s : State} {L : Lay} {key sig dig : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key sig dig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + L.ql)) (hsg : Src s L sig (2 * L.ql))
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) :
    WP isa Verify.body s fun t =>
      (t.gpr .r3 = BitVec.ofNat 64 (if ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < qOf s₀.mem L key) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < qOf s₀.mem L key)) ∧
          vComp (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig
              (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            (rOf s.mem L sig) (sOf s.mem L sig) = rOf s.mem L sig then 1 else 0) ∧
        Kept L s.mem t.mem ∧ t.gpr .r21 = L.S ∧ ScrL t L) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  have hnw := hL.nowrap
  obtain ⟨ip, scr, regs, p0, ptop, p8, q0, qtop, r2⟩ := hc
  obtain ⟨ep, eq, eg, ey⟩ := key_kept hk hkp.out
  unfold KeyOk at hK
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p8 ⊢
  generalize hq : qOf s₀.mem L key = q at hK q0 r2 hqlt ⊢
  generalize hgg : gOf s₀.mem L key = g at hK ⊢
  generalize hyy : yOf s₀.mem L key = y at hK ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hqb : Spec.Dsa.bitLength q ≤ 256 := by have := hK.1.1; unfold Spec.Dsa.supportedSizes at this; omega
  generalize hn : Spec.Dsa.bitLength q / 8 = n at r2 ⊢
  have hnq : n ≤ L.ql := by
    have hq0 : q ≠ 0 := by omega
    have hlog : q.log2 < 8 * L.ql := (Nat.log2_lt hq0).mpr hqlt
    have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
    omega
  unfold Verify.body
  -- r and s in range.
  refine WP.seq (WP.mono (ranges_ok hL scr regs hsg) fun s₁ ⟨⟨Q₁, r5₁, m22, qa₁⟩, k₁⟩ => ?_)
  rw [q0] at m22
  have q0₁ : arrQ s₁.mem L 0 = q := qa₁.arr0.trans q0
  -- The mask to the header.
  have hst : InRegions s₁.wr (L.S + BitVec.ofNat 64 hMask) 8 := (scr.congr k₁.wr).st (by simp only [hMask]; omega)
  have he : exec (.store .d .r22 .r21 hMask) s₁ =
      some { s₁ with mem := s₁.mem.writeW (L.S + BitVec.ofNat 64 hMask) (s₁.gpr .r22) } := by
    rw [exec_std (by decide) (by rw [Q₁.inq.h21]; exact hst), Q₁.inq.h21]
  refine WP.seq (WP.mono (WP.keep [] (Q := fun u => u.mem = s₁.mem.writeW (L.S + BitVec.ofNat 64 hMask)
      (s₁.gpr .r22)) (by unfold keepMask; prun [he]) (by decide)) fun s₂ ⟨m₂, k₂⟩ => ?_)
  rw [m22] at m₂
  have wo : Outside L.S hMask 8 s₁.mem s₂.mem := by
    rw [m₂]; exact writeW_outside s₁.mem L.S _ (by simp only [hMask]; omega)
  have hm₂ : word s₂.mem L.S hMask =
      mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧ (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) := by
    rw [m₂]; exact word_writeW_self s₁.mem L.S hMask _
  have Km : Kept L s₁.mem s₂.mem := Kept.ofMask hL wo
  have Kr : Kept L s.mem s₁.mem := Kept.ofBody hL (qa₁.qbody.body hL)
  have K₂ := Kr.trans Km
  have Q₂ : QS s₂ L key sig dig := Q₁.step k₂ (by decide)
  have q0₂ : arrQ s₂.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 (mask_keepQ hL wo) (by decide) (by decide)]; exact q0₁
  have pw : ∀ j < 28, arrP s₂.mem L j = arrP s.mem L j := fun j hj =>
    (mask_arrP hL wo hj).trans (qa₁.qbuf.arrP hL hj)
  have k₁₂ := k₁.trans k₂
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ_ok Q₂ (by rw [q0₂]; omega)) fun s₃ ⟨⟨Q₃, h8₃, qa₃, _⟩, k₃⟩ => ?_)
  rw [q0₂] at h8₃
  have q0₃ : arrQ s₃.mem L 0 = q := qa₃.arr0.trans q0₂
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok Q₃ hL (by rw [q0₃]; omega) (by rw [q0₃]; exact hqlt))
    fun s₄ ⟨⟨Q₄, bq₄, a8₄, qb₄, _⟩, k₄⟩ => ?_)
  rw [q0₃] at bq₄
  have q0₄ : arrQ s₄.mem L 0 = q := qb₄.arr0.trans q0₃
  have k₁₄ := (k₁₂.trans k₃).trans k₄
  have B₂₄ : Body L s₂.mem s₄.mem := (qa₃.qbody.body hL).trans (qb₄.body hL)
  have K₄ := K₂.trans (Kept.ofBody hL B₂₄)
  -- `w = s^(q − 2) mod q`.
  refine WP.seq (WP.mono (inverse_ok Q₄ hL (hsg.keep k₁₄.rd k₁₄.wr) (by rw [q0₄]; omega) (by rw [q0₄]; exact hqo)
      (by rw [a8₄, h8₃, q0₄])) fun s₅ ⟨⟨Q₅, w4₅, a8₅, qa₅⟩, k₅⟩ => ?_)
  rw [q0₄, bq₄, (sig_kept hsg hdg K₄.out (Nat.zero_le d)).2.1] at w4₅
  have q0₅ : arrQ s₅.mem L 0 = q := qa₅.arr0.trans q0₄
  have k₁₅ := k₁₄.trans k₅
  have B₂₅ := B₂₄.trans (qa₅.qbody.body hL)
  have K₅ := K₂.trans (Kept.ofBody hL B₂₅)
  -- `u1`, `u2`.
  refine WP.seq (WP.mono (products_ok Q₅ hL (hsg.keep k₁₅.rd k₁₅.wr) ((k₁₅.gpr .r2 (by decide)).trans r2)
      hnq hd ((hdg.keep k₁₅.rd k₁₅.wr).take (Nat.min_le_left d n))
      (by rw [q0₅]; omega) (by rw [q0₅]; exact hqo) (by rw [q0₅]; exact hqlt)
      (by rw [a8₅, a8₄, h8₃, q0₅]) w4₅ (by rw [q0₅]; exact Nat.mod_lt _ (by omega)))
    fun s₆ ⟨⟨Q₆, u1₆, u2₆, qb₆⟩, k₆⟩ => ?_)
  rw [q0₅, (sig_kept hsg hdg K₅.out (Nat.min_le_left d n)).2.2] at u1₆
  rw [q0₅, (sig_kept hsg hdg K₅.out (Nat.zero_le d)).1] at u2₆
  have k₁₆ := k₁₅.trans k₆
  have qb₂₆ : QBuf L s₂.mem s₆.mem := ((qa₃.qbuf.trans qb₄).trans qa₅.qbuf).trans qb₆
  have B₂₆ := B₂₅.trans (qb₆.body hL)
  have K₆ := K₂.trans (Kept.ofBody hL B₂₆)
  obtain ⟨ep₆, -, eg₆, ey₆⟩ := key_kept hk (hkp.trans K₆).out
  -- `g^u1 y^u2 mod p`.
  refine WP.seq (WP.mono (combine_ok hL Q₆.scr Q₆.regs (hk.keep k₁₆.rd k₁₆.wr)
      ((qb₂₆.arrP hL (by decide)).trans ((pw 0 (by decide)).trans p0)) (by omega) hpo
      ((qb₂₆.arrP hL (by decide)).trans ((pw 8 (by decide)).trans p8)))
    fun s₇ ⟨⟨v₇, ip₇, B₇, Qk₇⟩, k₇⟩ => ?_)
  rw [u1₆, u2₆, eg₆, ey₆, hgg, hyy] at v₇
  have k₁₇ := k₁₆.trans k₇
  have q0₇ : arrQ s₇.mem L 0 = q := by
    rw [arrQ, arr, Outside.val32 Qk₇ (by decide) (by decide)]; exact qb₂₆.arr0.trans q0₂
  have K₇ := K₆.trans (Kept.ofBody hL B₇)
  have hm₇ : word s₇.mem L.S hMask = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧
      (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) := by
    rw [Outside.word (B₂₆.trans B₇) (Or.inl (by decide)) (by simp only [hMask]; omega)]; exact hm₂
  -- The comparison.
  refine WP.mono (compare_ok hL (scr.congr k₁₇.wr) (regs.keep k₁₇) (hsg.keep k₁₇.rd k₁₇.wr) (by rw [q0₇]; omega)
      hm₇) fun t ⟨⟨r3, Bt⟩, kt⟩ => ?_
  rw [q0₇, v₇, (sig_kept hsg hdg K₇.out (Nat.zero_le d)).1] at r3
  refine ⟨⟨?_, K₂.trans (Kept.ofBody hL ((B₂₆.trans B₇).trans Bt)), (kt.gpr .r21 (by decide)).trans ip₇.h21,
    scr.congr (k₁₇.trans kt).wr⟩, keep_but21 (k₁₇.trans kt) (by decide) (by decide)⟩
  rw [r3]
  refine congrArg (BitVec.ofNat 64) (ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl))
  unfold vComp
  rw [decide_eq_true_eq]
  exact and_comm

end VG.Proof.Dsa.PPC64LE
