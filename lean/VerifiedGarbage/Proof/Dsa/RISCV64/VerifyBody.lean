module

public import VerifiedGarbage.Proof.Dsa.RISCV64.CheckKey
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyQ
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyInv
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyProd
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyComb
public import VerifiedGarbage.Proof.Dsa.RISCV64.VerifyEnd
import VerifiedGarbage.Proof.Dsa.SizeBounds
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: after the check of the key

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyBody.lean`). `body_ok`:
`Verify.body` leaves in `a0` 1 exactly when r and s are in `(0, q)` and
`(g^u1 y^u2 mod p) mod q = r`, for `w = s^(q − 2) mod q`, `u1 = z w mod q`
and `u2 = r w mod q` (`vComp`), z the digest's first
`min(d, bitLength q / 8)` octets. Memory changes only in `scratch`'s
`hMask` and past its header (`BKept`).
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- The value verification compares with r. -/
def vComp (p q g y z r s : Nat) : Nat :=
  (g ^ (z * (s ^ (q - 2) % q) % q) % p * (y ^ (r * (s ^ (q - 2) % q) % q) % p) % p) % q

/-- Memory changed only in `scratch`'s word `hMask` and past its header. -/
def BKept (L : Lay) (m m' : Mem) : Prop :=
  ∀ x, ((8 ≤ ofs L.S x ∧ ofs L.S x < 256) ∨ L.Z ≤ ofs L.S x) → m' x = m x

theorem BKept.refl (L : Lay) (m : Mem) : BKept L m m := fun _ _ => rfl

theorem BKept.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : BKept L m₁ m₂) (h₂ : BKept L m₂ m₃) : BKept L m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem BKept.ofMask {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') : BKept L m m' :=
  fun x hx => h x (by have := hL.z256; simp only [hMask] at hx ⊢; omega)

theorem BKept.ofBody {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Body L m m') : BKept L m m' :=
  fun x hx => h x (by have := hL.z256; omega)

theorem BKept.out {L : Lay} {m m' : Mem} (h : BKept L m m') : Outside L.S 0 L.Z m m' :=
  fun x hx => h x (Or.inr (by omega))

/-- A word of the header from byte 8 on, kept. -/
theorem BKept.word {L : Lay} {m m' : Mem} (h : BKept L m m') {d : Nat} (hd : 8 ≤ d) (hd' : d + 8 ≤ 256) :
    word m' L.S d = word m L.S d :=
  (Mem.readW_congr fun i hi =>
    (h _ (by rw [ofs_off L.S (by omega)]; omega)).symm).symm

/-- Memory that changed only at offsets below `qOff` of `scratch` keeps the Q space. -/
theorem keepQ_of {L : Lay} (hL : L.Ok) {m m' : Mem} (h : ∀ x, L.qOff ≤ ofs L.S x → m' x = m x) :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' := by
  intro x hx
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  have hlt := (x - L.S).isLt
  have hlt' := (x - L.Q).isLt
  refine h x ?_
  simp only [ofs, Lay.Q, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.S (by omega_arith)] at hx
  by_cases hd : L.qOff ≤ (x - L.S).toNat
  · exact hd
  · rw [Nat.mod_eq_of_lt (by omega_arith)] at hx; omega_arith

/-- The store of the mask keeps the Q space. -/
theorem mask_keepQ {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') :
    Outside L.Q 1600 (2 ^ 64 - 1600) m m' :=
  keepQ_of hL fun x hx => h x (Or.inr (by simp only [hMask, Lay.qOff, Lay.slot_eq] at hx ⊢; omega_arith))

theorem keepQ_arr0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.Q 1600 (2 ^ 64 - 1600) m m') :
    arrQ m' L 0 = arrQ m L 0 :=
  h.wordsVal (Or.inl (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega)

/-- The store of the mask keeps the P space's arrays. -/
theorem mask_arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : Outside L.S hMask 8 m m') (j : Nat) (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have h28 : slot L.wp j + 8 * L.wp ≤ L.Z := by
    have := slot_lt (w := L.wp) hj; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at this; omega
  have hn := hL.nowrap
  exact h.wordsVal (Or.inr (by have := Lay.slot_eq L.wp j; simp only [hMask]; omega)) (by omega)

/-- A change in the Q space's arrays or the buffer keeps the P space. -/
theorem QBuf.keepP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    Outside L.S (L.qOff + slot L.wq 1) (1600 + 2 * L.pl - slot L.wq 1) m m' := by
  have hq : L.qOff ≤ 11456 := by rw [hL.qOff_eq]; rcases hL.pl with e | e | e <;> omega
  have hs := hL.qslot
  have e1 := Lay.slot_eq L.wq 1; have e28 := Lay.slot_eq L.wq 28
  exact outside_shift (B := L.S) (a := L.qOff) h (by have := hL.pl; omega_arith) (by omega_arith)

theorem QBuf.arrP {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') (j : Nat) (hj : j < 28) :
    arrP m' L j = arrP m L j := by
  have h28 : slot L.wp j + 8 * L.wp ≤ L.Z := by
    have := slot_lt (w := L.wp) hj; have := hL.buf_end; simp only [Lay.bOff, Lay.qOff] at this; omega
  have hj' : slot L.wp j + 8 * L.wp ≤ L.qOff := by have := slot_lt (w := L.wp) hj; simp only [Lay.qOff]; omega
  have hn := hL.nowrap
  exact (h.keepP hL).wordsVal (Or.inl (by omega)) (by omega)

/-- A buffer's first `min n k` octets. -/
theorem bytesAt_take (m : Mem) (D : Addr) (n k : Nat) :
    (Spec.Rsa.bytesAt m D n).take k = Spec.Rsa.bytesAt m D (min n k) := by
  simp only [Spec.Rsa.bytesAt, ← List.map_take, List.take_range, Nat.min_comm]

/-- The signature's and the digest's values, kept. -/
theorem sig_kept {s : State} {L : Lay} {sig dig : Addr} {D : Nat} (hsg : Src s L sig (2 * L.ql))
    (hdg : Src s L dig D) {m m' : Mem} (h : Outside L.S 0 L.Z m m') {k : Nat} (hk : k ≤ D) :
    rOf m' L sig = rOf m L sig ∧ sOf m' L sig = sOf m L sig ∧
      Spec.Rsa.bytesAt m' dig k = Spec.Rsa.bytesAt m dig k := by
  refine ⟨?_, ?_, (hdg.take hk).bytes h (by omega)⟩
  · simp only [rOf]; rw [(hsg.take (k := L.ql) (by omega)).bytes h (by omega)]
  · simp only [sOf]; rw [(hsg.sub (o := L.ql) (k := L.ql) (by omega)).bytes h (by omega)]

/-- `Regs` through a change that keeps the header's lengths. -/
theorem Regs.keepHdr {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : Regs s L key sig)
    (k : Keep rs s t) (hw : word t.mem L.S hLens = word s.mem L.S hLens)
    (hr : ∀ r ∈ regsRegs, r ∉ rs := by decide) : Regs t L key sig :=
  ⟨(k.gpr (hr _ (by decide))).trans h.s6, (k.gpr (hr _ (by decide))).trans h.s11,
    (k.gpr (hr _ (by decide))).trans h.ra, by rw [hw]; exact h.pl, by rw [hw]; exact h.ql⟩

/-- `keepMask`: the mask in `a4` to the header's word `hMask`. -/
theorem keepMask_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) :
    WP isa (.block keepMask) s fun t =>
      (QS t L key sig ∧ word t.mem L.S hMask = s.gpr .a4 ∧ Outside L.S hMask 8 s.mem t.mem) ∧
        Keep [] s t := by
  obtain ⟨hin, hal⟩ := ScrL.hdr h.scr hL (d := 0) (by decide) (by decide)
  have hst : InRegions s.wr (off L.S 0) 8 := h.scr.st (by have := hL.z256; omega)
  refine WP.mono (WP.keep [] (Q := fun u => u.mem = s.mem.writeW (off L.S 0) (s.gpr .a4)) (by
      unfold keepMask; brun [hMask, h.regs.s6, hst, hal]) (by decide) (by rfl)) fun t ⟨mt, kt⟩ => ?_
  have wo : Outside L.S hMask 8 s.mem t.mem := by
    rw [mt]; exact writeW_outside s.mem L.S _ (by simp only [hMask]; omega_arith)
  refine ⟨⟨⟨h.inq.keep kt (by decide), h.scr.congr kt.2.2, h.regs.keepHdr kt
    (wo.word (Or.inr (by decide)) (by have := hL.nowrap; have := hL.z256; simp only [hLens]; omega)) (by decide)⟩,
    by rw [mt]; exact word_writeW_self _ _ _ _, wo⟩, kt⟩

theorem q_bits {q ql : Nat} (hq : 1 ≤ q) (hlt : q < 2 ^ (8 * ql)) : Spec.Dsa.bitLength q / 8 ≤ ql := by
  have hq0 : q ≠ 0 := by omega
  have hlog : q.log2 < 8 * ql := (Nat.log2_lt hq0).mpr hlt
  have : Spec.Dsa.bitLength q = q.log2 + 1 := by simp [Spec.Dsa.bitLength, hq0]
  omega

/-- The registers of the Q space's part of `Verify.body`. -/
def bodyQRegs : List Reg := rangesRegs ++ [] ++ rrQRegs ++ qm2Regs ++ invRegs ++ prodRegs

/-- The Q space's part of `Verify.body`: the mask of r's and s's ranges to
`hMask`, then `u1` and `u2` to the buffer. -/
theorem bodyQ_ok {s : State} {L : Lay} {key sig dig : Addr} {q qb d : Nat} {Q : State → Prop} {rest : Prog isa}
    (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hq0 : arrQ s.mem L 0 = q) (hq2 : 2 ≤ q) (hqo : q % 2 = 1)
    (hql : q < 2 ^ (8 * L.ql)) (hsg : Src s L sig (2 * L.ql)) (hdg8 : word s.mem L.S hDigest = dig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb))
    (hrest : ∀ t, (QS t L key sig ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * (sOf s.mem L sig ^ (q - 2) % q) % q ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off L.Buf 32) L.ql) =
          rOf s.mem L sig * (sOf s.mem L sig ^ (q - 2) % q) % q ∧
        word t.mem L.S hMask = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) ∧
        BKept L s.mem t.mem ∧ (∀ j < 28, arrP t.mem L j = arrP s.mem L j) ∧ arrQ t.mem L 0 = q) →
        Keep bodyQRegs s t → WP isa rest t Q) :
    WP isa (.seq ranges (.seq (.block keepMask) (.seq rrQ (.seq qMinus2 (.seq inverse (.seq products rest))))))
      s Q := by
  have hZ := hL.z256
  refine WP.seq (WP.mono (ranges_ok hL hs hr hsg) fun s₁ ⟨⟨Q₁, _, m₁, qa₁⟩, k₁⟩ => ?_)
  rw [hq0] at m₁
  have q0₁ : arrQ s₁.mem L 0 = q := (qa₁.arr0 hL).trans hq0
  have B₁ : Body L s.mem s₁.mem := qa₁.body hL
  refine WP.seq (WP.mono (keepMask_ok hL Q₁) fun s₂ ⟨⟨Q₂, w₂, o₂⟩, k₂⟩ => ?_)
  rw [m₁] at w₂
  have K₂ : BKept L s.mem s₂.mem := (BKept.ofBody hL B₁).trans (BKept.ofMask hL o₂)
  have q0₂ : arrQ s₂.mem L 0 = q := (keepQ_arr0 hL (mask_keepQ hL o₂)).trans q0₁
  have pw₂ : ∀ j < 28, arrP s₂.mem L j = arrP s.mem L j := fun j hj =>
    (mask_arrP hL o₂ j hj).trans ((qa₁.qbuf hL).arrP hL j hj)
  -- `R² mod q`.
  refine WP.seq (WP.mono (rrQ_ok hL Q₂ (by rw [q0₂]; exact hq2) (by rw [q0₂]; exact hqo))
    fun s₃ ⟨⟨Q₃, I₃, _, h24₃, qa₃⟩, k₃⟩ => ?_)
  rw [q0₂] at h24₃
  have q0₃ : arrQ s₃.mem L 0 = q := (qa₃.arr0 hL).trans q0₂
  -- `q − 2`.
  refine WP.seq (WP.mono (qMinus2_ok hL Q₃ (by rw [q0₃]; exact hq2) (by rw [q0₃]; exact hql))
    fun s₄ ⟨⟨Q₄, bq₄, kj₄, w0₄, qb₄⟩, k₄⟩ => ?_)
  rw [q0₃] at bq₄
  have q0₄ : arrQ s₄.mem L 0 = q := (kj₄ 0 (by decide) (by decide)).trans q0₃
  have I₄ : QInv s₄ L := by
    show ((word s₄.mem L.Q (slot L.wq 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [w0₄, k₄.gpr (by decide)]; exact I₃
  have K₄ : BKept L s.mem s₄.mem := K₂.trans (BKept.ofBody hL ((qa₃.body hL).trans (qb₄.body hL)))
  -- `w = s^(q − 2) mod q`.
  have k₁₄ := ((k₁.trans k₂).trans k₃).trans k₄
  refine WP.seq (WP.mono (inverse_ok hL Q₄ I₄ (hsg.keep k₁₄.2.1 k₁₄.2.2) (by rw [q0₄]; exact hq2)
      (by rw [q0₄]; exact hqo) (by rw [q0₄, kj₄ 24 (by decide) (by decide)]; exact h24₃))
    fun s₅ ⟨⟨Q₅, I₅, w4₅, k24₅, qa₅⟩, k₅⟩ => ?_)
  rw [q0₄, bq₄, (sig_kept hsg hdg K₄.out (Nat.le_refl _)).2.1] at w4₅
  have q0₅ : arrQ s₅.mem L 0 = q := (qa₅.arr0 hL).trans q0₄
  have k₁₅ := k₁₄.trans k₅
  have K₅ : BKept L s.mem s₅.mem := K₄.trans (BKept.ofBody hL (qa₅.body hL))
  -- `u1`, `u2`.
  refine WP.seq (WP.mono (products_ok hL Q₅ I₅ (hsg.keep k₁₅.2.1 k₁₅.2.2)
      (by rw [K₅.word (by decide) (by decide)]; exact hdg8)
      (by rw [K₅.word (by decide) (by decide)]; exact hlen) hqb hd (hdg.keep k₁₅.2.1 k₁₅.2.2)
      (by rw [q0₅]; exact hq2) (by rw [q0₅]; exact hqo) (by rw [q0₅]; exact hql)
      (by rw [q0₅, k24₅ 24 (by decide) (by decide), kj₄ 24 (by decide) (by decide)]; exact h24₃) w4₅
      (by rw [q0₅]; exact Nat.mod_lt _ (by omega)))
    fun t ⟨⟨Qt, u1, u2, qbt⟩, kt⟩ => ?_)
  have sk := sig_kept hsg hdg K₅.out (Nat.le_refl _)
  rw [q0₅, sk.2.2] at u1
  rw [q0₅, sk.1] at u2
  have B₂t : Body L s₂.mem t.mem := ((qa₃.body hL).trans (qb₄.body hL)).trans ((qa₅.body hL).trans (qbt.body hL))
  have qb₂t : QBuf L s₂.mem t.mem := (((qa₃.qbuf hL).trans qb₄).trans (qa₅.qbuf hL)).trans qbt
  refine hrest t ⟨Qt, u1, u2, ?_, K₂.trans (BKept.ofBody hL B₂t), fun j hj => (qb₂t.arrP hL j hj).trans (pw₂ j hj),
    (qbt.arr0 hL).trans q0₅⟩ (k₁₅.trans kt)
  rw [B₂t.word (by decide)]; exact w₂

/-- The registers `Verify.body` writes. -/
def bodyRegs : List Reg := bodyQRegs ++ combRegs ++ cmpRegs

theorem body_ok {s₀ s : State} {L : Lay} {key sig dig : Addr} {d : Nat}
    (hL : L.Ok) (hK : KeyOk s₀.mem L key) (hc : Checked s₀ s L key sig d)
    (hkp : Kept L s₀.mem s.mem) (hk : Src s L key (3 * L.pl + L.ql)) (hsg : Src s L sig (2 * L.ql))
    (hd : d < 2 ^ 16) (hdg : Src s L dig d) (hdg8 : word s.mem L.S hDigest = dig) :
    WP isa Verify.body s fun t =>
      (t.gpr .a0 = BitVec.ofNat 64 (if ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < qOf s₀.mem L key) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < qOf s₀.mem L key)) ∧
          vComp (pOf s₀.mem L key) (qOf s₀.mem L key) (gOf s₀.mem L key) (yOf s₀.mem L key)
            (Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig
              (min d (Spec.Dsa.bitLength (qOf s₀.mem L key) / 8))))
            (rOf s.mem L sig) (sOf s.mem L sig) = rOf s.mem L sig then 1 else 0) ∧
        BKept L s.mem t.mem ∧ t.gpr .s6 = L.S ∧ ScrL t L) ∧ Keep bodyRegs s t := by
  have hZ := hL.z256
  have hpl := hL.pl
  have hql := hL.ql
  obtain ⟨ip, scr, regs, p0, ptop, inv, p24, q0, qtop, lens⟩ := hc
  have hk' := hk.take (k := 2 * L.pl + L.ql) (by omega)
  obtain ⟨ep, eq, eg⟩ := params_kept hk' hkp
  have ey := y_kept hk hkp
  unfold KeyOk at hK
  have hqlt : qOf s₀.mem L key < 2 ^ (8 * L.ql) := by
    rw [← eq, qOf, ← VG.Proof.Bignum.pow256_eq]
    have := VG.Proof.Bignum.os2ip_lt (Spec.Rsa.bytesAt s.mem (off key L.pl) L.ql)
    rwa [VG.Proof.Bignum.bytesAt_length] at this
  generalize pOf s₀.mem L key = p at hK p0 p24 ⊢
  generalize hq : qOf s₀.mem L key = q at hK q0 lens hqlt ⊢
  generalize hgg : gOf s₀.mem L key = g at hK ⊢
  generalize hyy : yOf s₀.mem L key = y at hK ⊢
  have B := VG.Proof.Dsa.supported_bounds hK.1.1
  have hqo : q % 2 = 1 := hK.1.2.1
  have hpo : p % 2 = 1 := hK.1.2.2
  have hnq : Spec.Dsa.bitLength q / 8 ≤ L.ql := q_bits (by omega) hqlt
  generalize hn : Spec.Dsa.bitLength q / 8 = n at lens hnq ⊢
  unfold Verify.body
  refine bodyQ_ok (q := q) (qb := n) hL scr regs q0 (by omega) hqo hqlt hsg hdg8 lens hnq hd
    (hdg.take (Nat.min_le_left d n)) fun t₁ ⟨Q₁, u1, u2, m₁, K₁, pw₁, q0₁⟩ k₁ => ?_
  have sk := sig_kept hsg hdg K₁.out (Nat.le_refl d)
  -- `g^u1 y^u2 mod p`.
  refine WP.seq (WP.mono (combine_ok hL Q₁.scr Q₁.regs (hk.keep k₁.2.1 k₁.2.2) ((pw₁ 0 (by decide)).trans p0)
      (by omega) hpo ((pw₁ 24 (by decide)).trans p24)) fun t₂ ⟨⟨v₂, ip₂, B₂, Qk₂⟩, k₂⟩ => ?_)
  rw [u1, u2] at v₂
  have hk₁ := hk.take (k := 2 * L.pl + L.ql) (by omega)
  have eg₁ : gOf t₁.mem L key = g := by
    simp only [gOf]
    rw [(hk.sub (o := L.pl + L.ql) (k := L.pl) (by omega)).bytes K₁.out (by omega)]
    exact eg.trans hgg
  have ey₁ : yOf t₁.mem L key = y := by
    simp only [yOf]
    rw [(hk.sub (o := 2 * L.pl + L.ql) (k := L.pl) (by omega)).bytes K₁.out (by omega)]
    exact ey.trans hyy
  rw [eg₁, ey₁] at v₂
  have k₁₂ := k₁.trans k₂
  have q0₂ : arrQ t₂.mem L 0 = q := (keepQ_arr0 hL Qk₂).trans q0₁
  have K₂ : BKept L s.mem t₂.mem := K₁.trans (BKept.ofBody hL B₂)
  -- The comparison.
  have hm₂ : word t₂.mem L.S hMask = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < q) ∧
      (0 < sOf s.mem L sig ∧ sOf s.mem L sig < q))) := by rw [B₂.word (by decide)]; exact m₁
  refine WP.mono (compare_ok hL (scr.congr k₁₂.2.2) (Q₁.regs.keep k₂ B₂) (hsg.keep k₁₂.2.1 k₁₂.2.2)
      (by rw [q0₂]; omega) hm₂) fun t ⟨⟨a0, Bt⟩, kt⟩ => ?_
  rw [q0₂, v₂, (sig_kept hsg hdg K₂.out (Nat.le_refl d)).1] at a0
  refine ⟨⟨?_, K₂.trans (BKept.ofBody hL Bt), ((k₂.trans kt).gpr (by decide)).trans Q₁.regs.s6,
    scr.congr (k₁₂.trans kt).2.2⟩, k₁₂.trans kt⟩
  rw [a0]
  refine congrArg (BitVec.ofNat 64) (ite_congr (propext ?_) (fun _ => rfl) (fun _ => rfl))
  unfold vComp
  rw [decide_eq_true_eq]
  exact and_comm

end VG.Proof.Dsa.RISCV64
