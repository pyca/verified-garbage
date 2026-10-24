module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Ptr
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Load
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Range
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreLoad
import VerifiedGarbage.Proof.Bignum.PPC64LE.PreCore
import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Offset

/-!
# DSA verification on PPC64LE: the ranges of r and s

`ranges_ok`: into the Q space (q in array 0), r into array 5 and s into
array 6, and `r26 :=` the mask of `0 < r < q` and `0 < s < q`.
-/

@[expose] public section

namespace VG.Proof.Dsa.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE VG.Proof.MillerRabin.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Dsa.PPC64LE VG.Impl.Dsa.PPC64LE.Verify
open VG.Proof.Bignum (slot slot_sep)

/-- r and s, from the signature at `sig`. -/
def rOf (m : Mem) (L : Lay) (sig : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m sig L.ql)
def sOf (m : Mem) (L : Lay) (sig : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off sig L.ql) L.ql)

/-- `zeroArr j`: 0 into array `j`. -/
theorem zeroArr_ok {s : State} {B : Addr} {Z w j : Nat} (h : Env s B Z w) (hj : j < 28) :
    WP isa (zeroArr j) s fun t =>
      (arr t.mem B w j = 0 ∧ Outside B (slot w j) (8 * w) s.mem t.mem) ∧ Keep [.r0, .r14, .r17] s t := by
  have hA := h.arr hj
  unfold zeroArr
  refine WP.seq (WP.mono (h.base (rd := .r14) (by decide) (by decide) j) fun s₁ ⟨⟨a14, m1⟩, k1⟩ => ?_)
  refine WP.mono (zeroWords_ok (h.hs.congr k1.wr) a14 ((k1.gpr .r11 (by decide)).trans h.h11)
    (by have := h.hw; omega) (by have := h.hw'; omega) (by omega)) fun t ⟨⟨_, hz, ot⟩, kt⟩ =>
    ⟨⟨?_, by rw [← m1]; exact ot⟩, (k1.trans kt).mono (by decide)⟩
  rw [arr, VG.Proof.Bignum.PPC64LE.Pre.val32_eq_wv]
  exact (VG.Proof.Bignum.wv_eq_zero_iff _ _ _ _).mpr hz

/-- A Q space state, with the header and `scratch`. -/
structure QS (s : State) (L : Lay) (key sig dig : Addr) : Prop where
  inq : InQ s L
  scr : ScrL s L
  hdr : Hdr s.mem L key sig dig

/-- `QS` after a change in the Q space's arrays. -/
theorem QS.step {s t : State} {L : Lay} {key sig dig : Addr} {rs : List Reg} (h : QS s L key sig dig)
    (hL : L.Ok) (k : Keep rs s t) (hr : ∀ r ∈ inRegs, r ∉ rs) (hm : QArr L s.mem t.mem) : QS t L key sig dig :=
  ⟨h.inq.keep k hr, h.scr.congr k.wr, h.hdr.body (hm.qbody.body hL) hL⟩

/-- A buffer apart from `scratch` is apart from the Q space. -/
theorem Src.sepQ {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) (hL : L.Ok) :
    ∀ i < n, ∀ x, ofs L.Q x < 1600 → off D i ≠ x :=
  h.sepIn (by have := hL.buf_end; simp only [Lay.bOff] at this; omega) hL.nowrap

/-- `loadArr j` in the Q space, from a buffer apart from `scratch`. -/
theorem loadQ_ok {s : State} {L : Lay} {key sig dig N : Addr} {k j : Nat} (h : QS s L key sig dig) (hL : L.Ok)
    (hj : j < 28) (hj0 : j ≠ 0) (hsrc : Src s L N k) (h12 : s.gpr .r12 = N) (h6 : s.gpr .r6 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 32) :
    WP isa (loadArr j) s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L j = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) ∧
        word t.mem L.Q (slot 4 j + 32) = 0 ∧ Outside L.Q (slot 4 j) (8 * (4 + 1)) s.mem t.mem ∧
        QArr L s.mem t.mem) ∧ Keep loadRegs s t := by
  have hA := h.inq.env.arr hj
  refine WP.mono (loadArr_ok h.inq.env hj h12 h6 hk (by omega) hsrc.rd (hsrc.sepQ hL))
    fun t ⟨⟨v, top, o, a10⟩, kt⟩ => ?_
  have qa : QArr L s.mem t.mem := QArr.of o (by simp only [slot_eq]; omega) (by simp only [slot_eq] at hA ⊢; omega)
  exact ⟨⟨⟨⟨env_keep10 h.inq.env kt (by decide) a10, (kt.gpr .r21 (by decide)).trans h.inq.h21,
      (kt.gpr .r23 (by decide)).trans h.inq.h23⟩, h.scr.congr kt.wr, h.hdr.body (qa.qbody.body hL) hL⟩,
    v, top, o, qa⟩, kt⟩

/-- Array 0 and its word 4, kept by a change from array 1 on. -/
theorem QArr.arr0 {L : Lay} {m m' : Mem} (h : QArr L m m') : arrQ m' L 0 = arrQ m L 0 :=
  Outside.val32 h (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)

theorem QArr.top0 {L : Lay} {m m' : Mem} (h : QArr L m m') :
    word m' L.Q (slot 4 0 + 32) = word m L.Q (slot 4 0 + 32) :=
  Outside.word h (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)

/-- The registers `ranges` writes. -/
def rangesRegs : List Reg := enterRegs ++ [.r6, .r12] ++ loadRegs ++ inRangeRegs

/-- `ranges`: into the Q space, r into array 5 and s into array 6, and `r26`
the mask of both in `(0, q)`, q in array 0. -/
theorem ranges_ok {s : State} {L : Lay} {key sig dig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hh : Hdr s.mem L key sig dig) (h21 : s.gpr .r21 = L.S) (hsg : Src s L sig (2 * L.ql)) :
    WP isa ranges s fun t =>
      (QS t L key sig dig ∧ arrQ t.mem L 5 = rOf s.mem L sig ∧
        t.gpr .r26 = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < arrQ s.mem L 0) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < arrQ s.mem L 0))) ∧
        QArr L s.mem t.mem) ∧ Keep rangesRegs s t := by
  have hql := hL.ql
  have hn : slot 4 28 ≤ 2 ^ 64 := by decide
  unfold ranges
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hh h21) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have Q1 : QS s₁ L key sig dig := ⟨q1, hs.congr k1.wr, m1 ▸ hh⟩
  refine WP.mono (ptrR_ok hL Q1.scr Q1.hdr q1.h21) fun s₂ ⟨⟨a12, a6, m2⟩, k2⟩ => ?_
  have Q2 := Q1.step hL k2 (by decide) (by rw [m2]; exact QArr.refl _ _)
  have k12 := k1.trans k2
  have src2 := hsg.keep k12.rd k12.wr
  have m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide) (by decide) (src2.sub (o := 0) (k := L.ql)
      (by omega)) (by rw [a12, off, BitVec.add_zero]) a6 (by omega) (by omega))
    fun s₃ ⟨⟨Q3, v5, top5, o3, qa3⟩, k3⟩ => ?_)
  have k13 := k12.trans k3
  refine WP.seq (WP.mono (ptrS_ok hL Q3.scr Q3.hdr Q3.inq.h21) fun s₄ ⟨⟨b12, b6, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.step hL k4 (by decide) (by rw [m4]; exact QArr.refl _ _)
  have src4 := hsg.keep (k13.trans k4).rd (k13.trans k4).wr
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q4 hL (by decide) (by decide) (src4.sub (o := L.ql) (k := L.ql)
      (by omega)) b12 b6 (by omega) (by omega))
    fun s₅ ⟨⟨Q5, v6, top6, o5, qa5⟩, k5⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q5.inq.env (j := 7) (by decide)) fun s₆ ⟨⟨z7, o6⟩, k6⟩ => ?_)
  have qa6 : QArr L s₅.mem s₆.mem := QArr.of o6 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have Q6 := Q5.step hL k6 (by decide) qa6
  have h26 : WP isa (.block [.li .r26 0, .subi .r26 .r26 1]) s₆ fun t =>
      (t.gpr .r26 = mask true ∧ t.mem = s₆.mem) ∧ Keep [.r26] s₆ t := by
    refine WP.keep _ ?_ (by decide)
    prun
    rfl
  refine WP.seq (WP.mono h26 fun s₇ ⟨⟨a26, m7⟩, k7⟩ => ?_)
  have Q7 := Q6.step hL k7 (by decide) (by rw [m7]; exact QArr.refl _ _)
  -- What the loads left.
  have o56 : Outside L.Q (slot 4 7) (8 * 4) s₅.mem s₇.mem := by rw [m7]; exact o6
  have e5 : arrQ s₇.mem L 5 = rOf s.mem L sig := by
    rw [arrQ, arr, Outside.val32 o56 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega),
      Outside.val32 o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega), m4]
    rw [arrQ, arr] at v5; rw [v5, m21]; simp only [rOf, off, BitVec.add_zero]
  have e6 : arrQ s₇.mem L 6 = sOf s.mem L sig := by
    rw [arrQ, arr, Outside.val32 o56 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]
    rw [arrQ, arr] at v6
    rw [v6, m4, (hsg.sub (o := L.ql) (k := L.ql) (by omega)).bytes (qa3.qbody.body hL) hL.z256, m21]
    rfl
  have qa7 : QArr L s.mem s₇.mem := by
    rw [← m21, m7]
    exact (qa3.trans (by rw [← m4]; exact qa5)).trans qa6
  have top5' : word s₇.mem L.Q (slot 4 5 + 8 * 4) = 0 := by
    rw [Outside.word o56 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega),
      Outside.word o5 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega), m4]
    exact top5
  have top6' : word s₇.mem L.Q (slot 4 6 + 8 * 4) = 0 := by
    rw [Outside.word o56 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]
    exact top6
  have z7' : arr s₇.mem L.Q 4 7 = 0 := by rw [m7]; exact z7
  refine WP.seq (WP.mono (inRange_ok Q7.inq.env (a := 5) (b := true) (by decide) (by decide) top5' z7' a26)
    fun s₈ ⟨⟨b26, o8⟩, k8⟩ => ?_)
  have qa8 : QArr L s₇.mem s₈.mem := QArr.of o8 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have Q8 := Q7.step hL k8 (by decide) qa8
  have keep3 : ∀ {m m' : Mem} (o : Outside L.Q (slot 4 3) (8 * (4 + 2)) m m') (j : Nat), j < 28 → j ≠ 3 →
      arr m' L.Q 4 j = arr m L.Q 4 j := fun o j hj h3 => Outside.arrEq o hj h3 hn
  refine WP.mono (inRange_ok Q8.inq.env (a := 6) (b := _) (by decide) (by decide)
    (by rw [Outside.word o8 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)]; exact top6')
    (by rw [keep3 o8 7 (by decide) (by decide)]; exact z7') b26) fun t ⟨⟨c26, o9⟩, k9⟩ => ?_
  have qa9 : QArr L s₈.mem t.mem := QArr.of o9 (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)
  have a0 : arr s₇.mem L.Q 4 0 = arrQ s.mem L 0 := qa7.arr0
  have a6' : arr s₇.mem L.Q 4 6 = sOf s.mem L sig := e6
  refine ⟨⟨Q8.step hL k9 (by decide) qa9, ?_, ?_, (qa7.trans qa8).trans qa9⟩, ?_⟩
  · rw [arrQ, keep3 o9 5 (by decide) (by decide), keep3 o8 5 (by decide) (by decide)]; exact e5
  · rw [c26, keep3 o8 6 (by decide) (by decide), keep3 o8 0 (by decide) (by decide), a0, a6']
    rw [arrQ] at e5
    simp only [Bool.true_and, Bool.decide_and, e5]
  · exact (((((((k12.trans k3).trans k4).trans k5).trans k6).trans k7).trans k8).trans k9).mono (by decide)

/-! ## Changes in the Q space's arrays and the buffer -/

/-- Memory changed only in the Q space's arrays from array 1 on, or in the
buffer (which follows the Q space). -/
abbrev QBuf (L : Lay) (m m' : Mem) : Prop := Outside L.Q (slot 4 1) (1600 + 2 * L.pl - slot 4 1) m m'

theorem QBuf.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : QBuf L m₁ m₂) (h₂ : QBuf L m₂ m₃) : QBuf L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem QArr.qbuf {L : Lay} {m m' : Mem} (h : QArr L m m') : QBuf L m m' :=
  h.mono (Nat.le_refl _) (by simp only [slot_eq]; omega)

theorem buf_eq (L : Lay) : L.Buf = off L.Q 1600 := by
  simp only [Lay.Buf, Lay.Q, Lay.bOff, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A change in the buffer. -/
theorem QBuf.ofBuf {L : Lay} (hL : L.Ok) {n : Nat} {m m' : Mem} (h : Outside L.Buf 0 n m m')
    (hn : n ≤ 2 * L.pl) : QBuf L m m' := by
  rw [buf_eq] at h
  have hb := hL.buf_end
  have hw := hL.nowrap
  simp only [Lay.bOff, Lay.qOff, slot_eq] at hb
  exact (outside_shift h (by omega) (by omega)).mono (by simp only [slot_eq]; omega)
    (by simp only [slot_eq]; omega)

theorem QBuf.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have eq : L.qOff = 256 + 28 * (8 * (L.wp + 2)) := rfl
  have eb : L.bOff = L.qOff + 1600 := rfl
  have h' : Outside (off L.S L.qOff) 304 (1600 + 2 * L.pl - 304) m m' := h
  exact (outside_shift h' (by omega) (by omega)).mono (by omega) (by omega)

theorem QBuf.arr0 {L : Lay} {m m' : Mem} (h : QBuf L m m') : arrQ m' L 0 = arrQ m L 0 :=
  Outside.val32 h (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)

theorem QBuf.top0 {L : Lay} {m m' : Mem} (h : QBuf L m m') :
    word m' L.Q (slot 4 0 + 32) = word m L.Q (slot 4 0 + 32) :=
  Outside.word h (by simp only [slot_eq]; omega) (by simp only [slot_eq]; omega)

/-- `QS` after a change in the Q space's arrays or the buffer. -/
theorem QS.stepB {s t : State} {L : Lay} {key sig dig : Addr} {rs : List Reg} (h : QS s L key sig dig)
    (hL : L.Ok) (k : Keep rs s t) (hr : ∀ r ∈ inRegs, r ∉ rs) (hm : QBuf L s.mem t.mem) : QS t L key sig dig :=
  ⟨h.inq.keep k hr, h.scr.congr k.wr, h.hdr.body (hm.body hL) hL⟩

/-- The buffer's bytes are past the Q space. -/
theorem buf_sepQ (L : Lay) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    ∀ x, ofs L.Buf x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  rw [buf_eq] at hx
  have hlt := (x - L.Q).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega)] at hx
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hx
  omega

/-- The buffer's first `n` bytes are a working space. -/
theorem ScrL.bufN {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) {n : Nat} (hn : n ≤ 2 * L.pl) :
    Scr s L.Buf n :=
  scr_prefix (h.buf hL) hn

end VG.Proof.Dsa.PPC64LE
