module

public import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega

/-!
# DSA verification on RISC-V: the pointers, and the ranges of r and s

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyQ.lean`):

* `ptrR_ok`, `ptrS_ok`, `ptrBuf_ok`, `ptrBuf2_ok`: r's, s's and the
  buffer's octets into `s7` and `s8`;
* `loadQ_ok`: a number into the Q space's array `j`;
* `ranges_ok`: into the Q space (q in array 0), r into array 5 and s into
  array 6, and `a4 :=` the mask of `0 < r < q` and `0 < s < q`;
* `QArr`, `QBuf`: changes in the Q space's arrays from array 1 on, and in
  the buffer.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)
open VG.Proof.Bignum.RISCV64.Win (mask)

/-- r and s, from the signature at `sig`. -/
def rOf (m : Mem) (L : Lay) (sig : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m sig L.ql)
def sOf (m : Mem) (L : Lay) (sig : Addr) : Nat := Spec.Dsa.decodeBE (Spec.Rsa.bytesAt m (off sig L.ql) L.ql)

/-! ## The pointers -/

/-- `ptrR`: the signature, `q_len`. -/
theorem ptrR_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrR) s fun t =>
      (t.gpr .s7 = sig ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.s7, .s8] s t := by
  unfold ptrR
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = sig ∧ u.mem = s.mem)
    (by brun [hr.ra, BitVec.add_zero]) (by rfl) (by rfl)) fun u ⟨⟨a7, mu⟩, ku⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .s8) fun t ⟨⟨b8, mt⟩, kt⟩ =>
    ⟨⟨(kt.gpr (by decide)).trans a7, b8, by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-- `ptrS`: the signature plus `q_len`, `q_len`. -/
theorem ptrS_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrS) s fun t =>
      (t.gpr .s7 = off sig L.ql ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.s7, .s8] s t := by
  unfold ptrS
  rw [WP.block_append_iff]
  refine WP.mono (ptrR_ok hs hL hr) fun u ⟨⟨a7, a8, mu⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = off sig L.ql ∧ t.mem = u.mem)
    (by brun [a7, a8, off]) (by rfl) (by rfl)) fun t ⟨⟨c7, mt⟩, kt⟩ =>
    ⟨⟨c7, by rw [kt.gpr (by decide), a8], by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-- `ptrBuf`: the buffer, `q_len`. -/
theorem ptrBuf_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrBuf) s fun t =>
      (t.gpr .s7 = L.Buf ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧ Keep [.s7, .t2, .s8] s t := by
  unfold ptrBuf
  rw [WP.block_append_iff]
  refine WP.mono (bufBase_ok hs hL hr (rd := .s7) (t := .t2) (by decide) (by decide) (by decide))
    fun u ⟨⟨a7, mu⟩, ku⟩ => ?_
  refine WP.mono (getQ_ok (hs.congr ku.2.2) hL (hr.keepM ku mu) .s8) fun t ⟨⟨b8, mt⟩, kt⟩ =>
    ⟨⟨(kt.gpr (by decide)).trans a7, b8, by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-- `ptrBuf2`: the buffer plus 32, `q_len`. -/
theorem ptrBuf2_ok {s : State} {L : Lay} {key sig : Addr} (hs : ScrL s L) (hL : L.Ok) (hr : Regs s L key sig) :
    WP isa (.block ptrBuf2) s fun t =>
      (t.gpr .s7 = off L.Buf 32 ∧ t.gpr .s8 = BitVec.ofNat 64 L.ql ∧ t.mem = s.mem) ∧
        Keep [.s7, .t2, .s8] s t := by
  unfold ptrBuf2
  rw [WP.block_append_iff]
  refine WP.mono (ptrBuf_ok hs hL hr) fun u ⟨⟨a7, a8, mu⟩, ku⟩ => ?_
  refine WP.mono (WP.keep [.s7] (Q := fun t => t.gpr .s7 = off L.Buf 32 ∧ t.mem = u.mem)
    (by brun [a7, off]) (by rfl) (by rfl)) fun t ⟨⟨c7, mt⟩, kt⟩ =>
    ⟨⟨c7, by rw [kt.gpr (by decide), a8], by rw [mt, mu]⟩, (ku.trans kt).mono (by decide)⟩

/-! ## The Q space -/

/-- A Q space state, with `scratch` and the registers `Regs` describes. -/
structure QS (s : State) (L : Lay) (key sig : Addr) : Prop where
  inq : InQ s L
  scr : ScrL s L
  regs : Regs s L key sig

/-- `QS` after a change in the registers apart from those it reads, and in
the body. -/
theorem QS.step {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : QS s L key sig)
    (k : Keep rs s t) (hb : Body L s.mem t.mem) (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) :
    QS t L key sig :=
  ⟨h.inq.keep k fun r h' => hr r (List.mem_append_left _ h'), h.scr.congr k.2.2,
    h.regs.keep k hb fun r h' => hr r (List.mem_append_right _ h')⟩

/-- `QS` through a block that keeps memory. -/
theorem QS.stepM {s t : State} {L : Lay} {key sig : Addr} {rs : List Reg} (h : QS s L key sig)
    (k : Keep rs s t) (hm : t.mem = s.mem) (hr : ∀ r ∈ inRegs ++ regsRegs, r ∉ rs := by decide) :
    QS t L key sig :=
  h.step k (by rw [hm]; exact Body.refl _ _) hr

/-- A buffer apart from `scratch` is apart from the Q space. -/
theorem Src.sepQ {s : State} {L : Lay} {D : Addr} {n : Nat} (h : Src s L D n) (hL : L.Ok) :
    ∀ i < n, ∀ x, ofs L.Q x < 1600 → off D i ≠ x :=
  h.sepIn (by have := hL.buf_end; simp only [Lay.bOff] at this; omega_arith) hL.nowrap

/-- Memory changed only in the Q space's arrays from array 1 on. -/
abbrev QArr (L : Lay) (m m' : Mem) : Prop := Outside L.Q (slot L.wq 1) (27 * (8 * (L.wq + 2))) m m'

theorem QArr.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : QArr L m₁ m₂) (h₂ : QArr L m₂ m₃) : QArr L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem QArr.of {L : Lay} {o n : Nat} {m m' : Mem} (h : Outside L.Q o n m m') (ho : slot L.wq 1 ≤ o)
    (hn : o + n ≤ slot L.wq 28) : QArr L m m' :=
  h.mono ho (by simp only [Lay.slot_eq] at hn ⊢; omega_arith)

theorem QArr.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') : Body L m m' :=
  Body.ofQ hL h (by have := hL.qslot; simp only [Lay.slot_eq] at this ⊢; omega_arith)

/-- Array 0 and its word `w`, kept by a change from array 1 on. -/
theorem QArr.arr0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') : arrQ m' L 0 = arrQ m L 0 :=
  h.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega_arith))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega_arith)

theorem QArr.top0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') :
    word m' L.Q (slot L.wq 0 + 8 * L.wq) = word m L.Q (slot L.wq 0 + 8 * L.wq) :=
  h.word (Or.inl (by simp only [Lay.slot_eq]; omega_arith))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega_arith)

/-- `loadArr j` in the Q space, from a buffer apart from `scratch`. -/
theorem loadQ_ok {s : State} {L : Lay} {key sig N : Addr} {k j : Nat} (h : QS s L key sig) (hL : L.Ok)
    (hj : j < 28) (hsrc : Src s L N k) (h7 : s.gpr .s7 = N) (h8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * L.wq) :
    WP isa (loadArr j) s fun t =>
      (QS t L key sig ∧ arrQ t.mem L j = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) ∧
        word t.mem L.Q (slot L.wq j + 8 * L.wq) = 0 ∧
        Outside L.Q (slot L.wq j) (8 * (L.wq + 1)) s.mem t.mem) ∧ Keep loadRegs s t := by
  have hA := h.inq.env.arr hj
  have hqs := hL.qslot
  refine WP.mono (loadArr_ok h.inq.env hj (by rw [h7]; exact (BitVec.add_zero _).symm) h8 hk hkw hsrc.rd
    (hsrc.sepQ hL)) fun t ⟨⟨v, top, o, a7⟩, kt⟩ => ?_
  have hb : Body L s.mem t.mem := Body.ofQ hL o (by omega_arith)
  exact ⟨⟨⟨⟨⟨h.inq.env.hs.congr kt.2.2, a7, (kt.gpr (by decide)).trans h.inq.env.s5,
      (kt.gpr (by decide)).trans h.inq.env.t0, h.inq.env.w2, h.inq.env.w48, h.inq.env.hZ⟩,
      (kt.gpr (by decide)).trans h.inq.s6⟩, h.scr.congr kt.2.2, h.regs.keep kt hb⟩, v, top, o⟩, kt⟩

/-! ## The ranges -/

theorem mask_and (a b : Bool) : mask a &&& mask b = mask (a && b) := by
  cases a <;> cases b <;> rfl

/-- The registers `inRange` writes. -/
def inRangeRegs : List Reg := belowRegs ++ eqRegs .a2 ++ [.a1, .a4]

/-- `inRange a`: `a4 &=` the mask of `0 < [a] < [0]`, with 0 in array 7 and
`[a]`'s word `w` zero; array 3 changes. -/
theorem inRange_ok {s : State} {B : Addr} {Z w a : Nat} {b : Bool} (h : Env s B Z w) (ha : a < 28)
    (ha3 : a ≠ 3) (ha7 : a ≠ 7) (top : word s.mem B (slot w a + 8 * w) = 0)
    (h7 : wordsVal s.mem B (slot w 7) w = 0) (h4 : s.gpr .a4 = mask b) :
    WP isa (inRange a) s fun t =>
      (t.gpr .a4 = mask (b && decide (0 < wordsVal s.mem B (slot w a) w ∧
          wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w)) ∧
        Outside B (slot w 3) (8 * w) s.mem t.mem) ∧ Keep inRangeRegs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  have hZa := h.arr ha
  have hZ7 := h.arr (show 7 < 28 by decide)
  have s3a := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ a by omega)
  have s37 := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ 7 by decide)
  unfold inRange
  refine WP.seq (WP.mono (below_ok h ha ha3 top) fun s₁ ⟨⟨b1, o1⟩, k1⟩ => ?_)
  have h1 := h.keep k1
  refine WP.seq (WP.mono (eqMask_ok h1 (j := a) (k := 7) (rd := .a2) ha (by decide) (by decide))
    fun s₂ ⟨⟨c2, m2⟩, k2⟩ => ?_)
  rw [o1.wordsVal (by omega) (by omega_arith), o1.wordsVal (by omega) (by omega_arith), h7] at c2
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s₂ ((k2.gpr (by decide)).trans b1) c2) fun s₃ ⟨⟨d1, m3⟩, k3⟩ => ?_
  have k13 := (k1.trans k2).trans k3
  refine WP.mono (WP.keep [.a4] (Q := fun t => t.gpr .a4 = mask (b && decide (0 < wordsVal s.mem B (slot w a) w ∧
      wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w)) ∧ t.mem = s₃.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨t4, mt⟩, kt⟩ => ⟨⟨t4, by rw [mt, m3, m2]; exact o1⟩, (k13.trans kt).mono (by decide)⟩
  brun [d1, (k13.gpr (r := .a4) (by decide)).trans h4, mask_and]
  congr 1
  cases b <;> by_cases h0 : wordsVal s.mem B (slot w a) w = 0 <;>
    by_cases hl : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w <;> simp [h0, hl] <;> omega

/-- The registers `ranges` writes. -/
def rangesRegs : List Reg :=
  enterRegs ++ [.s7, .s8] ++ loadRegs ++ [.s0, .t3, .t5] ++ [.a4] ++ inRangeRegs

/-- `ranges`: into the Q space, r into array 5 and s into array 6, and `a4`
the mask of both in `(0, q)`, q in array 0. -/
theorem ranges_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (hs : ScrL s L)
    (hr : Regs s L key sig) (hsg : Src s L sig (2 * L.ql)) :
    WP isa ranges s fun t =>
      (QS t L key sig ∧ arrQ t.mem L 5 = rOf s.mem L sig ∧
        t.gpr .a4 = mask (decide ((0 < rOf s.mem L sig ∧ rOf s.mem L sig < arrQ s.mem L 0) ∧
          (0 < sOf s.mem L sig ∧ sOf s.mem L sig < arrQ s.mem L 0))) ∧
        QArr L s.mem t.mem) ∧ Keep rangesRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  have hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega
  have e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  have e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  have e7 := e 7; have e8 := e 8; have e28 := e 28
  unfold ranges
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  have Q1 : QS s₁ L key sig := ⟨q1, hs.congr k1.2.2, hr.keepM k1 m1⟩
  refine WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_
  have Q2 := Q1.stepM k2 m2
  have k12 := k1.trans k2
  have m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide)
      ((hsg.keep k12.2.1 k12.2.2).sub (o := 0) (k := L.ql) (by omega)) (by rw [a7, off, BitVec.add_zero]) a8
      (by omega) (by omega)) fun s₃ ⟨⟨Q3, v5, top5, o3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (ptrS_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ => ?_)
  have Q4 := Q3.stepM k4 m4
  have k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q4 hL (by decide)
      ((hsg.keep k14.2.1 k14.2.2).sub (o := L.ql) (k := L.ql) (by omega)) b7 b8 (by omega) (by omega))
    fun s₅ ⟨⟨Q5, v6, top6, o5⟩, k5⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q5.inq.env (j := 7) (by decide)) fun s₆ ⟨⟨z7, o6⟩, k6⟩ => ?_)
  have Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega))
  have h4 : WP isa (.block [.li .a4 (-1)]) s₆ fun t =>
      (t.gpr .a4 = mask true ∧ t.mem = s₆.mem) ∧ Keep [.a4] s₆ t := by
    refine WP.keep _ ?_ (by decide) (by rfl)
    brun [exec_li (show imm12 (-1) by decide)]
    rfl
  refine WP.seq (WP.mono h4 fun s₇ ⟨⟨a4, m7⟩, k7⟩ => ?_)
  have Q7 := Q6.stepM k7 m7
  -- What the loads left.
  have o57 : Outside L.Q (slot L.wq 7) (8 * L.wq) s₅.mem s₇.mem := by rw [m7]; exact o6
  have e5' : wordsVal s₇.mem L.Q (slot L.wq 5) L.wq = rOf s.mem L sig := by
    rw [o57.wordsVal (by omega) (by omega_arith), o5.wordsVal (by omega) (by omega_arith), m4]
    refine v5.trans ?_
    rw [m21]; simp only [rOf, off, BitVec.add_zero]
  have e6' : wordsVal s₇.mem L.Q (slot L.wq 6) L.wq = sOf s.mem L sig := by
    rw [o57.wordsVal (by omega) (by omega_arith)]
    refine v6.trans ?_
    rw [m4, (hsg.sub (o := L.ql) (k := L.ql) (by omega)).bytes (Body.ofQ hL o3 (by omega))
      (by have := hL.z256; omega), m21]
    rfl
  have e0' : wordsVal s₇.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [o57.wordsVal (by omega) (by omega_arith), o5.wordsVal (by omega) (by omega_arith), m4,
      o3.wordsVal (by omega) (by omega_arith), m21]
  have top5' : word s₇.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by
    rw [o57.word (by omega) (by omega_arith), o5.word (by omega) (by omega_arith), m4]; exact top5
  have top6' : word s₇.mem L.Q (slot L.wq 6 + 8 * L.wq) = 0 := by
    rw [o57.word (by omega) (by omega_arith)]; exact top6
  have z7' : wordsVal s₇.mem L.Q (slot L.wq 7) L.wq = 0 := by rw [m7]; exact z7
  refine WP.seq (WP.mono (inRange_ok Q7.inq.env (a := 5) (b := true) (by decide) (by decide) (by decide)
    top5' z7' a4) fun s₈ ⟨⟨b4, o8⟩, k8⟩ => ?_)
  have Q8 := Q7.step k8 (Body.ofQ hL o8 (by omega))
  refine WP.mono (inRange_ok Q8.inq.env (a := 6) (by decide) (by decide) (by decide)
    (by rw [o8.word (by omega) (by omega_arith)]; exact top6')
    (by rw [o8.wordsVal (by omega) (by omega_arith)]; exact z7') b4) fun t ⟨⟨c4, o9⟩, k9⟩ => ?_
  have qa : QArr L s.mem t.mem := by
    have qa1 : QArr L s₂.mem s₃.mem := QArr.of o3 (by omega) (by omega)
    have qa2 : QArr L s₃.mem s₅.mem := by rw [← m4]; exact QArr.of o5 (by omega) (by omega)
    have qa3 : QArr L s₅.mem s₇.mem := by rw [m7]; exact QArr.of o6 (by omega) (by omega)
    have qa4 : QArr L s₇.mem t.mem := (QArr.of o8 (by omega) (by omega)).trans (QArr.of o9 (by omega) (by omega))
    rw [← m21]; exact ((qa1.trans qa2).trans qa3).trans qa4
  refine ⟨⟨Q8.step k9 (Body.ofQ hL o9 (by omega)), ?_, ?_, qa⟩, ?_⟩
  · rw [arrQ, o9.wordsVal (by omega) (by omega_arith), o8.wordsVal (by omega) (by omega_arith)]; exact e5'
  · rw [c4, o8.wordsVal (by omega) (by omega_arith), o8.wordsVal (by omega) (by omega_arith), e0', e5', e6']
    simp only [Bool.true_and, Bool.decide_and]
  · exact ((((((k12.trans k3).trans k4).trans k5).trans k6).trans k7).trans (k8.trans k9)).mono (by decide)

/-! ## Changes in the Q space's arrays and the buffer -/

/-- Memory changed only in the Q space's arrays from array 1 on, or in the
buffer (which follows the Q space). -/
abbrev QBuf (L : Lay) (m m' : Mem) : Prop := Outside L.Q (slot L.wq 1) (1600 + 2 * L.pl - slot L.wq 1) m m'

theorem QBuf.trans {L : Lay} {m₁ m₂ m₃ : Mem} (h₁ : QBuf L m₁ m₂) (h₂ : QBuf L m₂ m₃) : QBuf L m₁ m₃ :=
  Outside.trans h₁ h₂

theorem QArr.qbuf {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QArr L m m') : QBuf L m m' :=
  h.mono (Nat.le_refl _) (by have := hL.qslot; simp only [Lay.slot_eq] at this ⊢; omega_arith)

theorem buf_eq (L : Lay) : L.Buf = off L.Q 1600 := by
  simp only [Lay.Buf, Lay.Q, Lay.bOff, off, BitVec.add_assoc, BitVec.ofNat_add_ofNat]

/-- A change in the buffer. -/
theorem QBuf.ofBuf {L : Lay} (hL : L.Ok) {n : Nat} {m m' : Mem} (h : Outside L.Buf 0 n m m')
    (hn : n ≤ 2 * L.pl) : QBuf L m m' := by
  rw [buf_eq] at h
  have hb := hL.buf_end
  have hw := hL.nowrap
  have hqs := hL.qslot
  simp only [Lay.bOff, Lay.qOff, Lay.slot_eq] at hb hqs
  exact (outside_shift h (by omega_arith) (by omega_arith)).mono (by simp only [Lay.slot_eq]; omega_arith)
    (by simp only [Lay.slot_eq]; omega_arith)

theorem QBuf.body {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') : Body L m m' := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  have hwq := hL.wq_ge
  have eq : L.qOff = 256 + 28 * (8 * (L.wp + 2)) := rfl
  have eb : L.bOff = L.qOff + 1600 := rfl
  have e1 : slot L.wq 1 = 256 + 8 * (L.wq + 2) := by simp only [Lay.slot_eq]; omega
  have h' : Outside L.Q (256 + 8 * (L.wq + 2)) (1600 + 2 * L.pl - (256 + 8 * (L.wq + 2))) m m' := by
    rw [← e1]; exact h
  exact (outside_shift h' (by omega_arith) (by omega_arith)).mono (by omega_arith) (by omega_arith)

theorem QBuf.arr0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') : arrQ m' L 0 = arrQ m L 0 :=
  h.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega_arith))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega_arith)

theorem QBuf.top0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') :
    word m' L.Q (slot L.wq 0 + 8 * L.wq) = word m L.Q (slot L.wq 0 + 8 * L.wq) :=
  h.word (Or.inl (by simp only [Lay.slot_eq]; omega_arith))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega_arith)

/-- The buffer's bytes are past the Q space. -/
theorem buf_sepQ (L : Lay) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    ∀ x, ofs L.Buf x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  rw [buf_eq] at hx
  have hlt := (x - L.Q).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega_arith)] at hx
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hx
  omega_arith

/-- The buffer's bytes are apart from the Q space. -/
theorem buf_apartQ (L : Lay) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    ∀ i < n, ∀ x, ofs L.Q x < 1600 → off L.Buf i ≠ x := by
  intro i hi x hx e
  subst e
  have := buf_sepQ L hn (off L.Buf i) (by rw [ofs_off0 L.Buf (by omega_arith)]; exact hi)
  omega_arith

/-- The buffer's bytes, kept by a change in the Q space's arrays. -/
theorem QArr.bufBytes {L : Lay} {m m' : Mem} (h : QArr L m m') (hL : L.Ok) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    Spec.Rsa.bytesAt m' L.Buf n = Spec.Rsa.bytesAt m L.Buf n := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  have hi := List.mem_range.mp hi
  have := buf_sepQ L (n := n) hn (L.Buf + BitVec.ofNat 64 i)
    (by rw [show L.Buf + BitVec.ofNat 64 i = off L.Buf i from rfl, ofs_off0 L.Buf (by omega_arith)]; exact hi)
  have := hL.qslot
  simp only [Lay.slot_eq] at *
  omega_arith

/-- The buffer's bytes from `o` on are writable. -/
theorem ScrL.bufSt {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) {o k : Nat} (hk : o + k ≤ 2 * L.pl) :
    ∀ i < k, InRegions s.wr (off (off L.Buf o) i) 1 := fun i hi => by
  have := (h.buf hL).st (d := o + i) (n := 1) (by omega)
  rwa [off_off]

theorem buf_nowrap {L : Lay} (hL : L.Ok) {o k : Nat} (hk : o + k ≤ 2 * L.pl) (hk0 : 0 < k) :
    (off L.Buf o).toNat + k ≤ 2 ^ 64 := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  rw [Lay.Buf, off_off, off, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.bOff + o < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show L.S.toNat + (L.bOff + o) < 2 ^ 64 by omega_arith)]
  omega

/-- The buffer from `d ≥ 1600` of the Q space on is past it. -/
theorem sepQ_from (L : Lay) {d n : Nat} (hd : 1600 ≤ d) (hn : d + n ≤ 2 ^ 64) :
    ∀ x, ofs (off L.Q d) x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  have hlt := (x - L.Q).isLt
  simp only [ofs, off] at hx ⊢
  rw [Offset.toNat_sub_add x L.Q (by omega_arith)] at hx
  by_contra hc
  rw [Nat.mod_eq_of_lt (by omega)] at hx
  omega_arith

/-- The buffer's first `n` bytes are a working space. -/
theorem ScrL.bufN {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) {n : Nat} (hn : n ≤ 2 * L.pl) :
    Scr s L.Buf n :=
  scr_prefix (h.buf hL) hn

end VG.Proof.Dsa.RISCV64
