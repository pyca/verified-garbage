module

public import VerifiedGarbage.Proof.Bignum.RISCV64.PubMont
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.RISCV64.PreR2
public import VerifiedGarbage.Proof.Dsa.RISCV64.Elem
public import VerifiedGarbage.Impl.Dsa.RISCV64.Verify

/-! ### `Dsa.RISCV64.VerifyQ`, which this module and modules that import it used -/

section

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

/-- `loadArr j` in the Q space, from a buffer apart from `scratch`. -/
theorem loadQ_ok {s : State} {L : Lay} {key sig N : Addr} {k j : Nat} (h : QS s L key sig) (hL : L.Ok)
    (hj : j < 28) (hsrc : Src s L N k) (h7 : s.gpr .s7 = N) (h8 : s.gpr .s8 = BitVec.ofNat 64 k)
    (hk : 1 ≤ k) (hkw : k ≤ 8 * L.wq) :
    WP isa (loadArr j) s fun t =>
      (QS t L key sig ∧ arrQ t.mem L j = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem N k) ∧
        word t.mem L.Q (slot L.wq j + 8 * L.wq) = 0 ∧
        Outside L.Q (slot L.wq j) (8 * (L.wq + 1)) s.mem t.mem) ∧ Keep loadRegs s t := by
  obtain hA := h.inq.env.arr hj
  have hqs := hL.qslot
  refine WP.mono (loadArr_ok h.inq.env hj (by rw [h7]; exact (BitVec.add_zero _).symm) h8 hk hkw hsrc.rd
    (hsrc.sepQ hL)) fun t ⟨⟨v, top, o, a7⟩, kt⟩ => ?_
  obtain hb : Body L s.mem t.mem := Body.ofQ hL o (by omega_arith)
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
  obtain hZa := h.arr ha
  obtain hZ7 := h.arr (show 7 < 28 by decide)
  obtain s3a := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ a by omega)
  obtain s37 := VG.Proof.Bignum.slot_sep (w := w) (show 3 ≠ 7 by decide)
  unfold inRange
  refine WP.seq (WP.mono (below_ok h ha ha3 top) fun s₁ ⟨⟨b1, o1⟩, k1⟩ => ?_)
  obtain h1 := h.keep k1
  refine WP.seq (WP.mono (eqMask_ok h1 (j := a) (k := 7) (rd := .a2) ha (by decide) (by decide))
    fun s₂ ⟨⟨c2, m2⟩, k2⟩ => ?_)
  rw [o1.wordsVal (by omega_using [s3a]) (by omega_arith), o1.wordsVal (by omega_using [s37]) (by omega_arith), h7] at c2
  rw [WP.block_append_iff]
  refine WP.mono (clear_ok s₂ ((k2.gpr (by decide)).trans b1) c2) fun s₃ ⟨⟨d1, m3⟩, k3⟩ => ?_
  obtain k13 := (k1.trans k2).trans k3
  refine WP.mono (WP.keep [.a4] (Q := fun t => t.gpr .a4 = mask (b && decide (0 < wordsVal s.mem B (slot w a) w ∧
      wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w)) ∧ t.mem = s₃.mem) ?_ (by decide) (by rfl))
    fun t ⟨⟨t4, mt⟩, kt⟩ => ⟨⟨t4, by rw [mt, m3, m2]; exact o1⟩, (k13.trans kt).mono (by decide)⟩
  brun [d1, (k13.gpr (r := .a4) (by decide)).trans h4, mask_and]
  congr 1
  cases b <;> by_cases h0 : wordsVal s.mem B (slot w a) w = 0 <;>
    by_cases hl : wordsVal s.mem B (slot w a) w < wordsVal s.mem B (slot w 0) w <;> simp [h0, hl] <;> omega_using [h0]

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
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  obtain e7 := e 7; have e8 := e 8; have e28 := e 28
  unfold ranges
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (enterQ_ok hL hs hr) fun s₁ ⟨⟨q1, m1⟩, k1⟩ => ?_
  obtain Q1 : QS s₁ L key sig := ⟨q1, hs.congr k1.2.2, hr.keepM k1 m1⟩
  refine WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_
  obtain Q2 := Q1.stepM k2 m2
  obtain k12 := k1.trans k2
  obtain m21 : s₂.mem = s.mem := m2.trans m1
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide)
      ((hsg.keep k12.2.1 k12.2.2).sub (o := 0) (k := L.ql) (by omega_using [])) (by rw [a7, off, BitVec.add_zero]) a8
      (by omega_using [hql]) (by omega_using [hwq])) fun s₃ ⟨⟨Q3, v5, top5, o3⟩, k3⟩ => ?_)
  refine WP.seq (WP.mono (ptrS_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ => ?_)
  obtain Q4 := Q3.stepM k4 m4
  obtain k14 := (k12.trans k3).trans k4
  refine WP.seq (WP.mono (loadQ_ok (j := 6) Q4 hL (by decide)
      ((hsg.keep k14.2.1 k14.2.2).sub (o := L.ql) (k := L.ql) (by omega_using [])) b7 b8 (by omega_using [hql]) (by omega_using [hwq]))
    fun s₅ ⟨⟨Q5, v6, top6, o5⟩, k5⟩ => ?_)
  refine WP.seq (WP.mono (zeroArr_ok Q5.inq.env (j := 7) (by decide)) fun s₆ ⟨⟨z7, o6⟩, k6⟩ => ?_)
  obtain Q6 := Q5.step k6 (Body.ofQ hL o6 (by omega_using [hwq, e7]))
  obtain h4 : WP isa (.block [.li .a4 (-1)]) s₆ fun t =>
      (t.gpr .a4 = mask true ∧ t.mem = s₆.mem) ∧ Keep [.a4] s₆ t := by
    refine WP.keep _ ?_ (by decide) (by rfl)
    brun [exec_li (show imm12 (-1) by decide)]
    rfl
  refine WP.seq (WP.mono h4 fun s₇ ⟨⟨a4, m7⟩, k7⟩ => ?_)
  obtain Q7 := Q6.stepM k7 m7
  -- What the loads left.
  obtain o57 : Outside L.Q (slot L.wq 7) (8 * L.wq) s₅.mem s₇.mem := by rw [m7]; exact o6
  obtain e5' : wordsVal s₇.mem L.Q (slot L.wq 5) L.wq = rOf s.mem L sig := by
    rw [o57.wordsVal (by omega_using [e5, e7]) (by omega_arith), o5.wordsVal (by omega_using [e5, e6]) (by omega_arith), m4]
    refine v5.trans ?_
    rw [m21]; simp only [rOf, off, BitVec.add_zero]
  obtain e6' : wordsVal s₇.mem L.Q (slot L.wq 6) L.wq = sOf s.mem L sig := by
    rw [o57.wordsVal (by omega_using [e6, e7]) (by omega_arith)]
    refine v6.trans ?_
    rw [m4, (hsg.sub (o := L.ql) (k := L.ql) (by omega_using [])).bytes (Body.ofQ hL o3 (by omega_using [hwq, e5]))
      (by have := hL.z256; omega_using [this]), m21]
    rfl
  obtain e0' : wordsVal s₇.mem L.Q (slot L.wq 0) L.wq = arrQ s.mem L 0 := by
    rw [o57.wordsVal (by omega_using [e0, e7]) (by omega_arith), o5.wordsVal (by omega_using [e0, e6]) (by omega_arith), m4,
      o3.wordsVal (by omega_using [e0, e5]) (by omega_arith), m21]
  obtain top5' : word s₇.mem L.Q (slot L.wq 5 + 8 * L.wq) = 0 := by
    rw [o57.word (by omega_using [e5, e7]) (by omega_arith), o5.word (by omega_using [e5, e6]) (by omega_arith), m4]; exact top5
  obtain top6' : word s₇.mem L.Q (slot L.wq 6 + 8 * L.wq) = 0 := by
    rw [o57.word (by omega_using [e6, e7]) (by omega_arith)]; exact top6
  obtain z7' : wordsVal s₇.mem L.Q (slot L.wq 7) L.wq = 0 := by rw [m7]; exact z7
  refine WP.seq (WP.mono (inRange_ok Q7.inq.env (a := 5) (b := true) (by decide) (by decide) (by decide)
    top5' z7' a4) fun s₈ ⟨⟨b4, o8⟩, k8⟩ => ?_)
  obtain Q8 := Q7.step k8 (Body.ofQ hL o8 (by omega_using [hwq, e3]))
  refine WP.mono (inRange_ok Q8.inq.env (a := 6) (by decide) (by decide) (by decide)
    (by rw [o8.word (by omega_using [e3, e6]) (by omega_arith)]; exact top6')
    (by rw [o8.wordsVal (by omega_using [e3, e7]) (by omega_arith)]; exact z7') b4) fun t ⟨⟨c4, o9⟩, k9⟩ => ?_
  obtain qa : QArr L s.mem t.mem := by
    obtain qa1 : QArr L s₂.mem s₃.mem := QArr.of o3 (by omega_using [e1, e5]) (by omega_using [e5, e28])
    obtain qa2 : QArr L s₃.mem s₅.mem := by rw [← m4]; exact QArr.of o5 (by omega_using [e1, e6]) (by omega_using [e6, e28])
    obtain qa3 : QArr L s₅.mem s₇.mem := by rw [m7]; exact QArr.of o6 (by omega_using [e1, e7]) (by omega_using [e7, e28])
    obtain qa4 : QArr L s₇.mem t.mem := (QArr.of o8 (by omega_using [e1, e3]) (by omega_using [e3, e28])).trans (QArr.of o9 (by omega_using [e1, e3]) (by omega_using [e3, e28]))
    rw [← m21]; exact ((qa1.trans qa2).trans qa3).trans qa4
  refine ⟨⟨Q8.step k9 (Body.ofQ hL o9 (by omega_using [hwq, e3])), ?_, ?_, qa⟩, ?_⟩
  · rw [arrQ, o9.wordsVal (by omega_using [e3, e5]) (by omega_arith), o8.wordsVal (by omega_using [e3, e5]) (by omega_arith)]; exact e5'
  · rw [c4, o8.wordsVal (by omega_using [e3, e6]) (by omega_arith), o8.wordsVal (by omega_using [e0, e3]) (by omega_arith), e0', e5', e6']
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
  obtain e1 : slot L.wq 1 = 256 + 8 * (L.wq + 2) := by simp only [Lay.slot_eq]; omega_using []
  obtain h' : Outside L.Q (256 + 8 * (L.wq + 2)) (1600 + 2 * L.pl - (256 + 8 * (L.wq + 2))) m m' := by
    rw [← e1]; exact h
  exact (outside_shift h' (by omega_arith) (by omega_arith)).mono (by omega_arith) (by omega_arith)

theorem QBuf.arr0 {L : Lay} (hL : L.Ok) {m m' : Mem} (h : QBuf L m m') : arrQ m' L 0 = arrQ m L 0 :=
  h.wordsVal (Or.inl (by simp only [Lay.slot_eq]; omega_arith))
    (by have := hL.wq_ge; simp only [Lay.slot_eq]; omega_arith)

/-- The buffer's bytes are past the Q space. -/
theorem buf_sepQ (L : Lay) {n : Nat} (hn : n ≤ 2 ^ 64 - 1600) :
    ∀ x, ofs L.Buf x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  rw [buf_eq] at hx
  obtain hlt := (x - L.Q).isLt
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
  obtain hi := List.mem_range.mp hi
  have := buf_sepQ L (n := n) hn (L.Buf + BitVec.ofNat 64 i)
    (by rw [show L.Buf + BitVec.ofNat 64 i = off L.Buf i from rfl, ofs_off0 L.Buf (by omega_arith)]; exact hi)
  have := hL.qslot
  simp only [Lay.slot_eq] at *
  omega_arith

/-- The buffer's bytes from `o` on are writable. -/
theorem ScrL.bufSt {s : State} {L : Lay} (h : ScrL s L) (hL : L.Ok) {o k : Nat} (hk : o + k ≤ 2 * L.pl) :
    ∀ i < k, InRegions s.wr (off (off L.Buf o) i) 1 := fun i hi => by
  have := (h.buf hL).st (d := o + i) (n := 1) (by omega_using [hk, hi])
  rwa [off_off]

theorem buf_nowrap {L : Lay} (hL : L.Ok) {o k : Nat} (hk : o + k ≤ 2 * L.pl) (hk0 : 0 < k) :
    (off L.Buf o).toNat + k ≤ 2 ^ 64 := by
  have hb := hL.buf_end
  have hw := hL.nowrap
  rw [Lay.Buf, off_off, off, BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show L.bOff + o < 2 ^ 64 by omega_arith),
    Nat.mod_eq_of_lt (show L.S.toNat + (L.bOff + o) < 2 ^ 64 by omega_arith)]
  omega_using [hk, hb, hw]

/-- The buffer from `d ≥ 1600` of the Q space on is past it. -/
theorem sepQ_from (L : Lay) {d n : Nat} (hd : 1600 ≤ d) (hn : d + n ≤ 2 ^ 64) :
    ∀ x, ofs (off L.Q d) x < n → 1600 ≤ ofs L.Q x := by
  intro x hx
  obtain hlt := (x - L.Q).isLt
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

end

end

/-! ### `Dsa.RISCV64.VerifyInv`, which this module and modules that import it used -/

section

/-!
# DSA verification on RISC-V: `R² mod q`, `q − 2` and `w = s^(q − 2) mod q`

In the Q space, q in array 0:

* `rrQ_ok`: `-q⁻¹ mod 2⁶⁴` into `t1`, `R² mod q` (`R = 2^(64 w)`) into arrays
  1 and 24;
* `minus2_ok`, `qMinus2_ok`: `q − 2` into array 6, then its `q_len` octets
  to the buffer;
* `inverse_ok`: s into array 4, and `s^(q − 2) mod q` into array 4.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot)

/-- `-q⁻¹ mod 2⁶⁴` is in `t1`. -/
abbrev QInv (s : State) (L : Lay) : Prop :=
  ((word s.mem L.Q (slot L.wq 0)).toNat * (s.gpr .t1).toNat + 1) % 2 ^ 64 = 0

/-- The registers `rrQ` writes. -/
def rrQRegs : List Reg := [.s0, .s1, .s2, .s3, .t1] ++ rrRegs

/-- `rrQ`: `-q⁻¹ mod 2⁶⁴` into `t1`, `R² mod q` into arrays 1 and 24. -/
theorem rrQ_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) :
    WP isa rrQ s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L 1 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧
        arrQ t.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 ∧ QArr L s.mem t.mem) ∧ Keep rrQRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain e0 := Lay.slot_eq L.wq 0; have e1 := Lay.slot_eq L.wq 1; have e25 := Lay.slot_eq L.wq 25
  obtain e28 := Lay.slot_eq L.wq 28
  unfold rrQ
  obtain hodd : (word s.mem L.Q (slot L.wq 0)).toNat % 2 = 1 := by
    rw [wordsVal_mod_two _ _ _ (w := L.wq) (by omega_using [hwq])]; exact hqo
  refine WP.seq (WP.mono (minv_ok e.hs e.a7 (slot_al _ _) (by omega_using [e0]) hodd) fun s₁ ⟨⟨i1, m1⟩, k1⟩ => ?_)
  obtain e1' := e.keep k1
  refine WP.mono (rr_ok e1' (by rw [m1]; exact hq)) fun t ⟨⟨r1, r24, o⟩, kt⟩ => ?_
  rw [m1] at r1 r24 o
  obtain qa : QArr L s.mem t.mem := QArr.of o (by omega_using []) (by omega_using [e1, e28])
  refine ⟨⟨h.step (k1.trans kt) (qa.body hL), ?_, r1, r24, qa⟩, k1.trans kt⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [o.word (by omega_using [e0, e1]) (by omega_arith), kt.gpr (by decide)]
  exact i1

/-- The registers `minus2` writes. -/
def m2Regs : List Reg := [.t3, .t4, .t5, .s4, .s2, .s0]

theorem sub_borrow (x : BitVec 64) {c : Nat} (hc : c ≤ 2) :
    (x - BitVec.ofNat 64 c).toNat + c = x.toNat + 2 ^ 64 * (if x.toNat < c then 1 else 0) := by
  have hx := x.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc])]
  split <;> omega_arith

theorem lt_ofNat (x : BitVec 64) {c : Nat} (hc : c ≤ 2) :
    (if x < BitVec.ofNat 64 c then (1 : BitVec 64) else 0) = BitVec.ofNat 64 (if x.toNat < c then 1 else 0) := by
  have : (x < BitVec.ofNat 64 c) ↔ x.toNat < c := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega_using [hc])]
  by_cases h : x.toNat < c <;> simp only [this, h, ite_true, ite_false] <;> rfl

/-- `minus2`: array 6 := `[0] − 2`, for `[0] ≥ 2`. -/
theorem minus2_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w)
    (hq : 2 ≤ wordsVal s.mem B (slot w 0) w) :
    WP isa minus2 s fun t =>
      (wordsVal t.mem B (slot w 6) w = wordsVal s.mem B (slot w 0) w - 2 ∧
        Outside B (slot w 6) (8 * w) s.mem t.mem) ∧ Keep m2Regs s t := by
  have hs := h.hs
  have hnw := hs.nowrap
  obtain hZ6 := h.arr (show 6 < 28 by decide)
  have hw2 := h.w2
  have hw48 := h.w48
  obtain e0 := Lay.slot_eq w 0; have e6 := Lay.slot_eq w 6
  obtain al0 := slot_al w 0
  obtain al6 := slot_al w 6
  unfold minus2
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (h.base (rd := .t3) (by decide) 0) fun s₁ ⟨⟨a3, m1⟩, k1⟩ => ?_
  refine WP.mono ((h.keep k1).base (rd := .t4) (by decide) 6) fun s₂ ⟨⟨a4, m2⟩, k2⟩ => ?_
  obtain k12 := k1.trans k2
  refine WP.mono (WP.keep [.t5, .s4] (Q := fun s₃ => s₃.gpr .t5 = BitVec.ofNat 64 w ∧
      s₃.gpr .s4 = BitVec.ofNat 64 2 ∧ s₃.mem = s₂.mem)
    (by brun [(k12.gpr (r := .t0) (by decide)).trans h.t0, BitVec.add_zero, exec_li_lit (show 2 < 2048 by decide)])
    (by rfl) (by rfl)) fun s₃ ⟨⟨b5, b4, m3⟩, k3⟩ => ?_
  obtain k123 := k12.trans k3
  let Inv : Nat → State → Prop := fun i t =>
    t.gpr .t3 = off B (slot w 0 + 8 * i) ∧ t.gpr .t4 = off B (slot w 6 + 8 * i) ∧
      (∃ c, c ≤ 2 ∧ t.gpr .s4 = BitVec.ofNat 64 c ∧
        wordsVal t.mem B (slot w 6) i + 2 = wordsVal s.mem B (slot w 0) i + 2 ^ (64 * i) * c) ∧
      Outside B (slot w 6) (8 * i) s.mem t.mem ∧ Keep m2Regs s t
  refine WP.mono (wp_countdown (body := .block ([.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .sub .s2 .s2 .s4,
      .addi .s4 .s0 0, .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8] ++
      ([.addi .t5 .t5 (-1)] : List Instr))) (cnt := .t5) (N := w) (by omega_arith) (by omega_using [hw2])
    Inv (fun i hi t ⟨j3, j4, ⟨c, hc, jc, jv⟩, jout, jk⟩ hcnt => ?_)
    ⟨by rw [k3.gpr (by decide), k2.gpr (by decide), a3]; rfl, by rw [k3.gpr (by decide), a4]; rfl,
      ⟨2, by decide, b4, by simp [wordsVal]⟩, by rw [m3, m2, m1]; exact Outside.refl _ _ _ _,
      k123.mono (by decide)⟩ b5)
    fun t ⟨_, _, ⟨c, hc, _, tv⟩, tout, tk⟩ => ⟨⟨?_, tout⟩, tk⟩
  · have hx : word t.mem B (slot w 0 + 8 * i) = word s.mem B (slot w 0 + 8 * i) :=
      jout.word (by omega_using [e0, e6, hi]) (by omega_arith)
    obtain hst : WP isa (.block [.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .sub .s2 .s2 .s4,
        .addi .s4 .s0 0, .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .t5 .t5 (-1)]) t
        fun t' => t' = (((({ ((((t.write .s2 (word t.mem B (slot w 0 + 8 * i))).write .s0
          (if word t.mem B (slot w 0 + 8 * i) < BitVec.ofNat 64 c then 1 else 0)).write .s2
          (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c)).write .s4
          (if word t.mem B (slot w 0 + 8 * i) < BitVec.ofNat 64 c then 1 else 0)) with
          mem := t.mem.writeW (off B (slot w 6 + 8 * i)) (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c) } :
            State).write .t3 (off B (slot w 0 + 8 * i + 8))).write .t4 (off B (slot w 6 + 8 * i + 8))).write .t5
              (t.gpr .t5 - BitVec.ofNat 64 1)) := by
      brun [j3, j4, jc, BitVec.add_zero, (hs.congr jk.2.2).ld (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w 0 + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith),
        (hs.congr jk.2.2).st (show slot w 6 + 8 * i + 8 ≤ Z by omega_arith),
        (hs.congr jk.2.2).al8 (show slot w 6 + 8 * i + 8 ≤ Z by omega_arith) (by omega_arith)]
    refine WP.mono hst fun t' e => ?_
    subst e
    obtain hw := writeW_outside t.mem B (d := slot w 6 + 8 * i)
      (word t.mem B (slot w 0 + 8 * i) - BitVec.ofNat 64 c) (by omega_arith)
    refine ⟨⟨by gsimp; rw [show slot w 0 + 8 * i + 8 = slot w 0 + 8 * (i + 1) by omega_using []],
      by gsimp; rw [show slot w 6 + 8 * i + 8 = slot w 6 + 8 * (i + 1) by omega_using []], ?_, ?_, ?_⟩, by gsimp⟩
    · refine ⟨if (word s.mem B (slot w 0 + 8 * i)).toNat < c then 1 else 0, by split <;> omega_using [], ?_, ?_⟩
      · gsimp; rw [lt_ofNat _ hc, hx]
      · gsimp
        rw [wordsVal_succ_top, wordsVal_succ_top, word_writeW_self,
          hw.wordsVal (Or.inl (Nat.le_refl _)) (by omega_arith), hx]
        obtain hb := sub_borrow (word s.mem B (slot w 0 + 8 * i)) hc
        obtain key := congrArg (fun z => 2 ^ (64 * i) * z) hb
        simp only [Nat.mul_add] at key
        rw [show 64 * (i + 1) = 64 * i + 64 by omega_using [], Nat.pow_add, Nat.mul_assoc]
        omega_using [jv, key]
    · gsimp; exact (jout.mono (Nat.le_refl _) (by omega_using [])).trans (hw.mono (by omega_using []) (by omega_using []))
    · exact Keep.trans' jk (((((((((Keep.write _ _ _).trans (Keep.write _ _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.mem _ _)).trans (Keep.write _ _ _)).trans
        (Keep.write _ _ _)).trans (Keep.write _ _ _)).mono (by decide))
  · have hlt := wordsVal_lt t.mem B (slot w 6) w
    obtain hlt0 := wordsVal_lt s.mem B (slot w 0) w
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega_using [hc]) with rfl | rfl | rfl <;> omega_arith

theorem slot_mono {w j k : Nat} (h : j ≤ k) : slot w j ≤ slot w k := by
  rw [Lay.slot_eq, Lay.slot_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem m2_sep {L : Lay} (hL : L.Ok) : ∀ x, ofs L.Buf x < L.ql → 1600 ≤ ofs L.Q x :=
  buf_sepQ L (by rcases hL.ql with e | e | e <;> omega_using [e])

/-- The registers `qMinus2` writes. -/
def qm2Regs : List Reg := m2Regs ++ [.s7, .t2, .s8] ++ storeRegs

/-- `qMinus2`: the `q_len` octets of `q − 2` to the buffer, for
`2 ≤ q < 2^(8 q_len)`. Arrays 0–5 and 7–27 are kept. -/
theorem qMinus2_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig)
    (hq : 2 ≤ arrQ s.mem L 0) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql)) :
    WP isa qMinus2 s fun t =>
      (QS t L key sig ∧ Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) = arrQ s.mem L 0 - 2 ∧
        (∀ j < 28, j ≠ 6 → arrQ t.mem L j = arrQ s.mem L j) ∧
        word t.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) ∧ QBuf L s.mem t.mem) ∧
        Keep qm2Regs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega_using [e]
  obtain hql' : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain e1 := Lay.slot_eq L.wq 1; have e6 := Lay.slot_eq L.wq 6; have e7 := Lay.slot_eq L.wq 7; have e28 := Lay.slot_eq L.wq 28
  unfold qMinus2
  refine WP.seq (WP.mono (minus2_ok e hq) fun s₁ ⟨⟨v6, o1⟩, k1⟩ => ?_)
  obtain Q1 := h.step k1 (Body.ofQ hL o1 (by omega_using [hwq, e6]))
  refine WP.seq (WP.mono (ptrBuf_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  obtain e2 := Q1.inq.env.keep k2
  refine WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e2 (by decide)
    (by have := ScrL.bufSt (Q1.scr.congr k2.2.2) hL (o := 0) (k := L.ql) (by omega_using [hwq, hpl])
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.ql) (by omega_using [hwq, hpl]) (by omega_using [hql']); simpa only [off, BitVec.add_zero] using this) a7 a8 (by omega_using [hql']) (by omega_using [hwq]) (m2_sep hL))
    fun t ⟨⟨vt, ot⟩, kt⟩ => ?_
  rw [m2] at vt ot
  obtain qb : QBuf L s₁.mem t.mem := QBuf.ofBuf hL ot (by omega_using [hwq, hpl])
  obtain ot' : Outside (off L.Q 1600) 0 L.ql s₁.mem t.mem := by rw [← buf_eq]; exact ot
  obtain otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega_using [hwq])
    (by decide)
  obtain k := (k1.trans k2).trans kt
  refine ⟨⟨Q1.step (k2.trans kt) (qb.body hL), ?_, fun j hj hj6 => ?_, ?_,
    (QArr.of o1 (by omega_using [e1, e6]) (by omega_using [e6, e28])).qbuf hL |>.trans qb⟩, k.mono (by decide)⟩
  · have hql2 : wordsVal s.mem L.Q (slot L.wq 0) L.wq < 2 ^ (8 * L.ql) := hql
    have hq2 : 2 ≤ wordsVal s.mem L.Q (slot L.wq 0) L.wq := hq
    rw [vt, read_low _ _ (w := L.wq) (by omega_using [hwq]) (by rw [v6]; omega_using [hql2]), v6]
  · have := slot_lt (w := L.wq) hj
    obtain sj := VG.Proof.Bignum.slot_sep (w := L.wq) hj6
    rw [arrQ, otq.wordsVal (Or.inl (by omega_using [hqs, this])) (by omega_arith), o1.wordsVal (by omega_using [sj]) (by omega_arith)]
  · have e0 := Lay.slot_eq L.wq 0
    rw [otq.word (Or.inl (by omega_using [e0])) (by omega_arith), o1.word (by omega_using [e6, e0]) (by omega_arith)]

/-- The registers `inverse` writes. -/
def invRegs : List Reg := [.s7, .s8] ++ loadRegs ++ copyRegs ++ [.s7, .t2, .s8, .s9, .s10] ++ Win.powWRegs

/-- `inverse`: s into array 4, then `s^e mod q` into array 4, for the `q_len`
octets `e` of the buffer. Arrays 24–27 and `t1` are kept. -/
theorem inverse_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    (hsg : Src s L sig (2 * L.ql)) (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1)
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) :
    WP isa inverse s fun t =>
      (QS t L key sig ∧ QInv t L ∧
        arrQ t.mem L 4 = sOf s.mem L sig ^ Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem L.Buf L.ql) %
          arrQ s.mem L 0 ∧
        (∀ j < 28, 24 ≤ j → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧ Keep invRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hql : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e24 := e 24; have e28 := e 28
  unfold inverse
  refine WP.seq (WP.mono (ptrS_ok h.scr hL h.regs) fun s₁ ⟨⟨a7, a8, m1⟩, k1⟩ => ?_)
  obtain Q1 := h.stepM k1 m1
  refine WP.seq (WP.mono (loadQ_ok (j := 4) Q1 hL (by decide)
      ((hsg.keep k1.2.1 k1.2.2).sub (o := L.ql) (k := L.ql) (by omega_using [])) a7 a8 (by omega_using [hql]) (by omega_using [hwq]))
    fun s₂ ⟨⟨Q2, v4, _, o2⟩, k2⟩ => ?_)
  rw [m1] at v4 o2
  refine WP.seq (WP.mono (copy_ok Q2.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₃ ⟨⟨c1, o3⟩, k3⟩ => ?_)
  obtain Q3 := Q2.step k3 (Body.ofQ hL o3 (by omega_using [hwq, e1]))
  obtain A0 : arrQ s₃.mem L 0 = arrQ s.mem L 0 := by
    rw [arrQ, o3.wordsVal (by omega_using [e0, e1]) (by omega_arith), o2.wordsVal (by omega_using [e0, e4]) (by omega_arith)]
  obtain W0 : word s₃.mem L.Q (slot L.wq 0) = word s.mem L.Q (slot L.wq 0) := by
    rw [o3.word (by omega_using [e0, e1]) (by omega_arith), o2.word (by omega_using [e0, e4]) (by omega_arith)]
  obtain A4 : arrQ s₃.mem L 4 = sOf s.mem L sig := by
    rw [arrQ, o3.wordsVal (by omega_using [e1, e4]) (by omega_arith)]; exact v4
  obtain A24 : ∀ j < 28, 24 ≤ j → arrQ s₃.mem L j = arrQ s.mem L j := fun j hj hj24 => by
    have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o3.wordsVal (by omega_using [e1, e24, this]) (by omega_arith), o2.wordsVal (by omega_using [e4, e24, this]) (by omega_arith)]
  obtain A1 : arrQ s₃.mem L 1 = 2 ^ (128 * L.wq) % arrQ s.mem L 0 := by
    rw [arrQ, wordsVal_congr (m := s₂.mem) (d := slot L.wq 24) fun i hi => c1 i (by omega_using [hi])]
    rw [← h24, arrQ, o2.wordsVal (by omega_using [e4, e24]) (by omega_arith)]
  obtain hbuf : Spec.Rsa.bytesAt s₃.mem L.Buf L.ql = Spec.Rsa.bytesAt s.mem L.Buf L.ql := by
    obtain qa : QArr L s.mem s₃.mem :=
      (QArr.of o2 (by omega_using [e1, e4]) (by omega_using [e4, e28])).trans (QArr.of o3 (by omega_using []) (by omega_using [e1, e28]))
    exact qa.bufBytes hL (by omega_using [hwq])
  -- The exponent's pointer and length.
  refine WP.seq (WP.block_append (WP.mono (ptrBuf_ok Q3.scr hL Q3.regs) fun s₄ ⟨⟨b7, b8, m4⟩, k4⟩ =>
    WP.mono (WP.keep [.s9, .s10] (Q := fun u => u.gpr .s9 = off L.Buf 0 ∧
      u.gpr .s10 = BitVec.ofNat 64 L.ql ∧ u.mem = s₄.mem) (by brun [b7, b8, BitVec.add_zero]) (by decide) (by rfl))
    fun s₅ ⟨⟨c9, c10, m5⟩, k5⟩ => ?_))
  obtain k35 := k4.trans k5
  obtain m53 : s₅.mem = s₃.mem := by rw [m5, m4]
  obtain e5 := Q3.inq.env.keep k35
  obtain k15 := (((k1.trans k2).trans k3).trans k35)
  refine WP.mono (Win.powWin_ok (D := L.Buf) (L := L.ql) e5.hs (by omega_using [hwq]) (by omega_using [hwq])
    (by omega_using [hwq, e24]) e5.a7 e5.s5 e5.t0
    (by rw [m53, W0, k15.gpr (by decide)]; exact hi)
    (by rw [m53]; show 2 ≤ arrQ s₃.mem L 0; rw [A0]; exact hq2)
    (by rw [m53]; show arrQ s₃.mem L 0 % 2 = 1; rw [A0]; exact hqo)
    (by rw [m53]; show arrQ s₃.mem L 1 < arrQ s₃.mem L 0; rw [A1, A0]; exact Nat.mod_lt _ (by omega_using [hq2]))
    c9 c10 (by omega_using [hql]) (by omega_arith)
    (fun i hi => by
      rw [k35.2.1, k35.2.2]
      exact (ScrL.bufN (s := s₃) Q3.scr hL (n := L.ql) (by rcases hL.pl with e | e | e <;> omega_using [hwq, e])).ld
        (show i + 1 ≤ L.ql by omega_using [hi]))
    (buf_apartQ L (by omega_using [hwq]))) fun t ⟨⟨r4, o4'⟩, k6⟩ => ?_
  obtain o4 : Outside L.Q (slot L.wq 1) (23 * (8 * (L.wq + 2))) s₃.mem t.mem := by rw [← m53]; exact o4'
  rw [m53] at r4
  obtain r4 := r4 (by
    show arrQ s₃.mem L 1 = 2 ^ (64 * L.wq) * 2 ^ (64 * L.wq) % arrQ s₃.mem L 0
    rw [A1, A0, pow_two_mul])
  rw [hbuf] at r4
  obtain qa : QArr L s.mem t.mem :=
    ((QArr.of o2 (by omega_using [e1, e4]) (by omega_using [e4, e28])).trans (QArr.of o3 (by omega_using []) (by omega_using [e1, e28]))).trans
      (QArr.of o4 (by omega_using []) (by omega_using [e1, e28]))
  refine ⟨⟨Q3.step (k35.trans k6) (Body.ofQ hL o4 (by omega_using [hwq, e1])), ?_, ?_, fun j hj hj24 => ?_, qa⟩,
    (k15.trans k6).mono (by decide)⟩
  · show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega_using [e0, e1]) (by omega_arith), W0, (k15.trans k6).gpr (by decide)]; exact hi
  · show wordsVal t.mem L.Q (slot L.wq 4) L.wq = _
    rw [r4]
    show arrQ s₃.mem L 4 ^ _ % arrQ s₃.mem L 0 = _
    rw [A4, A0]
  · have := slot_lt (w := L.wq) hj
    have := slot_mono (w := L.wq) hj24
    rw [arrQ, o4.wordsVal (by omega_using [e1, e24, this]) (by omega_arith)]; exact A24 j hj hj24

end VG.Proof.Dsa.RISCV64

end

end

/-!
# DSA verification on RISC-V: `u1` and `u2`

As on PPC64LE (`Proof/Dsa/PPC64LE/VerifyBody.lean`). `products_ok`: in the Q
space, with q in array 0, `-q⁻¹ mod 2⁶⁴` in `t1`, `R² mod q` in array 24 and
`w` in array 4: the digest's scalar `z` (its first `min(d, qb)` octets, its
address from the header's `hDigest`, the lengths from `hLens`) and r, then
`u1 = z w mod q` and `u2 = r w mod q` (Montgomery multiplications by w, then
by `R²`) to the buffer's first and second `q_len` octets.
-/

@[expose] public section

namespace VG.Proof.Dsa.RISCV64

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64
open VG.Impl.Bignum VG.Impl.Bignum.RISCV64 VG.Impl.Dsa.RISCV64 VG.Impl.Dsa.RISCV64.Verify
open VG.Proof.Bignum (slot Arrays)

/-- The borrow of `a − b`, for `a` and `b` below `2^63`. -/
theorem sub_shr63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a - BitVec.ofNat 64 b) >>> 63 = BitVec.ofNat 64 (if a < b then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  simp only [Nat.reducePow] at *
  split <;> omega_arith

/-- The registers `scalarLen` writes. -/
def scalarLenRegs : List Reg := [.s8, .t3, .a0]

/-- `scalarLen`: `s8 := min(d, qb)`, from the header's lengths. -/
theorem scalarLen_ok {s : State} {L : Lay} {qb d : Nat} (hs : ScrL s L) (hL : L.Ok) (h6 : s.gpr .s6 = L.S)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d) (h3 : qb < 2 ^ 16) (h4 : d < 2 ^ 16) :
    WP isa scalarLen s fun t =>
      (t.gpr .s8 = BitVec.ofNat 64 (min d qb) ∧ t.mem = s.mem) ∧ Keep scalarLenRegs s t := by
  obtain hp : L.pl < 2 ^ 16 := by rcases hL.pl with e | e | e <;> omega_arith
  obtain hq : L.ql < 2 ^ 16 := by rcases hL.ql with e | e | e <;> omega_arith
  unfold scalarLen
  refine WP.seq (WP.block_append (WP.block_append (WP.mono (getQb_ok hs hL h6 .s8) fun u ⟨⟨a8, mu⟩, ku⟩ =>
    WP.mono (getD_ok (hs.congr ku.2.2) hL (by rw [ku.gpr (by decide)]; exact h6) .t3)
      fun v ⟨⟨b3, mv⟩, kv⟩ => ?_)))
  rw [hlen, pack_qb hp hq h3 h4] at a8
  rw [mu, hlen, pack_d hp hq h3 h4] at b3
  obtain a8' : v.gpr .s8 = BitVec.ofNat 64 qb := (kv.gpr (by decide)).trans a8
  obtain hsub := sub_shr63 (a := qb) (b := d) (by omega_using [h3]) (by omega_using [h4])
  refine WP.mono (WP.keep [.a0] (Q := fun t => t.gpr .a0 = BitVec.ofNat 64 (if qb < d then 1 else 0) ∧
      t.mem = v.mem) (by brun [a8', b3, exec_shift_d (show 63 < 64 by decide), hsub]) (by decide) (by rfl))
    fun w ⟨⟨c0, mw⟩, kw⟩ => ?_
  obtain kuvw := (ku.trans kv).trans kw
  obtain m : w.mem = s.mem := by rw [mw, mv, mu]
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by split <;> decide) c0) (fun hz => ?_) (fun hz => ?_)
  · have hz : ¬ qb < d := by have := of_decide_eq_true hz; split at this <;> simp_all
    refine WP.mono (WP.keep [.s8] (Q := fun t => t.gpr .s8 = BitVec.ofNat 64 (min d qb) ∧ t.mem = w.mem)
      (by brun [(kw.gpr (r := .t3) (by decide)).trans b3, BitVec.add_zero]; rw [Nat.min_eq_left (by omega_using [hz])])
      (by decide) (by rfl)) fun t ⟨⟨t8, mt⟩, kt⟩ => ⟨⟨t8, by rw [mt, m]⟩, (kuvw.trans kt).mono (by decide)⟩
  · have hz : qb < d := by have := of_decide_eq_false hz; split at this <;> simp_all
    refine WP.block_nil ⟨⟨by rw [kw.gpr (by decide), a8', Nat.min_eq_right (by omega_using [hz])], m⟩,
      kuvw.mono (by decide)⟩

/-- The registers `scalar` writes. -/
def scalarRegs : List Reg := scalarLenRegs ++ [.s7] ++ loadRegs ++ [.s0, .t3, .t5]

/-- `scalar`: the digest's (at the header's `hDigest`) first `min(d, qb)`
octets into array 6. -/
theorem scalar_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d : Nat} (hL : L.Ok) (h : QS s L key sig)
    (hdg8 : word s.mem L.S hDigest = dig) (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d)
    (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16) (hdg : Src s L dig (min d qb)) :
    WP isa scalar s fun t =>
      (QS t L key sig ∧ arrQ t.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) ∧
        Outside L.Q (slot L.wq 6) (8 * (L.wq + 1)) s.mem t.mem) ∧ Keep scalarRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hql : L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [hwq]
  obtain e6 := Lay.slot_eq L.wq 6; have e7 := Lay.slot_eq L.wq 7; have e1 := Lay.slot_eq L.wq 1
  unfold scalar
  refine WP.seq (WP.mono (scalarLen_ok h.scr hL h.regs.s6 hlen (by omega_using [hqb, hwq]) hd) fun s₀ ⟨⟨a8, m0⟩, k0⟩ => ?_)
  obtain ⟨hin, hal⟩ := ScrL.hdr (h.scr.congr k0.2.2) hL (d := 8) (by decide) (by decide)
  refine WP.seq (WP.mono (WP.keep [.s7] (Q := fun u => u.gpr .s7 = dig ∧ u.mem = s₀.mem)
    (by brun [hDigest, (k0.gpr (r := .s6) (by decide)).trans h.regs.s6, hin, hal, m0]; exact hdg8)
    (by rfl) (by rfl))
    fun s₁ ⟨⟨a7, m1⟩, k1'⟩ => ?_)
  obtain a8 : s₁.gpr .s8 = BitVec.ofNat 64 (min d qb) := (k1'.gpr (by decide)).trans a8
  obtain k1 := k0.trans k1'
  obtain m1 : s₁.mem = s.mem := m1.trans m0
  obtain hdl : min d qb ≤ L.ql := Nat.le_trans (Nat.min_le_right _ _) hqb
  generalize min d qb = dl at a8 hdg hdl ⊢
  obtain Q1 := h.stepM k1 m1
  refine WP.ite _ (Steps.eval_zero_ofNat _ _ (by omega_using [hwq, hdl]) a8) (fun hz => ?_) (fun hz => ?_)
  · have hz : dl = 0 := of_decide_eq_true hz
    subst hz
    refine WP.mono (zeroArr_ok Q1.inq.env (j := 6) (by decide)) fun t ⟨⟨z6, ot⟩, kt⟩ => ?_
    refine ⟨⟨Q1.step kt (Body.ofQ hL ot (by omega_using [hwq, e6])), ?_, ?_⟩, (k1.trans kt).mono (by decide)⟩
    · rw [arrQ, z6]; rfl
    · rw [← m1]; exact ot.mono (Nat.le_refl _) (by omega_using [])
  · have hz : dl ≠ 0 := of_decide_eq_false hz
    refine WP.mono (loadQ_ok (j := 6) Q1 hL (by decide) (hdg.keep k1.2.1 k1.2.2) a7 a8 (by omega_using [hz])
      (by omega_using [hwq, hdl])) fun t ⟨⟨Qt, v6, _, ot⟩, kt⟩ => ?_
    rw [m1] at v6 ot
    exact ⟨⟨Qt, v6, ot⟩, (k1.trans kt).mono (by decide)⟩

/-! ## Montgomery multiplications in the Q space -/

/-- An array that `Arrays` does not list keeps its value. -/
theorem arrays_val {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m') {j : Nat}
    (hj : j < 28) (hjs : ∀ k ∈ js, k ≠ j) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) :
    wordsVal m' B (slot w j) w = wordsVal m B (slot w j) w :=
  wordsVal_congr fun i hi => h.word_eq (fun k hk => by
      have := VG.Proof.Bignum.slot_sep (w := w) (hjs k hk); omega_using [hi, this])
    (by have := slot_lt (w := w) hj; omega_using [hn, hi, this])

theorem arrays_word0 {B : Addr} {w : Nat} {js : List Nat} {m m' : Mem} (h : Arrays B w js m m')
    (hjs : ∀ k ∈ js, k ≠ 0) (hn : B.toNat + slot w 28 ≤ 2 ^ 64) :
    word m' B (slot w 0) = word m B (slot w 0) :=
  h.word_eq (fun k hk => by have := VG.Proof.Bignum.slot_sep (w := w) (hjs k hk); omega_using [this])
    (by have := slot_lt (w := w) (show 0 < 28 by decide); omega_using [hn, this])

theorem arrays_qarr {L : Lay} {js : List Nat} {m m' : Mem} (h : Arrays L.Q L.wq js m m')
    (hjs : ∀ k ∈ js, 1 ≤ k ∧ k < 28) : QArr L m m' := fun x hx => h x fun k hk => by
  obtain ⟨a, b⟩ := hjs k hk
  have := slot_mono (w := L.wq) a
  have := slot_lt (w := L.wq) b
  obtain e1 := Lay.slot_eq L.wq 1; have e28 := Lay.slot_eq L.wq 28
  simp only [VG.Proof.Bignum.ofs, ofs] at hx ⊢
  omega_arith

/-- `montOp o a b` in the Q space, for `o` among 5 and 6, `[b] < q`. -/
theorem qmont_ok {s : State} {L : Lay} {key sig : Addr} (hL : L.Ok) (h : QS s L key sig) (hi : QInv s L)
    {o a b : Nat} (ho : o = 5 ∨ o = 6) (ha : a < 8) (ha2 : a ≠ 2) (hb : b < 8) (hb2 : b ≠ 2)
    (hB : arrQ s.mem L b < arrQ s.mem L 0) :
    WP isa (PublicChecked.montOp o a b) s fun t =>
      (QS t L key sig ∧ QInv t L ∧ arrQ t.mem L o < arrQ s.mem L 0 ∧
        arrQ t.mem L o * 2 ^ (64 * L.wq) % arrQ s.mem L 0 = arrQ s.mem L a * arrQ s.mem L b % arrQ s.mem L 0 ∧
        (∀ j < 28, j ≠ 2 → j ≠ 3 → j ≠ o → arrQ t.mem L j = arrQ s.mem L j) ∧ QArr L s.mem t.mem) ∧
        Keep Pub.montRegs s t := by
  have e := h.inq.env
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain h8 := slot_lt (w := L.wq) (show 8 < 28 by decide)
  obtain hn : L.Q.toNat + slot L.wq 28 ≤ 2 ^ 64 := by have := e.hs.nowrap; omega_using [hqs, this]
  refine WP.mono (Pub.montOp_ok e.hs (by omega_using [ho]) ha hb (by omega_using [ho]) (by omega_using [ho]) ha2 hb2 e.w2 (by omega_using [hwq])
    (by omega_using [hqs, h8]) e.a7 e.s5 e.t0 hi hB) fun t ⟨⟨lt, eq, ar⟩, k⟩ => ?_
  obtain qa : QArr L s.mem t.mem := arrays_qarr ar (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [ho, hk])
  refine ⟨⟨h.step k (qa.body hL), ?_, lt, eq, fun j hj h2 h3 ho' => arrays_val ar hj (by
    intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [h2, h3, ho', hk]) hn, qa⟩, k⟩
  show ((word t.mem L.Q (slot L.wq 0)).toNat * (t.gpr .t1).toNat + 1) % 2 ^ 64 = 0
  rw [arrays_word0 ar (by intro k hk; simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega_using [ho, hk]) hn,
    k.gpr (by decide)]
  exact hi

/-- Two Montgomery multiplications, by `y` and by `R² mod q`: `x y mod q`. -/
theorem prod_mont_back {q R A B X Y : Nat} (hR : Nat.Coprime R q) (hB : B < q) (hA : A * R % q = X * Y % q)
    (hB' : B * R % q = A * (R * R % q) % q) : B = X * Y % q := by
  obtain e : B * R % q = X * Y * R % q := by
    rw [hB', Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, ← Nat.mod_mul_mod, hA,
      Nat.mod_mul_mod]
  have := VG.Proof.Bignum.mont_cancel hR e
  rw [Nat.mod_eq_of_lt hB] at this
  exact this

/-- Octets below a frame's range keep their values. -/
theorem prod_bytes_keep {B : Addr} {o n k : Nat} {m m' : Mem} (h : Outside B o n m m') (hk : k ≤ o)
    (hk' : k < 2 ^ 64) : Spec.Rsa.bytesAt m' B k = Spec.Rsa.bytesAt m B k := by
  simp only [Spec.Rsa.bytesAt]
  refine List.map_congr_left fun i hi => h _ (Or.inl ?_)
  obtain hi := List.mem_range.mp hi
  rw [show B + BitVec.ofNat 64 i = off B i from rfl, ofs_off0 B (by omega_arith)]
  omega_arith

/-- The registers `products` writes. -/
def prodRegs : List Reg :=
  scalarRegs ++ [.s7, .s8] ++ loadRegs ++ copyRegs ++ Pub.montRegs ++ [.s7, .t2, .s8] ++ storeRegs

/-- `products`: `u1 = z w mod q` and `u2 = r w mod q` to the buffer. -/
theorem products_ok {s : State} {L : Lay} {key sig dig : Addr} {qb d W : Nat} (hL : L.Ok) (h : QS s L key sig)
    (hi : QInv s L) (hsg : Src s L sig (2 * L.ql)) (hdg8 : word s.mem L.S hDigest = dig)
    (hlen : word s.mem L.S hLens = pack L.pl L.ql qb d) (hqb : qb ≤ L.ql) (hd : d < 2 ^ 16)
    (hdg : Src s L dig (min d qb))
    (hq2 : 2 ≤ arrQ s.mem L 0) (hqo : arrQ s.mem L 0 % 2 = 1) (hql : arrQ s.mem L 0 < 2 ^ (8 * L.ql))
    (h24 : arrQ s.mem L 24 = 2 ^ (128 * L.wq) % arrQ s.mem L 0) (h4 : arrQ s.mem L 4 = W)
    (hW : W < arrQ s.mem L 0) :
    WP isa products s fun t =>
      (QS t L key sig ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem L.Buf L.ql) =
          Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % arrQ s.mem L 0 ∧
        Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (off L.Buf 32) L.ql) = rOf s.mem L sig * W % arrQ s.mem L 0 ∧
        QBuf L s.mem t.mem) ∧ Keep prodRegs s t := by
  have hwq := hL.wq_ge
  have hqs := hL.qslot
  obtain hql' : 20 ≤ L.ql ∧ L.ql ≤ 32 := by rcases hL.ql with e | e | e <;> omega_using [e]
  obtain hpl : 128 ≤ L.pl := by rcases hL.pl with e | e | e <;> omega_using [e]
  obtain e : ∀ j, slot L.wq j = 256 + j * (8 * (L.wq + 2)) := fun _ => rfl
  obtain e0 := e 0; have e1 := e 1; have e4 := e 4; have e5 := e 5; have e6 := e 6; have e7 := e 7
  obtain e24 := e 24; have e25 := e 25; have e28 := e 28
  obtain hcop : Nat.Coprime (2 ^ (64 * L.wq)) (arrQ s.mem L 0) := VG.Proof.Bignum.coprime_pow2 hqo _
  obtain hRR := pow_two_mul L.wq
  generalize hq : arrQ s.mem L 0 = q at hq2 hqo hql h24 hW hcop ⊢
  generalize (2 : Nat) ^ (128 * L.wq) = R2 at h24 hRR
  unfold products
  -- The digest's scalar into array 6, r into array 5, `R² mod q` into array 1.
  refine WP.seq (WP.mono (scalar_ok hL h hdg8 hlen hqb hd hdg) fun s₁ ⟨⟨Q1, v6, o1⟩, k1⟩ => ?_)
  refine WP.seq (WP.mono (ptrR_ok Q1.scr hL Q1.regs) fun s₂ ⟨⟨a7, a8, m2⟩, k2⟩ => ?_)
  obtain Q2 := Q1.stepM k2 m2
  obtain k12 := k1.trans k2
  refine WP.seq (WP.mono (loadQ_ok (j := 5) Q2 hL (by decide)
      ((hsg.keep k12.2.1 k12.2.2).sub (o := 0) (k := L.ql) (by omega_using [])) (by rw [a7, off, BitVec.add_zero]) a8
      (by omega_using [hql']) (by omega_using [hwq])) fun s₃ ⟨⟨Q3, v5, _, o3⟩, k3⟩ => ?_)
  rw [m2] at v5 o3
  refine WP.seq (WP.mono (copy_ok Q3.inq.env (o := 1) (a := 24) (by decide) (by decide) (by decide))
    fun s₄ ⟨⟨c1, o4⟩, k4⟩ => ?_)
  obtain Q4 := Q3.step k4 (Body.ofQ hL o4 (by omega_using [hwq, e1]))
  obtain k14 := (k12.trans k3).trans k4
  -- The values in array 0, 1, 4, 5 and 6 and the inverse.
  obtain A0 : arrQ s₄.mem L 0 = q := by
    rw [arrQ, o4.wordsVal (by omega_using [e0, e1]) (by omega_arith), o3.wordsVal (by omega_using [e0, e5]) (by omega_arith),
      o1.wordsVal (by omega_using [e0, e6]) (by omega_arith)]; exact hq
  obtain A4 : arrQ s₄.mem L 4 = W := by
    rw [arrQ, o4.wordsVal (by omega_using [e1, e4]) (by omega_arith), o3.wordsVal (by omega_using [e4, e5]) (by omega_arith),
      o1.wordsVal (by omega_using [e4, e6]) (by omega_arith)]; exact h4
  obtain A6 : arrQ s₄.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) := by
    rw [arrQ, o4.wordsVal (by omega_using [e1, e6]) (by omega_arith), o3.wordsVal (by omega_using [e5, e6]) (by omega_arith)]; exact v6
  obtain A5 : arrQ s₄.mem L 5 = rOf s.mem L sig := by
    rw [arrQ, o4.wordsVal (by omega_using [e1, e5]) (by omega_arith)]
    refine v5.trans ?_
    rw [(hsg.sub (o := 0) (k := L.ql) (by omega_using [])).bytes (Body.ofQ hL o1 (by omega_using [hwq, e6])) (by have := hL.z256; omega_using [this])]
    simp only [rOf, off, BitVec.add_zero]
  obtain A1 : arrQ s₄.mem L 1 = R2 % q := by
    rw [arrQ, wordsVal_congr (m := s₃.mem) (d := slot L.wq 24) fun i hi => c1 i (by omega_using [hi])]
    rw [← h24, o3.wordsVal (by omega_using [e5, e24]) (by omega_arith), o1.wordsVal (by omega_using [e6, e24]) (by omega_arith)]
  obtain I4 : QInv s₄ L := by
    show ((word s₄.mem L.Q (slot L.wq 0)).toNat * (s₄.gpr .t1).toNat + 1) % 2 ^ 64 = 0
    rw [o4.word (by omega_using [e0, e1]) (by omega_arith), o3.word (by omega_using [e0, e5]) (by omega_arith),
      o1.word (by omega_using [e0, e6]) (by omega_arith), k14.gpr (by decide)]
    exact hi
  -- u1.
  refine WP.seq (WP.mono (qmont_ok hL Q4 I4 (o := 6) (a := 6) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [A4, A0]; exact hW)) fun s₅ ⟨⟨Q5, I5, _, e5, k5a, qa5⟩, k5⟩ => ?_)
  rw [A0, A6, A4] at e5
  obtain B0 := (k5a 0 (by decide) (by decide) (by decide) (by decide)).trans A0
  obtain B1 := (k5a 1 (by decide) (by decide) (by decide) (by decide)).trans A1
  obtain B4 := (k5a 4 (by decide) (by decide) (by decide) (by decide)).trans A4
  obtain B5 := (k5a 5 (by decide) (by decide) (by decide) (by decide)).trans A5
  refine WP.seq (WP.mono (qmont_ok hL Q5 I5 (o := 6) (a := 6) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B1, B0]; exact Nat.mod_lt _ (by omega_using [hq2])))
    fun s₆ ⟨⟨Q6, I6, l6, e6', k6a, qa6⟩, k6⟩ => ?_)
  rw [B0] at l6
  rw [B0, B1] at e6'
  obtain u1 : arrQ s₆.mem L 6 = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem dig (min d qb)) * W % q :=
    prod_mont_back hcop l6 e5 (by rw [e6', hRR])
  obtain C0 := (k6a 0 (by decide) (by decide) (by decide) (by decide)).trans B0
  obtain C1 := (k6a 1 (by decide) (by decide) (by decide) (by decide)).trans B1
  obtain C4 := (k6a 4 (by decide) (by decide) (by decide) (by decide)).trans B4
  obtain C5 := (k6a 5 (by decide) (by decide) (by decide) (by decide)).trans B5
  -- u2.
  refine WP.seq (WP.mono (qmont_ok hL Q6 I6 (o := 5) (a := 5) (b := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [C4, C0]; exact hW)) fun s₇ ⟨⟨Q7, I7, _, e7', k7a, qa7⟩, k7⟩ => ?_)
  rw [C0, C5, C4] at e7'
  obtain D0 := (k7a 0 (by decide) (by decide) (by decide) (by decide)).trans C0
  obtain D1 := (k7a 1 (by decide) (by decide) (by decide) (by decide)).trans C1
  obtain D6 := (k7a 6 (by decide) (by decide) (by decide) (by decide)).trans u1
  refine WP.seq (WP.mono (qmont_ok hL Q7 I7 (o := 5) (a := 5) (b := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [D1, D0]; exact Nat.mod_lt _ (by omega_using [hq2])))
    fun s₈ ⟨⟨Q8, _, l8, e8, k8a, qa8⟩, k8⟩ => ?_)
  rw [D0] at l8
  rw [D0, D1] at e8
  obtain u2 : arrQ s₈.mem L 5 = rOf s.mem L sig * W % q := prod_mont_back hcop l8 e7' (by rw [e8, hRR])
  obtain u1' := (k8a 6 (by decide) (by decide) (by decide) (by decide)).trans D6
  obtain k48 := ((k5.trans k6).trans k7).trans k8
  -- To the buffer.
  refine WP.seq (WP.mono (ptrBuf_ok Q8.scr hL Q8.regs) fun s₉ ⟨⟨b7, b8, m9⟩, k9⟩ => ?_)
  obtain e9 := Q8.inq.env.keep k9
  refine WP.seq (WP.mono (storeBE_ok (j := 6) (O := L.Buf) (k := L.ql) e9 (by decide)
    (by have := ScrL.bufSt (Q8.scr.congr k9.2.2) hL (o := 0) (k := L.ql) (by omega_using [hwq, hpl])
        simpa only [off, BitVec.add_zero] using this)
    (by have := buf_nowrap hL (o := 0) (k := L.ql) (by omega_using [hwq, hpl]) (by omega_using [hql']); simpa only [off, BitVec.add_zero] using this)
    b7 b8 (by omega_using [hql']) (by omega_using [hwq]) (m2_sep hL)) fun s₁₀ ⟨⟨vt, ot⟩, k10⟩ => ?_)
  rw [m9] at vt ot
  obtain qb10 : QBuf L s₈.mem s₁₀.mem := QBuf.ofBuf hL ot (by omega_using [hwq, hpl])
  obtain Q10 := Q8.step (k9.trans k10) (qb10.body hL)
  refine WP.seq (WP.mono (ptrBuf2_ok Q10.scr hL Q10.regs) fun s₁₁ ⟨⟨f7, f8, m11⟩, k11⟩ => ?_)
  obtain e11 := e9.keep (k10.trans k11)
  obtain hso : ∀ x, ofs (off L.Buf 32) x < L.ql → 1600 ≤ ofs L.Q x := by
    rw [buf_eq, off_off]
    exact sepQ_from L (by omega_using []) (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega_using [hwq])
  refine WP.mono (storeBE_ok (j := 5) (O := off L.Buf 32) (k := L.ql) e11 (by decide)
    (ScrL.bufSt (Q10.scr.congr k11.2.2) hL (o := 32) (k := L.ql) (by omega_using [hwq, hpl]))
    (buf_nowrap hL (o := 32) (k := L.ql) (by omega_using [hwq, hpl]) (by omega_using [hql'])) f7 f8 (by omega_using [hql']) (by omega_using [hwq]) hso)
    fun t ⟨⟨vt2, ot2⟩, kt⟩ => ?_
  rw [m11] at vt2 ot2
  obtain ot2b : Outside L.Buf (32 + 0) L.ql s₁₀.mem t.mem :=
    outside_shift ot2 (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega_using [hwq]) (by omega_using [])
  obtain qbt : QBuf L s₁₀.mem t.mem := QBuf.ofBuf hL (n := 64) (ot2b.mono (Nat.zero_le _) (by omega_using [hwq]))
    (by omega_using [hpl])
  obtain ot' : Outside (off L.Q 1600) 0 L.ql s₈.mem s₁₀.mem := by rw [← buf_eq]; exact ot
  obtain otq := outside_shift ot' (by have := hL.buf_end; have := hL.nowrap; simp only [Lay.bOff] at *; omega_using [hwq])
    (by decide)
  obtain u2' : arrQ s₁₀.mem L 5 = rOf s.mem L sig * W % q := by
    rw [arrQ, otq.wordsVal (Or.inl (by omega_arith)) (by omega_arith)]; exact u2
  obtain qa18 : QArr L s.mem s₈.mem := by
    obtain qa1 : QArr L s.mem s₁.mem := QArr.of o1 (by omega_using [e1, e6]) (by omega_using [e6, e28])
    obtain qa3 : QArr L s₁.mem s₃.mem := QArr.of o3 (by omega_arith) (by omega_arith)
    obtain qa4 : QArr L s₃.mem s₄.mem := QArr.of o4 (by omega_using []) (by omega_using [e1, e28])
    exact ((((((qa1.trans qa3).trans qa4).trans qa5).trans qa6).trans qa7).trans qa8)
  obtain kall := (((k14.trans k48).trans (k9.trans k10)).trans k11).trans kt
  refine ⟨⟨Q10.step (k11.trans kt) (qbt.body hL), ?_, ?_, (qa18.qbuf hL).trans (qb10.trans qbt)⟩,
    kall.mono (by decide)⟩
  · rw [prod_bytes_keep ot2b (by omega_using [hwq]) (by omega_using [hwq])]
    refine (vt.trans (read_low _ _ (w := L.wq) (by omega_using [hwq]) ?_)).trans u1'
    show arrQ s₈.mem L 6 < _
    rw [u1']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [hq2])) hql
  · refine (vt2.trans (read_low _ _ (w := L.wq) (by omega_using [hwq]) ?_)).trans u2'
    show arrQ s₁₀.mem L 5 < _
    rw [u2']
    exact Nat.lt_trans (Nat.mod_lt _ (by omega_using [hq2])) hql

end VG.Proof.Dsa.RISCV64
