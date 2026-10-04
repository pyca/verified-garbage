import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha512.Shifts
import VerifiedGarbage.Impl.Sha512.X86

/-!
# SHA-512 on x86 (32-bit) with SSE2: a round and two steps of the message schedule

A round's 64-bit words are the low quadwords of XMM registers (`qword · 0`);
the message schedule computes two words at a time, one in each quadword. A
round (`roundW`) and a pair of steps of the message schedule (`scheduleW`)
are each run once, symbolically, for any offsets, constant and registers in
each role; what they compute is stated with `split6` and `chain5` (the shifts
of `Σ` and `σ`, `Proof/Sha512/Shifts.lean`).
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_ ldq stq ldo sto xb xs X Y sig5 bigSig roundW scheduleW)

/-! ## Instructions on quadwords -/

theorem qword_append_0 (h l : BitVec 64) : qword (h ++ l) 0 = l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_zero, Nat.zero_add,
    decide_true, Bool.true_and, hi', ite_true]

theorem qword_append_1 (h l : BitVec 64) : qword (h ++ l) 1 = h := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi'
  simp only [qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, Nat.mul_one, hi', decide_true,
    Bool.true_and, show ¬64 + i < 64 by omega, ite_false, Nat.add_sub_cancel_left]

theorem q_psrlq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psrlq a n) 0 = if 63 < n.toNat then 0 else qword a 0 >>> n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [qword_append_0]

theorem q_psllq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psllq a n) 0 = if 63 < n.toNat then 0 else qword a 0 <<< n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [qword_append_0]

theorem q1_psrlq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psrlq a n) 1 = if 63 < n.toNat then 0 else qword a 1 >>> n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [qword_append_1]

theorem q1_psllq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psllq a n) 1 = if 63 < n.toNat then 0 else qword a 1 <<< n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [qword_append_1]

theorem q_pxor (a b : BitVec 128) : qword (XBinOp.eval .pxor a b) 0 = qword a 0 ^^^ qword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hi, decide_true,
    Bool.true_and]

theorem q1_pxor (a b : BitVec 128) : qword (XBinOp.eval .pxor a b) 1 = qword a 1 ^^^ qword b 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hi, decide_true,
    Bool.true_and]

theorem q_pand (a b : BitVec 128) : qword (XBinOp.eval .pand a b) 0 = qword a 0 &&& qword b 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, hi, decide_true,
    Bool.true_and]

theorem q_paddq (a b : BitVec 128) : qword (XBinOp.eval .paddq a b) 0 = qword a 0 + qword b 0 := by
  simp only [XBinOp.eval, qword_append_0]

theorem q1_paddq (a b : BitVec 128) : qword (XBinOp.eval .paddq a b) 1 = qword a 1 + qword b 1 := by
  simp only [XBinOp.eval, qword_append_1]

/-- `paddq`, as the two quadwords. -/
theorem eval_paddq (a b : BitVec 128) :
    XBinOp.eval .paddq a b = (qword a 1 + qword b 1) ++ (qword a 0 + qword b 0) := rfl

/-- `movd` of each half, then `punpckldq`: the halves together. -/
theorem q_punpckldq_movd (l h : BitVec 32) :
    qword (XBinOp.eval .punpckldq ((0 : BitVec 96) ++ l) ((0 : BitVec 96) ++ h)) 0 = h ++ l := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [XBinOp.eval, ofDwords, dword, qword, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append, hi,
    decide_true, Bool.true_and, Nat.mul_zero, Nat.zero_add, Nat.mul_one]
  by_cases h1 : i < 32
  · simp only [h1, ite_true, decide_true, Bool.true_and]
  · simp only [h1, ite_false, show i - 32 < 32 by omega, ite_true, decide_true, Bool.true_and]

theorem extractLsb'_qword (x : BitVec 128) : x.extractLsb' 0 64 = qword x 0 := rfl

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## 16-byte memory accesses as two quadwords -/

theorem qword_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 2) :
    qword (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (8 * j)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega), getLsbD_read _ _ (by omega)]
  rw [show a + BitVec.ofNat 64 ((64 * j + i) / 8) = a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (64 * j + i) / 8 = 8 * j + i / 8 by omega, BitVec.ofNat_add, BitVec.add_assoc]]
  rw [decide_eq_true (by omega), Bool.true_and]; exact congrArg _ (by omega)

theorem readW_writeW128_q (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * j)) 64 = qword v j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega)]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (8 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  simp only [show 8 * j + i / 8 < 128 / 8 by omega, ite_true, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega), decide_eq_true (by omega), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega)

/-! ## A round -/

/-- `U = h + k + w + Ch(e, f, g)`, as `roundW` computes it before `Σ₁(e)`. -/
def uOf (vh k vw ve vf vg : BitVec 64) : BitVec 64 :=
  vh + k + vw + ((vf ^^^ vg) &&& ve ^^^ vg)

theorem roundW_ok (a b d e f g h w : Nat) (k : BitVec 64) (A E BC T NE AB : XReg)
    (hn : [A, E, BC, T, NE, AB, X, Y].Nodup) (s : State)
    (ib : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) b) 8)
    (id : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) d) 8)
    (if_ : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) f) 8)
    (ig : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) g) 8)
    (ih : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) h) 8)
    (iw : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) w) 8)
    (oa : InRegions s.wr (addr (s.gpr .esi) a) 8) (oe : InRegions s.wr (addr (s.gpr .esi) e) 8)
    (eb : ∀ v : BitVec 64, (s.mem.writeW (addr (s.gpr .esi) e) v).readW (addr (s.gpr .esi) b) 64 =
      s.mem.readW (addr (s.gpr .esi) b) 64)
    (ed : ∀ v : BitVec 64, (s.mem.writeW (addr (s.gpr .esi) e) v).readW (addr (s.gpr .esi) d) 64 =
      s.mem.readW (addr (s.gpr .esi) d) 64) :
    WP isa (.block (roundW a b d e f g h w k A E BC T NE AB)) s fun s' =>
      let m o := s.mem.readW (addr (s.gpr .esi) o) 64
      let va := qword (s.xmm A) 0
      let ve := qword (s.xmm E) 0
      let u := uOf (m h) (Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k) (m w) ve (m f) (m g)
      let s1 := split6 ve 14 4 23 23 23 4
      qword (s'.xmm T) 0 =
        u + s1 + (qword (s.xmm BC) 0 &&& (va ^^^ m b) ^^^ m b) + split6 va 28 6 5 25 5 6 ∧
      qword (s'.xmm NE) 0 = m d + u + s1 ∧ qword (s'.xmm AB) 0 = va ^^^ m b ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (addr (s.gpr .esi) e) ve).writeW (addr (s.gpr .esi) a) va ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [roundW, bigSig, ldq, stq, xb, xs, X, Y, List.cons_append, List.nil_append] at hn hn' ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hn hn'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, readSrc, isa,
    State.load64, State.store64, ea_at, extractLsb'_qword, eval_movdqa,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.xmm_setReg, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, not_false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left',
    hn, hn', ib, id, if_, ig, ih, iw, oa, oe, eb, ed, q_psrlq, q_psllq, q_pxor, q_pand, q_paddq,
    q_punpckldq_movd, qword_append_0, BitVec.reduceToNat, Nat.reduceLT]
  refine ⟨rfl, rfl, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [hr, ↓reduceIte]

/-! ## Two steps of the message schedule -/

/-- `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆`, as `scheduleW` computes it in each quadword. -/
def schedOf (x2 x7 x15 x16 : BitVec 64) : BitVec 64 :=
  chain5 x2 6 3 13 42 42 + x7 + chain5 x15 1 56 6 7 1 + x16

theorem scheduleW_ok (o2 o7 o15 o16 : Nat) (P Q : XReg) (hn : [P, Q, X, Y].Nodup) (s : State)
    (i2 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o2) 16)
    (i7 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o7) 16)
    (i15 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o15) 16)
    (i16 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o16) 16)
    (w16 : InRegions s.wr (addr (s.gpr .esi) o16) 16) :
    WP isa (.block (scheduleW o2 o7 o15 o16 P Q)) s fun s' =>
      let m o j := qword (s.mem.readW (addr (s.gpr .esi) o) 128) j
      let v := schedOf (m o2 1) (m o7 1) (m o15 1) (m o16 1) ++ schedOf (m o2 0) (m o7 0) (m o15 0) (m o16 0)
      (∀ r, r ≠ P → r ≠ Q → r ≠ X → r ≠ Y → s'.xmm r = s.xmm r) ∧ s'.xmm P = v ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (addr (s.gpr .esi) o16) v ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [scheduleW, sig5, ldo, sto, xb, xs, X, Y, List.cons_append, List.nil_append] at hn hn' ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hn hn'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa,
    State.load128, State.store128, ea_at, eval_movdqa, eval_paddq,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left',
    hn, hn', i2, i7, i15, i16, w16, q_psrlq, q_psllq, q_pxor, q1_psrlq, q1_psllq, q1_pxor,
    qword_append_0, qword_append_1, BitVec.reduceToNat, Nat.reduceLT]
  refine ⟨fun r h1 h2 h3 h4 => ?_, rfl, trivial, rfl, trivial, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h1, h2, h3, h4, not_false_eq_true]

end VG.Proof.Sha512.X86
