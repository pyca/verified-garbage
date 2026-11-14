module

public import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Sha512.Shifts
public import VerifiedGarbage.Impl.Sha512.X86
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.X86.Reduce
public import VerifiedGarbage.Proof.Sha512.X86.Rounds
import VerifiedGarbage.Proof.Sha512.Spec

/-! ### `Sha512.X86.Sse`, which only this module used -/

section

/-!
# SHA-512 on x86 (32-bit) with SSE2: a round and two steps of the message schedule

A round's 64-bit words are the low quadwords of XMM registers (`qword · 0`);
the message schedule computes two words at a time, one in each quadword. A
round (`roundW`) and a pair of steps of the message schedule (`scheduleW`)
are each run once, symbolically, for any offsets, constant and registers in
each role; what they compute is stated with `split6` and `chain5` (the shifts
of `Σ` and `σ`, `Proof/Sha512/Shifts.lean`).
-/

@[expose] public section

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
    Bool.true_and, show ¬64 + i < 64 by omega_using [], ite_false, Nat.add_sub_cancel_left]

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
  · simp only [h1, ite_false, show i - 32 < 32 by omega_using [hi], ite_true, decide_true, Bool.true_and]

theorem extractLsb'_qword (x : BitVec 128) : x.extractLsb' 0 64 = qword x 0 := rfl

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

/-! ## 16-byte memory accesses as two quadwords -/

theorem qword_readW (m : Mem) (a : Addr) {j : Nat} (hj : j < 2) :
    qword (m.readW a 128) j = m.readW (a + BitVec.ofNat 64 (8 * j)) 64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hj, hi]), getLsbD_read _ _ (by omega_using [hi])]
  rw [show a + BitVec.ofNat 64 ((64 * j + i) / 8) = a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (i / 8) by
    rw [show (64 * j + i) / 8 = 8 * j + i / 8 by omega_using [], BitVec.ofNat_add, BitVec.add_assoc]]
  rw [decide_eq_true (by omega_using [hj, hi]), Bool.true_and]; exact congrArg _ (by omega_using [])

theorem readW_writeW128_q (m : Mem) (a : Addr) (v : BitVec 128) {j : Nat} (hj : j < 2) :
    (m.writeW a v).readW (a + BitVec.ofNat 64 (8 * j)) 64 = qword v j := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [qword, BitVec.getLsbD_extractLsb', Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ (by omega_using [hi])]
  simp only [Mem.writeW, Mem.write]
  rw [show a + BitVec.ofNat 64 (8 * j) + BitVec.ofNat 64 (i / 8) - a = BitVec.ofNat 64 (8 * j + i / 8) by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, Offset.add_sub_cancel_left]]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hj, hi])]
  simp only [show 8 * j + i / 8 < 128 / 8 by omega_using [hj, hi], ite_true, BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  rw [decide_eq_true (by omega_using []), decide_eq_true (by omega_using [hj, hi]), Bool.true_and, Bool.true_and]
  exact congrArg _ (by omega_using [])

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
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, readSrc, isa,
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
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, XOp.exec, isa,
    State.load128, State.store128, ea_at, eval_movdqa, eval_paddq,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left',
    hn, hn', i2, i7, i15, i16, w16, q_psrlq, q_psllq, q_pxor, q1_psrlq, q1_psllq, q1_pxor,
    qword_append_0, qword_append_1, BitVec.reduceToNat, Nat.reduceLT]
  refine ⟨fun r h1 h2 h3 h4 => ?_, rfl, trivial, rfl, trivial, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h1, h2, h3, h4, not_false_eq_true]

end VG.Proof.Sha512.X86

end

end

/-!
# SHA-512 on x86 (32-bit) with SSE2: the rounds

The invariant of the rounds (`RInv`): the working variables but `a` and `e`
in their slots, `a`, `e` and `b ⊕ c` in the registers of their roles, and the
message-schedule window, with the copy of its word `Wⱼ`, `j mod 16 = 0`.
`round_ok` and `schedule_ok` instantiate the symbolic runs of `Sse.lean` for
round `t` and for the words `Wₜ`, `Wₜ₊₁`.
-/

@[expose] public section

namespace VG.Proof.Sha512.X86

open VG VG.X86 VG.Impl.Sha512.X86
open VG.Spec.Sha512 (HashValue Word Block W K)
open VG.Proof.Sha256.X86.Stream (contains_addr addr_sep)
open VG.Proof.Sha512.Word64 (hi_append_lo)

/-! ## Memory -/

theorem readW64_write_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (v : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    (m.writeW (addr b o) v).readW (addr b o') 64 = m.readW (addr b o') 64 :=
  Mem.readW_writeW_sep (addr_sep h' h hs.symm) (by decide)

/-- A 64-bit read, after a 16-byte write elsewhere. -/
theorem readW64_write128_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (v : BitVec 128)
    (h : b.toNat + o + 16 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 16 ≤ o' ∨ o' + 8 ≤ o) :
    (m.writeW (addr b o) v).readW (addr b o') 64 = m.readW (addr b o') 64 :=
  Mem.readW_writeW_sep (addr_sep h' h hs.symm) (by decide)

/-- `addr b o + 8 = addr b (o + 8)` within the address space. -/
theorem addr_add8 {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 < 2 ^ 32) :
    addr b o + BitVec.ofNat 64 (8 * 1) = addr b (o + 8) := by
  rw [addr_eq (by omega_using [h]), addr_eq (by omega_using [h]), Offset.add_ofNat_add_ofNat]

theorem addr_add0 (b : BitVec 32) (o : Nat) : addr b o + BitVec.ofNat 64 (8 * 0) = addr b o :=
  BitVec.add_zero _

/-- The two quadwords of a 16-byte read. -/
theorem qword_readW_0 (m : Mem) (b : BitVec 32) (o : Nat) :
    qword (m.readW (addr b o) 128) 0 = m.readW (addr b o) 64 := by
  rw [qword_readW _ _ (by decide), addr_add0]

theorem qword_readW_1 (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 < 2 ^ 32) :
    qword (m.readW (addr b o) 128) 1 = m.readW (addr b (o + 8)) 64 := by
  rw [qword_readW _ _ (by decide), addr_add8 h]

/-- `rd64`, the word as two halves, is the 64-bit word. -/
theorem rd64_eq_readW (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 ≤ 2 ^ 32) :
    rd64 m b o = m.readW (addr b o) 64 := by
  rw [rd64, Word64.readW64, addr_eq (x := b) (k := o + 4) (by omega_using [h]), addr_eq (x := b) (k := o) (by omega_using [h]),
    ← Offset.add_ofNat_add_ofNat]
  rfl

/-! ## Offsets and registers -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega_using []

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega_using []

/-- Two words from `wOff j`, the second the next slot or the copy after the window. -/
theorem wOff_pair (j : Nat) : wOff j + 16 ≤ 200 := by simp only [wOff]; omega_using []

theorem vw_sep (t k j : Nat) : vOff t k + 8 ≤ wOff j := by simp only [vOff, wOff]; omega_using []

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega_using [hi, hj, h]

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega_using [h]

theorem wOff_next {j : Nat} (h : j % 16 ≠ 15) : wOff j + 8 = wOff (j + 1) := by simp only [wOff]; omega_using [h]

theorem wOff_last {j : Nat} (h : j % 16 = 15) : wOff j + 8 = mirOff := by simp only [wOff, mirOff]; omega_using [h]

theorem xr_mod (t k : Nat) : xr t k = xr (t % 2) k := by simp only [xr, Nat.mod_mod]

theorem xr_nodup (t : Nat) : [xr t 0, xr t 1, xr t 2, xr t 3, xr t 4, xr t 5, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 0, xr p 1, xr p 2, xr p 3, xr p 4, xr p 5, X, Y].Nodup := by decide
  simp only [xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_nodup_sched (t : Nat) : [xr t 3, xr t 4, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 3, xr p 4, X, Y].Nodup := by decide
  simp only [xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_succ (t k : Nat) (hk : k < 3) : xr (t + 1) k = xr t (k + 3) := by
  have key : ∀ p < 2, ∀ k < 3, xr (p + 1) k = xr p (k + 3) := by decide
  rw [xr_mod t, xr_mod (t + 1), show (t + 1) % 2 = (t % 2 + 1) % 2 by omega_using [], ← xr_mod]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-- The registers of roles 0–2 are none of the schedule's temporaries. -/
theorem xr_sched_ne (t k : Nat) (hk : k < 3) :
    xr t k ≠ xr t 3 ∧ xr t k ≠ xr t 4 ∧ xr t k ≠ X ∧ xr t k ≠ Y := by
  have key : ∀ p < 2, ∀ k < 3, xr p k ≠ xr p 3 ∧ xr p k ≠ xr p 4 ∧ xr p k ≠ X ∧ xr p k ≠ Y := by decide
  rw [xr_mod t k, xr_mod t 3, xr_mod t 4]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-! ## The invariant -/

/-- The part of the scratch region the rounds write. -/
abbrev workR (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 200⟩

/-- Where the scratch buffer is: at `scr` (in `esi`), writable. -/
structure Ctx (scr : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = scr
  fit : scr.toNat + 224 ≤ 2 ^ 32
  mem : ⟨scr.setWidth 64, 224⟩ ∈ s.wr

theorem Ctx.out {scr : BitVec 32} {s : State} (c : Ctx scr s) {o n : Nat} (ho : o + n ≤ 224) (hn : 0 < n) :
    InRegions s.wr (addr (s.gpr .esi) o) n :=
  ⟨_, c.mem, by rw [c.esi]; exact contains_addr ho hn c.fit⟩

theorem Ctx.inp {scr : BitVec 32} {s : State} (c : Ctx scr s) {o n : Nat} (ho : o + n ≤ 224) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o) n :=
  mem_rd (c.out ho hn)

/-- What holds between rounds, before round `t`, from `s₀`, with the
message-schedule window holding the words `Wⱼ` for `u - 16 ≤ j < max u 16`. -/
structure RInv (scr : BitVec 32) (H : HashValue) (M : Block) (s₀ : State) (u t : Nat) (s : State) :
    Prop where
  vars : ∀ k (hk : k < 8), k ≠ 0 → k ≠ 4 → s.mem.readW (addr scr (vOff t k)) 64 = (Spec.Sha512.rounds H M t)[k]
  xa : qword (s.xmm (xr t 0)) 0 = (Spec.Sha512.rounds H M t)[0]
  xe : qword (s.xmm (xr t 1)) 0 = (Spec.Sha512.rounds H M t)[4]
  xbc : qword (s.xmm (xr t 2)) 0 = (Spec.Sha512.rounds H M t)[1] ^^^ (Spec.Sha512.rounds H M t)[2]
  win : ∀ j, j < max u 16 → u ≤ j + 16 → s.mem.readW (addr scr (wOff j)) 64 = W M j
  mir : ∀ j, j < max u 16 → u ≤ j + 16 → j % 16 = 0 → s.mem.readW (addr scr mirOff) 64 = W M j
  gpr : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [workR scr] s₀.mem s.mem

theorem Ctx.of_rinv {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : Ctx scr s₀) (hI : RInv scr H M s₀ u t s) : Ctx scr s :=
  ⟨(hI.gpr _ (by decide) (by decide) (by decide)).trans c.esi, c.fit, hI.wr ▸ c.mem⟩

/-- Every window of at most the first 16 words is all of them. -/
theorem RInv.early {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u u' t : Nat}
    (hI : RInv scr H M s₀ u t s) (hu : u ≤ 16) (hu' : u' ≤ 16) : RInv scr H M s₀ u' t s :=
  { hI with
    win := fun j hj _ => hI.win j (by omega_using [hu', hj]) (by omega_using [hu])
    mir := fun j hj _ h0 => hI.mir j (by omega_using [hu', hj]) (by omega_using [hu]) h0 }

theorem frame_writeW {scr : BitVec 32} {m m' : Mem} (h : Frame [workR scr] m m') (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    {o : Nat} (ho : o + 8 ≤ 200) (v : BitVec 64) : Frame [workR scr] m (m'.writeW (addr scr o) v) :=
  h.writeW (by simp) v (contains_addr ho (by decide) (by omega_using [hfit]))

theorem frame_writeW16 {scr : BitVec 32} {m m' : Mem} (h : Frame [workR scr] m m') (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    {o : Nat} (ho : o + 16 ≤ 200) (v : BitVec 128) : Frame [workR scr] m (m'.writeW (addr scr o) v) :=
  h.writeW (by simp) v (contains_addr ho (by decide) (by omega_using [hfit]))

/-! ## A round -/

theorem round_word (v : HashValue) (k w : Word) :
    uOf v[7] (Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k) w v[4] v[5] v[6] + split6 v[4] 14 4 23 23 23 4 =
      v[7] + Spec.Sha512.bsig1 v[4] + Spec.Sha512.ch v[4] v[5] v[6] + k + w := by
  rw [uOf, show Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k = k from hi_append_lo k, bsig1_split,
    ← ch_eq]
  simp only [BitVec.add_assoc, BitVec.add_comm, add_left_comm]

theorem round_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ u t s) (ht : t < max u 16) (hu : u ≤ t + 16) :
    WP isa (.block (round t)) s (RInv scr H M s₀ u (t + 1)) := by
  let v := Spec.Sha512.rounds H M t
  try rewrite [show Spec.Sha512.rounds H M t = v from rfl] at *
  have hv : v = Spec.Sha512.rounds H M t := rfl
  have hw : s.mem.readW (addr scr (wOff t)) 64 = W M t := hI.win t ht hu
  have fit := c.fit
  have vl := vOff_lt t
  have e14 := vOff_sep t (i := 1) (j := 4) (by decide) (by decide) (by decide)
  have e34 := vOff_sep t (i := 3) (j := 4) (by decide) (by decide) (by decide)
  have rb : ∀ (o : Nat) (x : BitVec 64), o + 8 ≤ 64 → (vOff t 4 + 8 ≤ o ∨ o + 8 ≤ vOff t 4) →
      (s.mem.writeW (addr (s.gpr .esi) (vOff t 4)) x).readW (addr (s.gpr .esi) o) 64 =
        s.mem.readW (addr (s.gpr .esi) o) 64 := fun o x ho h => by
    rw [c.esi]; exact readW64_write_ne _ _ (by have := vl 4; omega_using [fit, this]) (by omega_using [fit, ho]) h
  refine WP.mono (roundW_ok _ _ _ _ _ _ _ _ (K t) _ _ _ _ _ _ (xr_nodup t) s
    (c.inp (by have := vl 1; omega_using [this]) (by decide)) (c.inp (by have := vl 3; omega_using [this]) (by decide))
    (c.inp (by have := vl 5; omega_using [this]) (by decide)) (c.inp (by have := vl 6; omega_using [this]) (by decide))
    (c.inp (by have := vl 7; omega_using [this]) (by decide)) (c.inp (by have := wOff_lt t; omega_using [this]) (by decide))
    (c.out (by have := vl 0; omega_using [this]) (by decide)) (c.out (by have := vl 4; omega_using [this]) (by decide))
    (fun x => rb _ x (vl 1) e14.symm) (fun x => rb _ x (vl 3) e34.symm)) fun s' h => ?_
  obtain ⟨hT, hNE, hAB, hg, hm, hrd, hwr⟩ := h
  have h1 := hI.vars 1 (by decide) (by decide) (by decide)
  have h3 := hI.vars 3 (by decide) (by decide) (by decide)
  have h5 := hI.vars 5 (by decide) (by decide) (by decide)
  have h6 := hI.vars 6 (by decide) (by decide) (by decide)
  have h7 := hI.vars 7 (by decide) (by decide) (by decide)
  simp only [c.esi, h1, h3, h5, h6, h7, hw, hI.xa, hI.xe, hI.xbc] at hT hNE hAB hm
  have hnext : Spec.Sha512.rounds H M (t + 1) = roundKW v (K t) (W M t) := by
    rw [rounds_succ, round_eq]
  have e04 := vOff_sep t (i := 0) (j := 4) (by decide) (by decide) (by decide)
  -- The new memory, at the offsets of the working variables and the window.
  have rm : ∀ o, o + 8 ≤ 200 → (vOff t 0 + 8 ≤ o ∨ o + 8 ≤ vOff t 0) →
      (vOff t 4 + 8 ≤ o ∨ o + 8 ≤ vOff t 4) → s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 :=
    fun o ho h0 h4 => by
      rw [hm, readW64_write_ne _ _ (by have := vl 0; omega_using [fit, this]) (by omega_using [fit, ho]) h0,
        readW64_write_ne _ _ (by have := vl 4; omega_using [fit, this]) (by omega_using [fit, ho]) h4]
  have mv : ∀ k, vOff t k + 8 ≤ mirOff := fun k => by have := vw_sep t k 0; simp only [wOff, mirOff] at *; omega_using [this]
  refine ⟨fun k hk h0 h4 => ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun j hj hj' h0 => ?_,
    fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [hnext]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega_using [h0]⟩
    rw [vOff_succ t i (by omega_using [hk])]
    by_cases hi0 : i = 0
    · subst hi0
      rw [hm, Mem.readW_writeW_self64]
      rfl
    by_cases hi4 : i = 4
    · subst hi4
      rw [hm, Mem.readW_writeW_sep (addr_sep (by have := vl 4; omega_using [fit, this]) (by have := vl 0; omega_using [fit, this]) e04.symm)
        (by decide), Mem.readW_writeW_self64]
      rfl
    · rw [rm _ (by have := vl i; omega_using [this]) (vOff_sep t (by decide) (by omega_using [hk]) (Ne.symm hi0))
        (vOff_sep t (by decide) (by omega_using [hk]) (Ne.symm hi4)), hI.vars i (by omega_using [hk]) hi0 hi4]
      rcases (by omega_using [hk, h4, hi0, hi4] : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl <;> rfl
  · rw [xr_succ t 0 (by decide), hT, hnext, roundKW_0, round_word, bsig0_split, BitVec.and_comm,
      maj_xor]
    simp only [hv, BitVec.add_assoc]
    rw [BitVec.add_comm (Spec.Sha512.maj _ _ _)]
  · rw [xr_succ t 1 (by decide), hNE, hnext, roundKW_4, BitVec.add_assoc, round_word]
  · rw [xr_succ t 2 (by decide), hAB, hnext, roundKW_1, roundKW_2]
  · rw [rm _ (by have := wOff_lt j; omega_using [this]) (.inl (vw_sep t 0 j)) (.inl (vw_sep t 4 j))]
    exact hI.win j hj hj'
  · rw [rm _ (by decide) (.inl (mv 0)) (.inl (mv 4))]
    exact hI.mir j hj hj' h0
  · rw [hg r h1, hI.gpr r h1 h2 h3]
  · rw [hrd, hI.rd]
  · rw [hwr, hI.wr]
  · rw [hm]
    exact frame_writeW (frame_writeW hI.frame fit (by have := vl 4; omega_using [this]) _) fit
      (by have := vl 0; omega_using [this]) _

/-! ## Two steps of the message schedule -/

/-- The words at `wOff j` and the next slot, `Wⱼ` and `Wⱼ₊₁`, both in the window. -/
theorem pair_words {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ u t s) {j : Nat} (hj : j + 1 < max u 16) (hj' : u ≤ j + 16) :
    qword (s.mem.readW (addr scr (wOff j)) 128) 0 = W M j ∧
      qword (s.mem.readW (addr scr (wOff j)) 128) 1 = W M (j + 1) := by
  have fit := c.fit
  refine ⟨by rw [qword_readW_0]; exact hI.win j (by omega_using [hj]) hj', ?_⟩
  rw [qword_readW_1 _ (by have := wOff_pair j; omega_using [fit, this])]
  by_cases h15 : j % 16 = 15
  · rw [wOff_last h15]; exact hI.mir (j + 1) hj (by omega_using [hj']) (by omega_using [h15])
  · rw [wOff_next h15]; exact hI.win (j + 1) hj (by omega_using [hj'])

theorem schedule_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : Ctx scr s) (hI : RInv scr H M s₀ t t s) (h16 : 16 ≤ t) (hev : t % 2 = 0) :
    WP isa (.block (schedule t)) s (RInv scr H M s₀ (t + 2) t) := by
  have fit := c.fit
  have w' : ∀ j, wOff j + 16 ≤ 224 := fun j => by have := wOff_pair j; omega_using [this]
  rw [schedule, WP.block_append_iff]
  refine WP.mono (scheduleW_ok _ _ _ _ _ _ (xr_nodup_sched t) s (c.inp (w' _) (by decide))
    (c.inp (w' _) (by decide)) (c.inp (w' _) (by decide)) (c.inp (w' _) (by decide))
    (c.out (w' _) (by decide))) fun s' ⟨hx, hP, hg, hm, hrd, hwr⟩ => ?_
  simp only [c.esi] at hm hP
  -- The four pairs of words it reads.
  have p : ∀ i, 1 ≤ i → i ≤ 16 → i ≠ 1 →
      qword (s.mem.readW (addr scr (wOff (t + 16 - i))) 128) 0 = W M (t - i) ∧
      qword (s.mem.readW (addr scr (wOff (t + 16 - i))) 128) 1 = W M (t - i + 1) := fun i hi hi' h1 => by
    rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega_using [h16, hi']]
    exact pair_words c hI (by omega_using [hi, h1]) (by omega_using [hi'])
  obtain ⟨a2, b2⟩ := p 2 (by omega_using []) (by omega_using []) (by omega_using [])
  obtain ⟨a7, b7⟩ := p 7 (by omega_using []) (by omega_using []) (by omega_using [])
  obtain ⟨a15, b15⟩ := p 15 (by omega_using []) (by omega_using []) (by omega_using [])
  obtain ⟨a16, b16⟩ := p 16 (by omega_using []) (by omega_using []) (by omega_using [])
  rw [show t + 16 - 2 = t + 14 by omega_using []] at a2 b2
  rw [show t + 16 - 7 = t + 9 by omega_using []] at a7 b7
  rw [show t + 16 - 15 = t + 1 by omega_using []] at a15 b15
  rw [show t + 16 - 16 = t by omega_using []] at a16 b16
  have W0 : W M t = schedOf (W M (t - 2)) (W M (t - 7)) (W M (t - 15)) (W M (t - 16)) := by
    rw [schedOf, ssig1_chain, ssig0_chain, ← W_ge M h16]
  have W1 : W M (t + 1) =
      schedOf (W M (t - 2 + 1)) (W M (t - 7 + 1)) (W M (t - 15 + 1)) (W M (t - 16 + 1)) := by
    rw [schedOf, ssig1_chain, ssig0_chain, show t - 2 + 1 = t + 1 - 2 by omega_using [h16],
      show t - 7 + 1 = t + 1 - 7 by omega_using [h16], show t - 15 + 1 = t + 1 - 15 by omega_using [h16],
      show t - 16 + 1 = t + 1 - 16 by omega_using [h16], ← W_ge M (by omega_using [h16])]
  rw [a2, b2, a7, b7, a15, b15, a16, b16, ← W0, ← W1] at hm hP
  have tl : t % 16 ≠ 15 := by omega_using [hev]
  -- The memory after the 16-byte store, and the copy of `Wₜ`.
  have rm : ∀ o, o + 8 ≤ 224 → (wOff t + 16 ≤ o ∨ o + 8 ≤ wOff t) →
      s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 :=
    fun o ho h => by rw [hm, readW64_write128_ne _ _ (by have := w' t; omega_using [fit, this]) (by omega_using [fit, ho]) h]
  have r0 : s'.mem.readW (addr scr (wOff t)) 64 = W M t := by
    have e := readW_writeW128_q s.mem (addr scr (wOff t)) (W M (t + 1) ++ W M t) (j := 0) (by decide)
    rw [addr_add0] at e
    rw [hm, e, qword_append_0]
  have r1 : s'.mem.readW (addr scr (wOff (t + 1))) 64 = W M (t + 1) := by
    rw [hm, ← wOff_next tl, ← addr_add8 (by have := w' t; omega_using [fit, this]), readW_writeW128_q _ _ _ (by decide),
      qword_append_1]
  have xk : ∀ k < 3, s'.xmm (xr t k) = s.xmm (xr t k) := fun k hk => by
    obtain ⟨n3, n4, nx, ny⟩ := xr_sched_ne t k hk
    exact hx _ n3 n4 nx ny
  have mw : ∀ j, wOff j + 8 ≤ mirOff := fun j => by simp only [wOff, mirOff]; omega_using []
  have mv : ∀ k, vOff t k + 8 ≤ wOff t := fun k => vw_sep t k t
  -- The window after the store, but the copy.
  have win' : ∀ j, j < max (t + 2) 16 → t + 2 ≤ j + 16 → s'.mem.readW (addr scr (wOff j)) 64 = W M j :=
    fun j hj hj' => by
    by_cases hjt : j = t
    · subst hjt; exact r0
    by_cases hjt1 : j = t + 1
    · subst hjt1; exact r1
    · rw [rm _ (by have := wOff_lt j; omega_using [this]) (by simp only [wOff]; omega_using [hj, hj', hjt, hjt1])]
      exact hI.win j (by omega_using [hj, hjt, hjt1]) (by omega_using [hj'])
  -- The copy is stored only if `t mod 16 = 0`.
  split
  · rename_i h0
    refine WP.of_runBlock ?_
    have o := c.out (o := mirOff) (n := 8) (by decide) (by decide)
    simp only [stq, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store64, ea_at, hg,
      show s'.wr = s.wr from hwr, o, ↓reduceIte, hP, extractLsb'_qword, qword_append_0,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun k hk h0' h4 => ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun j hj hj' hj0 => ?_,
      fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [c.esi]
      rw [readW64_write_ne _ _ (by simp only [mirOff]; omega_using [fit]) (by have := vOff_lt t k; omega_using [fit, this])
        (.inr (by have := mv k; have := mw t; omega_arith)), rm _ (by have := vOff_lt t k; omega_using [this]) (.inr (mv k))]
      exact hI.vars k hk h0' h4
    · rw [xk 0 (by decide)]; exact hI.xa
    · rw [xk 1 (by decide)]; exact hI.xe
    · rw [xk 2 (by decide)]; exact hI.xbc
    · simp only [c.esi]
      rw [readW64_write_ne _ _ (by simp only [mirOff]; omega_using [fit]) (by have := wOff_lt j; omega_using [fit, this])
        (.inr (mw j))]
      exact win' j hj hj'
    · have : j = t := by omega_using [h0, hj, hj', hj0]
      subst this
      simp only [c.esi, Mem.readW_writeW_self64]
    · exact hI.gpr r h1 h2 h3
    · exact hrd.trans hI.rd
    · exact hI.wr
    · simp only [c.esi]
      exact frame_writeW (hm ▸ frame_writeW16 hI.frame fit (by have := wOff_pair t; omega_using [this]) _) fit
        (by decide) _
  · rename_i h0
    refine WP.block_nil ⟨fun k hk h0' h4 => ?_, by rw [xk 0 (by decide)]; exact hI.xa,
      by rw [xk 1 (by decide)]; exact hI.xe, by rw [xk 2 (by decide)]; exact hI.xbc, win',
      fun j hj hj' hj0 => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [rm _ (by have := vOff_lt t k; omega_using [this]) (.inr (mv k))]
      exact hI.vars k hk h0' h4
    · rw [rm _ (by decide) (.inl (by simp only [wOff, mirOff]; omega_using [tl]))]
      exact hI.mir j (by omega_using [tl, h0, hj, hj0]) (by omega_using [hj']) hj0
    · rw [hg, hI.gpr r h1 h2 h3]
    · rw [hrd, hI.rd]
    · rw [hwr, hI.wr]
    · rw [hm]; exact frame_writeW16 hI.frame fit (by have := wOff_pair t; omega_using [this]) _

/-! ## The rounds -/

/-- The window before step `t`: up to `Wₜ₋₁` (`Wₜ` too for odd `t`). -/
abbrev wEnd (t : Nat) : Nat := t + t % 2

theorem step_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : Ctx scr s₀) (hI : RInv scr H M s₀ (wEnd t) t s) :
    WP isa (.block (step t)) s (RInv scr H M s₀ (wEnd (t + 1)) (t + 1)) := by
  have c := c₀.of_rinv hI
  simp only [wEnd] at hI ⊢
  unfold step
  by_cases h16 : t < 16 ∨ t % 2 = 1
  · simp only [h16, ↓reduceIte]
    rcases h16 with h16 | hodd
    · exact WP.mono (round_ok c (hI.early (u' := 0) (by omega_using [h16]) (by omega_using [])) (by omega_using [h16]) (by omega_using []))
        fun s' h => h.early (by omega_using []) (by omega_using [h16])
    · rw [show t + 1 + (t + 1) % 2 = t + t % 2 by omega_using [hodd]]
      exact round_ok c hI (by omega_using [hodd]) (by omega_using [])
  · simp only [h16, ↓reduceIte]
    rw [WP.block_append_iff]
    rw [show t + t % 2 = t by omega_using [h16]] at hI
    rw [show t + 1 + (t + 1) % 2 = t + 2 by omega_using [h16]]
    exact WP.mono (schedule_ok c hI (by omega_using [h16]) (by omega_using [h16])) fun s' h =>
      round_ok (c₀.of_rinv h) h (by omega_using []) (by omega_using [])

theorem rounds_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State}
    (c₀ : Ctx scr s₀) (hI : RInv scr H M s₀ 0 0 s) :
    ∀ t, WP isa (rounds t) s (RInv scr H M s₀ (wEnd t) t) := by
  intro t
  induction t with
  | zero => exact WP.block_nil hI
  | succ t ih => exact WP.seq (WP.mono ih fun s' h => step_ok c₀ h)

end VG.Proof.Sha512.X86
