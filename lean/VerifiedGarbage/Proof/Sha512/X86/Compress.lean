import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Impl.Sha512.X86
import VerifiedGarbage.Proof.Sha256.X86.Stream.Finalize
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.Sha512
import VerifiedGarbage.TCB.X86.Target
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Impl.Sha512.X86.Stream
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.SseTaint

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.X86.Sse`. -/
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
  · rw [VG.Proof.Sha512.X86.qword_append_0]

theorem q_psllq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psllq a n) 0 = if 63 < n.toNat then 0 else qword a 0 <<< n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [VG.Proof.Sha512.X86.qword_append_0]

theorem q1_psrlq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psrlq a n) 1 = if 63 < n.toNat then 0 else qword a 1 >>> n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [VG.Proof.Sha512.X86.qword_append_1]

theorem q1_psllq (a : BitVec 128) (n : BitVec 8) :
    qword (XShiftOp.eval .psllq a n) 1 = if 63 < n.toNat then 0 else qword a 1 <<< n.toNat := by
  simp only [XShiftOp.eval]
  split
  · rfl
  · rw [VG.Proof.Sha512.X86.qword_append_1]

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
  simp only [XBinOp.eval, VG.Proof.Sha512.X86.qword_append_0]

theorem q1_paddq (a b : BitVec 128) : qword (XBinOp.eval .paddq a b) 1 = qword a 1 + qword b 1 := by
  simp only [XBinOp.eval, VG.Proof.Sha512.X86.qword_append_1]

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

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (VG.Impl.Sha512.X86.at_ b d) = VG.X86.addr (s.gpr b) d := rfl

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
    (ib : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) b) 8)
    (id : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) d) 8)
    (if_ : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) f) 8)
    (ig : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) g) 8)
    (ih : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) h) 8)
    (iw : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) w) 8)
    (oa : InRegions s.wr (VG.X86.addr (s.gpr .esi) a) 8) (oe : InRegions s.wr (VG.X86.addr (s.gpr .esi) e) 8)
    (eb : ∀ v : BitVec 64, (s.mem.writeW (VG.X86.addr (s.gpr .esi) e) v).readW (VG.X86.addr (s.gpr .esi) b) 64 =
      s.mem.readW (VG.X86.addr (s.gpr .esi) b) 64)
    (ed : ∀ v : BitVec 64, (s.mem.writeW (VG.X86.addr (s.gpr .esi) e) v).readW (VG.X86.addr (s.gpr .esi) d) 64 =
      s.mem.readW (VG.X86.addr (s.gpr .esi) d) 64) :
    WP isa (.block (roundW a b d e f g h w k A E BC T NE AB)) s fun s' =>
      let m o := s.mem.readW (VG.X86.addr (s.gpr .esi) o) 64
      let va := qword (s.xmm A) 0
      let ve := qword (s.xmm E) 0
      let u := VG.Proof.Sha512.X86.uOf (m h) (Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k) (m w) ve (m f) (m g)
      let s1 := split6 ve 14 4 23 23 23 4
      qword (s'.xmm T) 0 =
        u + s1 + (qword (s.xmm BC) 0 &&& (va ^^^ m b) ^^^ m b) + split6 va 28 6 5 25 5 6 ∧
      qword (s'.xmm NE) 0 = m d + u + s1 ∧ qword (s'.xmm AB) 0 = va ^^^ m b ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = (s.mem.writeW (VG.X86.addr (s.gpr .esi) e) ve).writeW (VG.X86.addr (s.gpr .esi) a) va ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [roundW, bigSig, ldq, stq, xb, xs, X, Y, List.cons_append, List.nil_append] at hn hn' ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hn hn'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, VG.X86.readSrc, isa,
    State.load64, State.store64, VG.Proof.Sha512.X86.ea_at, VG.Proof.Sha512.X86.extractLsb'_qword, eval_movdqa,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.xmm_setReg, RegUpd.gpr_setReg,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, reduceCtorEq, not_false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left',
    hn, hn', ib, id, if_, ig, ih, iw, oa, oe, eb, ed, VG.Proof.Sha512.X86.q_psrlq, VG.Proof.Sha512.X86.q_psllq, VG.Proof.Sha512.X86.q_pxor, VG.Proof.Sha512.X86.q_pand, VG.Proof.Sha512.X86.q_paddq,
    VG.Proof.Sha512.X86.q_punpckldq_movd, VG.Proof.Sha512.X86.qword_append_0, BitVec.reduceToNat, Nat.reduceLT]
  refine ⟨rfl, rfl, trivial, fun r hr => ?_, trivial, trivial, trivial⟩
  simp only [hr, ↓reduceIte]

/-! ## Two steps of the message schedule -/

/-- `Wₜ = σ₁(Wₜ₋₂) + Wₜ₋₇ + σ₀(Wₜ₋₁₅) + Wₜ₋₁₆`, as `scheduleW` computes it in each quadword. -/
def schedOf (x2 x7 x15 x16 : BitVec 64) : BitVec 64 :=
  chain5 x2 6 3 13 42 42 + x7 + chain5 x15 1 56 6 7 1 + x16

theorem scheduleW_ok (o2 o7 o15 o16 : Nat) (P Q : XReg) (hn : [P, Q, X, Y].Nodup) (s : State)
    (i2 : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) o2) 16)
    (i7 : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) o7) 16)
    (i15 : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) o15) 16)
    (i16 : InRegions (s.rd ++ s.wr) (VG.X86.addr (s.gpr .esi) o16) 16)
    (w16 : InRegions s.wr (VG.X86.addr (s.gpr .esi) o16) 16) :
    WP isa (.block (scheduleW o2 o7 o15 o16 P Q)) s fun s' =>
      let m o j := qword (s.mem.readW (VG.X86.addr (s.gpr .esi) o) 128) j
      let v := VG.Proof.Sha512.X86.schedOf (m o2 1) (m o7 1) (m o15 1) (m o16 1) ++ VG.Proof.Sha512.X86.schedOf (m o2 0) (m o7 0) (m o15 0) (m o16 0)
      (∀ r, r ≠ P → r ≠ Q → r ≠ X → r ≠ Y → s'.xmm r = s.xmm r) ∧ s'.xmm P = v ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (VG.X86.addr (s.gpr .esi) o16) v ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [scheduleW, sig5, ldo, sto, xb, xs, X, Y, List.cons_append, List.nil_append] at hn hn' ⊢
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at hn hn'
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa,
    State.load128, State.store128, VG.Proof.Sha512.X86.ea_at, eval_movdqa, VG.Proof.Sha512.X86.eval_paddq,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true,
    ↓reduceIte, Option.map_some, Option.some.injEq, exists_eq_left',
    hn, hn', i2, i7, i15, i16, w16, VG.Proof.Sha512.X86.q_psrlq, VG.Proof.Sha512.X86.q_psllq, VG.Proof.Sha512.X86.q_pxor, VG.Proof.Sha512.X86.q1_psrlq, VG.Proof.Sha512.X86.q1_psllq, VG.Proof.Sha512.X86.q1_pxor,
    VG.Proof.Sha512.X86.qword_append_0, VG.Proof.Sha512.X86.qword_append_1, BitVec.reduceToNat, Nat.reduceLT]
  refine ⟨fun r h1 h2 h3 h4 => ?_, rfl, trivial, rfl, trivial, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h1, h2, h3, h4, not_false_eq_true]

end VG.Proof.Sha512.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.X86.Rounds`. -/
section

/-!
# x86 (32-bit): 64-bit words as pairs of 32-bit words

Weakest-precondition rules for the macros of `VG.Impl.Sha512.X86` that keep a
64-bit word in a pair of general-purpose registers (loads and stores of a
64-bit word in a buffer, 64-bit additions; BLAKE2b's, Argon2's and SHA-3's
x86 code use them) and for `loadW`, which makes a message word of SHA-512,
each proved once for any registers and offsets, in continuation-passing
style: the rule for `x` proves `WP (x ++ rest)` from a proof of `WP rest` for
every state `x` can end in. The halves of 64-bit values are those of
`Proof/Sha512/Word64.lean`.
-/

namespace VG.Proof.Sha512.X86

open VG VG.X86
open VG.Impl.Sha512.X86 (at_ sc T Y0 Y1 Z0 Z1 ld st add64 add64m loadW)
open VG.Proof.Sha512.Word64 (lo hi lo_add hi_add lo_append hi_append hi_append_lo)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd WP.cons wp_store wp_bswap wp_shr)

theorem lo_eq (x : BitVec 64) : Impl.Sha512.X86.lo x = lo x := rfl
theorem hi_eq (x : BitVec 64) : Impl.Sha512.X86.hi x = hi x := rfl

/-! ## States -/

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags). -/
structure Only (ds : List Reg) (s s' : State) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.refl (ds : List Reg) (s : State) : VG.Proof.Sha512.X86.Only ds s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Only.of_upd {s s' : State} {d : Reg} {v : BitVec 32} (u : Upd s s' d v) : VG.Proof.Sha512.X86.Only [d] s s' :=
  ⟨fun r h => u.other r (by simpa using h), u.mem, u.rd, u.wr⟩

theorem Only.trans {ds es : List Reg} {s₁ s₂ s₃ : State} (h₁ : VG.Proof.Sha512.X86.Only ds s₁ s₂) (h₂ : VG.Proof.Sha512.X86.Only es s₂ s₃) :
    VG.Proof.Sha512.X86.Only (ds ++ es) s₁ s₃ :=
  ⟨fun r h => by
    simp only [List.mem_append, not_or] at h
    rw [h₂.gpr r h.2, h₁.gpr r h.1], h₂.mem.trans h₁.mem, h₂.rd.trans h₁.rd, h₂.wr.trans h₁.wr⟩

theorem Only.mono {ds es : List Reg} {s s' : State} (h : VG.Proof.Sha512.X86.Only ds s s') (he : ∀ r ∈ ds, r ∈ es) :
    VG.Proof.Sha512.X86.Only es s s' :=
  ⟨fun r hr => h.gpr r fun hd => hr (he r hd), h.mem, h.rd, h.wr⟩

/-- The 64-bit word `x` is in the registers `l` (low half) and `h`. -/
def Pair (s : State) (l h : Reg) (x : BitVec 64) : Prop := s.gpr l = lo x ∧ s.gpr h = hi x

theorem Pair.of_only {s s' : State} {l h : Reg} {x : BitVec 64} {ds : List Reg} (p : VG.Proof.Sha512.X86.Pair s l h x)
    (o : VG.Proof.Sha512.X86.Only ds s s') (hl : l ∉ ds) (hh : h ∉ ds) : VG.Proof.Sha512.X86.Pair s' l h x :=
  ⟨(o.gpr l hl).trans p.1, (o.gpr h hh).trans p.2⟩

/-- `s'` is `s` with (at most) the registers `ds` changed (and the flags), and memory `m`. -/
structure Wrote (ds : List Reg) (s s' : State) (m : Mem) : Prop where
  gpr : ∀ r, r ∉ ds → s'.gpr r = s.gpr r
  mem : s'.mem = m
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Only.wrote {ds : List Reg} {s₁ s₂ s₃ : State} {m : Mem} (h : VG.Proof.Sha512.X86.Only ds s₁ s₂) (u : Mupd s₂ s₃ m) :
    VG.Proof.Sha512.X86.Wrote ds s₁ s₃ m :=
  ⟨fun r hr => by rw [u.gpr, h.gpr r hr], u.mem, u.rd.trans h.rd, u.wr.trans h.wr⟩

theorem Wrote.mono' {ds es : List Reg} {s s' : State} {m : Mem} (w : VG.Proof.Sha512.X86.Wrote ds s s' m)
    (h : ∀ r ∈ ds, r ∈ es) : VG.Proof.Sha512.X86.Wrote es s s' m :=
  ⟨fun r hr => w.gpr r fun hd => hr (h r hd), w.mem, w.rd, w.wr⟩

/-! ## Memory -/

/-- The 64-bit word at `[b + off]`, from its two halves. -/
def rd64 (m : Mem) (b : BitVec 32) (off : Nat) : BitVec 64 :=
  m.readW (addr b (off + 4)) 32 ++ m.readW (addr b off) 32

/-- Store the 64-bit word `x` at `[b + off]`, as its two halves. -/
def write64 (m : Mem) (b : BitVec 32) (off : Nat) (x : BitVec 64) : Mem :=
  (m.writeW (addr b off) (lo x)).writeW (addr b (off + 4)) (hi x)

theorem lo_rd64 (m : Mem) (b : BitVec 32) (off : Nat) : lo (VG.Proof.Sha512.X86.rd64 m b off) = m.readW (addr b off) 32 :=
  lo_append _ _

theorem hi_rd64 (m : Mem) (b : BitVec 32) (off : Nat) :
    hi (VG.Proof.Sha512.X86.rd64 m b off) = m.readW (addr b (off + 4)) 32 :=
  hi_append _ _

theorem mem_rd {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n :=
  let ⟨r, hr, hc⟩ := h
  ⟨r, List.mem_append_right _ hr, hc⟩

/-- Every word `[B + o, B + o + 4)` with `o + 4 ≤ N` is writable. -/
def Acc (wr : List Region) (B : BitVec 32) (N : Nat) : Prop :=
  ∀ o, o + 4 ≤ N → InRegions wr (addr B o) 4

/-! ## Single instructions -/

section
variable {is : List Instr} {s : State} {Q : State → Prop}

theorem ea_of {b : Reg} {B : BitVec 32} (hb : s.gpr b = B) (d : Nat) : s.ea (at_ b d) = addr B d := by
  rw [← hb]; rfl

theorem readSrc_mem {b : Reg} {d : Nat} {B : BitVec 32} (hb : s.gpr b = B)
    (hin : InRegions (s.rd ++ s.wr) (addr B d) 4) :
    readSrc s (.mem (at_ b d)) = some (s.mem.readW (addr B d) 32) := by
  show s.load32 (s.ea (at_ b d)) = _
  rw [VG.Proof.Sha512.X86.ea_of hb]; simp only [State.load32, hin, ↓reduceIte]

theorem wp_movS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d v → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d src :: is)) s Q :=
  WP.cons (s' := s.setReg d v) (by simp [exec, h]) (k _ (Upd.setReg _ _ _))

theorem wp_addS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d + v) → s'.cf = some (decide (2 ^ 32 ≤ (s.gpr d).toNat + v.toNat)) →
      WP isa (.block is) s' Q) :
    WP isa (.block (.alu .add d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _) rfl)

theorem wp_adcS {d : Reg} {src : Src} {v : BitVec 32} {c : Bool} (h : readSrc s src = some v)
    (hc : s.cf = some c)
    (k : ∀ s', Upd s s' d (s.gpr d + v + (BitVec.ofBool c).setWidth 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .adc d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h, hc]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_xorS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ^^^ v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .xor d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_andS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d &&& v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .and d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_orS {d : Reg} {src : Src} {v : BitVec 32} (h : readSrc s src = some v)
    (k : ∀ s', Upd s s' d (s.gpr d ||| v) → WP isa (.block is) s' Q) :
    WP isa (.block (.alu .or d src :: is)) s Q :=
  WP.cons (by simp [exec, execAlu, h]; rfl) (k _ (Upd.flags _ _ _ _ _ _))

theorem wp_ror {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d ((s.gpr d).rotateRight n) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .ror d n :: is)) s Q :=
  WP.cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl)
    (k _ (Upd.setFlags _ _ _ _ _ _ _))

end

theorem carry_eq (a b : BitVec 32) :
    (BitVec.ofBool (decide (2 ^ 32 ≤ a.toNat + b.toNat))).setWidth 32 =
      if 2 ^ 32 ≤ a.toNat + b.toNat then 1 else 0 := by
  by_cases h : 2 ^ 32 ≤ a.toNat + b.toNat <;> simp only [h, decide_true, decide_false, ↓reduceIte] <;> rfl

/-- A left shift, as the code computes it: a rotation, masked. -/
theorem ror_and (x : BitVec 32) {n : Nat} (h0 : 0 < n) (h : n < 32) :
    x.rotateRight (32 - n) &&& (BitVec.allOnes 32 <<< n) = x <<< n := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_rotateRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_allOnes, Nat.mod_eq_of_lt (show 32 - n < 32 by omega)]
  by_cases hc : i < n
  · simp [hc, hi]
  · simp [hc, hi, show ¬ i < 32 - (32 - n) by omega, show i - (32 - (32 - n)) = i - n by omega]
    omega

/-! ## Loads, stores and additions of 64-bit words in the scratch buffer -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_ld {l h : Reg} {B : BitVec 32} {off N : Nat} (hl : l ≠ .esi) (hlh : l ≠ h)
    (hb : s.gpr .esi = B) (hA : VG.Proof.Sha512.X86.Acc s.wr B N) (ho : off + 8 ≤ N)
    (k : ∀ s', VG.Proof.Sha512.X86.Only [l, h] s s' → VG.Proof.Sha512.X86.Pair s' l h (VG.Proof.Sha512.X86.rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (ld l h off ++ rest)) s Q := by
  simp only [ld, sc, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem hb (VG.Proof.Sha512.X86.mem_rd (hA off (by omega)))) fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem (by rw [u₁.other _ (Ne.symm hl), hb])
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Sha512.X86.mem_rd (hA (off + 4) (by omega)))) fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other l hlh, u₁.gpr, VG.Proof.Sha512.X86.lo_rd64]
  · rw [u₂.gpr, u₁.mem, VG.Proof.Sha512.X86.hi_rd64]

theorem wp_st {l h : Reg} {B : BitVec 32} {off N : Nat} {x : BitVec 64}
    (hb : s.gpr .esi = B) (hA : VG.Proof.Sha512.X86.Acc s.wr B N) (ho : off + 8 ≤ N) (hp : VG.Proof.Sha512.X86.Pair s l h x)
    (k : ∀ s', Mupd s s' (VG.Proof.Sha512.X86.write64 s.mem B off x) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Sha512.X86.st l h off ++ rest)) s Q := by
  simp only [VG.Impl.Sha512.X86.st, List.cons_append, List.nil_append]
  refine wp_store (VG.Proof.Sha512.X86.ea_of hb _) (hA off (by omega)) fun s₁ u₁ => ?_
  refine wp_store (VG.Proof.Sha512.X86.ea_of (by rw [u₁.gpr, hb]) _) (by rw [u₁.wr]; exact hA (off + 4) (by omega))
    fun s₂ u₂ => k s₂ ⟨u₂.gpr.trans u₁.gpr, ?_, u₂.rd.trans u₁.rd, u₂.wr.trans u₁.wr⟩
  rw [u₂.mem, u₁.mem, u₁.gpr, hp.1, hp.2]; rfl

theorem wp_add64 {dl dh l h : Reg} {x y : BitVec 64} (h₁ : dl ≠ dh) (h₂ : dl ≠ h)
    (px : VG.Proof.Sha512.X86.Pair s dl dh x) (py : VG.Proof.Sha512.X86.Pair s l h y)
    (k : ∀ s', VG.Proof.Sha512.X86.Only [dl, dh] s s' → VG.Proof.Sha512.X86.Pair s' dl dh (x + y) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64 dl dh l h ++ rest)) s Q := by
  simp only [add64, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.X86.wp_addS rfl fun s₁ u₁ hc => ?_
  refine VG.Proof.Sha512.X86.wp_adcS rfl hc fun s₂ u₂ => k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, py.1, lo_add]
  · rw [u₂.gpr, VG.Proof.Sha512.X86.carry_eq, u₁.other dh (Ne.symm h₁), u₁.other h (Ne.symm h₂), px.1, py.1, px.2,
      py.2, hi_add]

theorem wp_add64m {dl dh : Reg} {x : BitVec 64} {B : BitVec 32} {off N : Nat} (h₁ : dl ≠ dh)
    (h₂ : dl ≠ .esi) (hb : s.gpr .esi = B) (hA : VG.Proof.Sha512.X86.Acc s.wr B N) (ho : off + 8 ≤ N) (px : VG.Proof.Sha512.X86.Pair s dl dh x)
    (k : ∀ s', VG.Proof.Sha512.X86.Only [dl, dh] s s' → VG.Proof.Sha512.X86.Pair s' dl dh (x + VG.Proof.Sha512.X86.rd64 s.mem B off) → WP isa (.block rest) s' Q) :
    WP isa (.block (add64m dl dh off ++ rest)) s Q := by
  simp only [add64m, sc, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.X86.wp_addS (VG.Proof.Sha512.X86.readSrc_mem hb (VG.Proof.Sha512.X86.mem_rd (hA off (by omega)))) fun s₁ u₁ hc => ?_
  refine VG.Proof.Sha512.X86.wp_adcS (VG.Proof.Sha512.X86.readSrc_mem (by rw [u₁.other _ (Ne.symm h₂), hb])
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Sha512.X86.mem_rd (hA (off + 4) (by omega)))) hc fun s₂ u₂ =>
    k s₂ ((Only.of_upd u₁).trans (Only.of_upd u₂)) ⟨?_, ?_⟩
  · rw [u₂.other dl h₁, u₁.gpr, px.1, lo_add, VG.Proof.Sha512.X86.lo_rd64]
  · rw [u₂.gpr, VG.Proof.Sha512.X86.carry_eq, u₁.other dh (Ne.symm h₁), u₁.mem, px.1, px.2, hi_add, VG.Proof.Sha512.X86.lo_rd64, VG.Proof.Sha512.X86.hi_rd64]

end

/-! ## 64-bit words in memory -/

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_self (m : Mem) {b : BitVec 32} {o : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) : VG.Proof.Sha512.X86.rd64 (VG.Proof.Sha512.X86.write64 m b o x) b o = x := by
  simp only [VG.Proof.Sha512.X86.rd64, VG.Proof.Sha512.X86.write64]
  rw [Mem.readW_writeW_self32, readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    Mem.readW_writeW_self32, hi_append_lo]

open VG.Proof.Sha256.X86.Stream (readW_writeW_addr) in
theorem rd64_write64_ne (m : Mem) {b : BitVec 32} {o o' : Nat} (x : BitVec 64)
    (h : b.toNat + o + 8 ≤ 2 ^ 32) (h' : b.toNat + o' + 8 ≤ 2 ^ 32) (hs : o + 8 ≤ o' ∨ o' + 8 ≤ o) :
    VG.Proof.Sha512.X86.rd64 (VG.Proof.Sha512.X86.write64 m b o x) b o' = VG.Proof.Sha512.X86.rd64 m b o' := by
  simp only [VG.Proof.Sha512.X86.rd64, VG.Proof.Sha512.X86.write64]
  rw [readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega),
    readW_writeW_addr _ _ (by omega) (by omega) (by omega)]

/-! ## The message schedule -/

section
variable {rest : List Instr} {s : State} {Q : State → Prop}

theorem wp_loadW {i o N : Nat} {Bb B : BitVec 32} (ho : o + 8 ≤ N)
    (hA : VG.Proof.Sha512.X86.Acc s.wr B N) (hb : s.gpr .esi = B) (hbb : s.gpr .edi = Bb)
    (hin : InRegions (s.rd ++ s.wr) (addr Bb i) 4) (hin' : InRegions (s.rd ++ s.wr) (addr Bb (i + 4)) 4)
    (k : ∀ s', VG.Proof.Sha512.X86.Wrote [Z0, Z1] s s' (VG.Proof.Sha512.X86.write64 s.mem B o
      (bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))) →
      WP isa (.block rest) s' Q) :
    WP isa (.block (loadW i o ++ rest)) s Q := by
  simp only [loadW, List.cons_append, List.nil_append]
  refine VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem hbb hin') fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem (by rw [u₁.other _ (by decide), hbb]) (by rw [u₁.rd, u₁.wr]; exact hin))
    fun s₂ u₂ => wp_bswap fun s₃ u₃ => wp_bswap fun s₄ u₄ => ?_
  have O := (((Only.of_upd u₁).trans (Only.of_upd u₂)).trans (Only.of_upd u₃)).trans (Only.of_upd u₄)
  refine VG.Proof.Sha512.X86.wp_st (x := bswap (s.mem.readW (addr Bb i) 32) ++ bswap (s.mem.readW (addr Bb (i + 4)) 32))
    (by rw [O.gpr _ (by decide), hb]) (by rw [O.wr]; exact hA) ho ⟨?_, ?_⟩ fun s₅ u₅ => k s₅ ?_
  · rw [lo_append, u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr]
  · rw [hi_append, u₄.gpr, u₃.other _ (by decide), u₂.gpr, u₁.mem]
  · rw [O.mem] at u₅
    exact (O.mono (by decide)).wrote u₅

end

open VG.Proof.Sha256.X86.Stream (contains_addr)

theorem frame_write64 {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hr : ⟨b.setWidth 64, N⟩ ∈ rs) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) (x : BitVec 64) :
    Frame rs m (VG.Proof.Sha512.X86.write64 m' b o x) :=
  (h.writeW hr _ (contains_addr (by omega) (by omega) hfit)).writeW hr _
    (contains_addr (by omega) (by omega) hfit)

theorem Acc.of_mem {wr : List Region} {B : BitVec 32} {N : Nat} (h : ⟨B.setWidth 64, N⟩ ∈ wr)
    (hfit : B.toNat + N ≤ 2 ^ 32) : VG.Proof.Sha512.X86.Acc wr B N :=
  fun _ ho => ⟨_, h, contains_addr ho (by omega) hfit⟩

theorem rd64_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b.setWidth 64, N⟩ r) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) :
    VG.Proof.Sha512.X86.rd64 m' b o = VG.Proof.Sha512.X86.rd64 m b o := by
  simp only [VG.Proof.Sha512.X86.rd64]
  rw [h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide),
    h.readW (contains_addr (by omega) (by omega) hfit) hd (by decide)]

end VG.Proof.Sha512.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.X86.Steps`. -/
section

/-!
# SHA-512 on x86 (32-bit) with SSE2: the rounds

The invariant of the rounds (`RInv`): the working variables but `a` and `e`
in their slots, `a`, `e` and `b ⊕ c` in the registers of their roles, and the
message-schedule window, with the copy of its word `Wⱼ`, `j mod 16 = 0`.
`round_ok` and `schedule_ok` instantiate the symbolic runs of `Sse.lean` for
round `t` and for the words `Wₜ`, `Wₜ₊₁`.
-/

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
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_ofNat_add_ofNat]

theorem addr_add0 (b : BitVec 32) (o : Nat) : addr b o + BitVec.ofNat 64 (8 * 0) = addr b o :=
  BitVec.add_zero _

/-- The two quadwords of a 16-byte read. -/
theorem qword_readW_0 (m : Mem) (b : BitVec 32) (o : Nat) :
    qword (m.readW (addr b o) 128) 0 = m.readW (addr b o) 64 := by
  rw [VG.Proof.Sha512.X86.qword_readW _ _ (by decide), VG.Proof.Sha512.X86.addr_add0]

theorem qword_readW_1 (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 < 2 ^ 32) :
    qword (m.readW (addr b o) 128) 1 = m.readW (addr b (o + 8)) 64 := by
  rw [VG.Proof.Sha512.X86.qword_readW _ _ (by decide), VG.Proof.Sha512.X86.addr_add8 h]

/-- `rd64`, the word as two halves, is the 64-bit word. -/
theorem rd64_eq_readW (m : Mem) {b : BitVec 32} {o : Nat} (h : b.toNat + o + 8 ≤ 2 ^ 32) :
    VG.Proof.Sha512.X86.rd64 m b o = m.readW (addr b o) 64 := by
  rw [VG.Proof.Sha512.X86.rd64, Word64.readW64, addr_eq (x := b) (k := o + 4) (by omega), addr_eq (x := b) (k := o) (by omega),
    ← Offset.add_ofNat_add_ofNat]
  rfl

/-! ## Offsets and registers -/

theorem vOff_lt (t k : Nat) : vOff t k + 8 ≤ 64 := by simp only [vOff]; omega

theorem wOff_lt (j : Nat) : wOff j + 8 ≤ 192 := by simp only [wOff]; omega

/-- Two words from `wOff j`, the second the next slot or the copy after the window. -/
theorem wOff_pair (j : Nat) : wOff j + 16 ≤ 200 := by simp only [wOff]; omega

theorem vw_sep (t k j : Nat) : vOff t k + 8 ≤ wOff j := by simp only [vOff, wOff]; omega

theorem vOff_sep (t : Nat) {i j : Nat} (hi : i < 8) (hj : j < 8) (h : i ≠ j) :
    vOff t i + 8 ≤ vOff t j ∨ vOff t j + 8 ≤ vOff t i := by
  simp only [vOff]; omega

theorem vOff_succ (t k : Nat) (hk : k < 7) : vOff (t + 1) (k + 1) = vOff t k := by
  simp only [vOff]; omega

theorem wOff_sep {i j : Nat} (h : i % 16 ≠ j % 16) : wOff i + 8 ≤ wOff j ∨ wOff j + 8 ≤ wOff i := by
  simp only [wOff]; omega

theorem wOff_next {j : Nat} (h : j % 16 ≠ 15) : wOff j + 8 = wOff (j + 1) := by simp only [wOff]; omega

theorem wOff_last {j : Nat} (h : j % 16 = 15) : wOff j + 8 = mirOff := by simp only [wOff, mirOff]; omega

theorem xr_mod (t k : Nat) : xr t k = xr (t % 2) k := by simp only [xr, Nat.mod_mod]

theorem xr_nodup (t : Nat) : [xr t 0, xr t 1, xr t 2, xr t 3, xr t 4, xr t 5, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 0, xr p 1, xr p 2, xr p 3, xr p 4, xr p 5, X, Y].Nodup := by decide
  simp only [VG.Proof.Sha512.X86.xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_nodup_sched (t : Nat) : [xr t 3, xr t 4, X, Y].Nodup := by
  have key : ∀ p < 2, [xr p 3, xr p 4, X, Y].Nodup := by decide
  simp only [VG.Proof.Sha512.X86.xr_mod t]
  exact key _ (Nat.mod_lt _ (by decide))

theorem xr_succ (t k : Nat) (hk : k < 3) : xr (t + 1) k = xr t (k + 3) := by
  have key : ∀ p < 2, ∀ k < 3, xr (p + 1) k = xr p (k + 3) := by decide
  rw [VG.Proof.Sha512.X86.xr_mod t, VG.Proof.Sha512.X86.xr_mod (t + 1), show (t + 1) % 2 = (t % 2 + 1) % 2 by omega, ← VG.Proof.Sha512.X86.xr_mod]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-- The registers of roles 0–2 are none of the schedule's temporaries. -/
theorem xr_sched_ne (t k : Nat) (hk : k < 3) :
    xr t k ≠ xr t 3 ∧ xr t k ≠ xr t 4 ∧ xr t k ≠ X ∧ xr t k ≠ Y := by
  have key : ∀ p < 2, ∀ k < 3, xr p k ≠ xr p 3 ∧ xr p k ≠ xr p 4 ∧ xr p k ≠ X ∧ xr p k ≠ Y := by decide
  rw [VG.Proof.Sha512.X86.xr_mod t k, VG.Proof.Sha512.X86.xr_mod t 3, VG.Proof.Sha512.X86.xr_mod t 4]
  exact key _ (Nat.mod_lt _ (by decide)) k hk

/-! ## The invariant -/

/-- The part of the scratch region the rounds write. -/
abbrev workR (scr : BitVec 32) : Region := ⟨scr.setWidth 64, 200⟩

/-- Where the scratch buffer is: at `scr` (in `esi`), writable. -/
structure Ctx (scr : BitVec 32) (s : State) : Prop where
  esi : s.gpr .esi = scr
  fit : scr.toNat + 224 ≤ 2 ^ 32
  mem : ⟨scr.setWidth 64, 224⟩ ∈ s.wr

theorem Ctx.out {scr : BitVec 32} {s : State} (c : VG.Proof.Sha512.X86.Ctx scr s) {o n : Nat} (ho : o + n ≤ 224) (hn : 0 < n) :
    InRegions s.wr (addr (s.gpr .esi) o) n :=
  ⟨_, c.mem, by rw [c.esi]; exact contains_addr ho hn c.fit⟩

theorem Ctx.inp {scr : BitVec 32} {s : State} (c : VG.Proof.Sha512.X86.Ctx scr s) {o n : Nat} (ho : o + n ≤ 224) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) o) n :=
  VG.Proof.Sha512.X86.mem_rd (c.out ho hn)

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
  frame : Frame [VG.Proof.Sha512.X86.workR scr] s₀.mem s.mem

theorem Ctx.of_rinv {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : VG.Proof.Sha512.X86.Ctx scr s₀) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ u t s) : VG.Proof.Sha512.X86.Ctx scr s :=
  ⟨(hI.gpr _ (by decide) (by decide) (by decide)).trans c.esi, c.fit, hI.wr ▸ c.mem⟩

/-- Every window of at most the first 16 words is all of them. -/
theorem RInv.early {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u u' t : Nat}
    (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ u t s) (hu : u ≤ 16) (hu' : u' ≤ 16) : VG.Proof.Sha512.X86.RInv scr H M s₀ u' t s :=
  { hI with
    win := fun j hj _ => hI.win j (by omega) (by omega)
    mir := fun j hj _ h0 => hI.mir j (by omega) (by omega) h0 }

theorem frame_writeW {scr : BitVec 32} {m m' : Mem} (h : Frame [VG.Proof.Sha512.X86.workR scr] m m') (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    {o : Nat} (ho : o + 8 ≤ 200) (v : BitVec 64) : Frame [VG.Proof.Sha512.X86.workR scr] m (m'.writeW (addr scr o) v) :=
  h.writeW (by simp) v (contains_addr ho (by decide) (by omega))

theorem frame_writeW16 {scr : BitVec 32} {m m' : Mem} (h : Frame [VG.Proof.Sha512.X86.workR scr] m m') (hfit : scr.toNat + 224 ≤ 2 ^ 32)
    {o : Nat} (ho : o + 16 ≤ 200) (v : BitVec 128) : Frame [VG.Proof.Sha512.X86.workR scr] m (m'.writeW (addr scr o) v) :=
  h.writeW (by simp) v (contains_addr ho (by decide) (by omega))

/-! ## A round -/

theorem round_word (v : HashValue) (k w : Word) :
    VG.Proof.Sha512.X86.uOf v[7] (Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k) w v[4] v[5] v[6] + split6 v[4] 14 4 23 23 23 4 =
      v[7] + Spec.Sha512.bsig1 v[4] + Spec.Sha512.ch v[4] v[5] v[6] + k + w := by
  rw [VG.Proof.Sha512.X86.uOf, show Impl.Sha512.X86.hi k ++ Impl.Sha512.X86.lo k = k from hi_append_lo k, bsig1_split,
    ← ch_eq]
  simp only [BitVec.add_assoc, BitVec.add_comm, add_left_comm]

theorem round_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : VG.Proof.Sha512.X86.Ctx scr s) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ u t s) (ht : t < max u 16) (hu : u ≤ t + 16) :
    WP isa (.block (round t)) s (VG.Proof.Sha512.X86.RInv scr H M s₀ u (t + 1)) := by
  set v := Spec.Sha512.rounds H M t with hv
  have hw : s.mem.readW (addr scr (wOff t)) 64 = W M t := hI.win t ht hu
  have fit := c.fit
  have vl := VG.Proof.Sha512.X86.vOff_lt t
  have e14 := VG.Proof.Sha512.X86.vOff_sep t (i := 1) (j := 4) (by decide) (by decide) (by decide)
  have e34 := VG.Proof.Sha512.X86.vOff_sep t (i := 3) (j := 4) (by decide) (by decide) (by decide)
  have rb : ∀ (o : Nat) (x : BitVec 64), o + 8 ≤ 64 → (vOff t 4 + 8 ≤ o ∨ o + 8 ≤ vOff t 4) →
      (s.mem.writeW (addr (s.gpr .esi) (vOff t 4)) x).readW (addr (s.gpr .esi) o) 64 =
        s.mem.readW (addr (s.gpr .esi) o) 64 := fun o x ho h => by
    rw [c.esi]; exact VG.Proof.Sha512.X86.readW64_write_ne _ _ (by have := vl 4; omega) (by omega) h
  refine WP.mono (VG.Proof.Sha512.X86.roundW_ok _ _ _ _ _ _ _ _ (K t) _ _ _ _ _ _ (VG.Proof.Sha512.X86.xr_nodup t) s
    (c.inp (by have := vl 1; omega) (by decide)) (c.inp (by have := vl 3; omega) (by decide))
    (c.inp (by have := vl 5; omega) (by decide)) (c.inp (by have := vl 6; omega) (by decide))
    (c.inp (by have := vl 7; omega) (by decide)) (c.inp (by have := VG.Proof.Sha512.X86.wOff_lt t; omega) (by decide))
    (c.out (by have := vl 0; omega) (by decide)) (c.out (by have := vl 4; omega) (by decide))
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
  have e04 := VG.Proof.Sha512.X86.vOff_sep t (i := 0) (j := 4) (by decide) (by decide) (by decide)
  -- The new memory, at the offsets of the working variables and the window.
  have rm : ∀ o, o + 8 ≤ 200 → (vOff t 0 + 8 ≤ o ∨ o + 8 ≤ vOff t 0) →
      (vOff t 4 + 8 ≤ o ∨ o + 8 ≤ vOff t 4) → s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 :=
    fun o ho h0 h4 => by
      rw [hm, VG.Proof.Sha512.X86.readW64_write_ne _ _ (by have := vl 0; omega) (by omega) h0,
        VG.Proof.Sha512.X86.readW64_write_ne _ _ (by have := vl 4; omega) (by omega) h4]
  have mv : ∀ k, vOff t k + 8 ≤ mirOff := fun k => by have := VG.Proof.Sha512.X86.vw_sep t k 0; simp only [wOff, mirOff] at *; omega
  refine ⟨fun k hk h0 h4 => ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun j hj hj' h0 => ?_,
    fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
  · rw [hnext]
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [VG.Proof.Sha512.X86.vOff_succ t i (by omega)]
    by_cases hi0 : i = 0
    · subst hi0
      rw [hm, Mem.readW_writeW_self64]
      rfl
    by_cases hi4 : i = 4
    · subst hi4
      rw [hm, Mem.readW_writeW_sep (addr_sep (by have := vl 4; omega) (by have := vl 0; omega) e04.symm)
        (by decide), Mem.readW_writeW_self64]
      rfl
    · rw [rm _ (by have := vl i; omega) (VG.Proof.Sha512.X86.vOff_sep t (by decide) (by omega) (Ne.symm hi0))
        (VG.Proof.Sha512.X86.vOff_sep t (by decide) (by omega) (Ne.symm hi4)), hI.vars i (by omega) hi0 hi4]
      rcases (by omega : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 6) with rfl | rfl | rfl | rfl <;> rfl
  · rw [VG.Proof.Sha512.X86.xr_succ t 0 (by decide), hT, hnext, roundKW_0, VG.Proof.Sha512.X86.round_word, bsig0_split, BitVec.and_comm,
      maj_xor]
    simp only [hv, BitVec.add_assoc]
    rw [BitVec.add_comm (Spec.Sha512.maj _ _ _)]
  · rw [VG.Proof.Sha512.X86.xr_succ t 1 (by decide), hNE, hnext, roundKW_4, BitVec.add_assoc, VG.Proof.Sha512.X86.round_word]
  · rw [VG.Proof.Sha512.X86.xr_succ t 2 (by decide), hAB, hnext, roundKW_1, roundKW_2]
  · rw [rm _ (by have := VG.Proof.Sha512.X86.wOff_lt j; omega) (.inl (VG.Proof.Sha512.X86.vw_sep t 0 j)) (.inl (VG.Proof.Sha512.X86.vw_sep t 4 j))]
    exact hI.win j hj hj'
  · rw [rm _ (by decide) (.inl (mv 0)) (.inl (mv 4))]
    exact hI.mir j hj hj' h0
  · rw [hg r h1, hI.gpr r h1 h2 h3]
  · rw [hrd, hI.rd]
  · rw [hwr, hI.wr]
  · rw [hm]
    exact VG.Proof.Sha512.X86.frame_writeW (VG.Proof.Sha512.X86.frame_writeW hI.frame fit (by have := vl 4; omega) _) fit
      (by have := vl 0; omega) _

/-! ## Two steps of the message schedule -/

/-- The words at `wOff j` and the next slot, `Wⱼ` and `Wⱼ₊₁`, both in the window. -/
theorem pair_words {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {u t : Nat}
    (c : VG.Proof.Sha512.X86.Ctx scr s) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ u t s) {j : Nat} (hj : j + 1 < max u 16) (hj' : u ≤ j + 16) :
    qword (s.mem.readW (addr scr (wOff j)) 128) 0 = W M j ∧
      qword (s.mem.readW (addr scr (wOff j)) 128) 1 = W M (j + 1) := by
  have fit := c.fit
  refine ⟨by rw [VG.Proof.Sha512.X86.qword_readW_0]; exact hI.win j (by omega) hj', ?_⟩
  rw [VG.Proof.Sha512.X86.qword_readW_1 _ (by have := VG.Proof.Sha512.X86.wOff_pair j; omega)]
  by_cases h15 : j % 16 = 15
  · rw [VG.Proof.Sha512.X86.wOff_last h15]; exact hI.mir (j + 1) hj (by omega) (by omega)
  · rw [VG.Proof.Sha512.X86.wOff_next h15]; exact hI.win (j + 1) hj (by omega)

theorem schedule_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c : VG.Proof.Sha512.X86.Ctx scr s) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ t t s) (h16 : 16 ≤ t) (hev : t % 2 = 0) :
    WP isa (.block (schedule t)) s (VG.Proof.Sha512.X86.RInv scr H M s₀ (t + 2) t) := by
  have fit := c.fit
  have w' : ∀ j, wOff j + 16 ≤ 224 := fun j => by have := VG.Proof.Sha512.X86.wOff_pair j; omega
  rw [schedule, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.X86.scheduleW_ok _ _ _ _ _ _ (VG.Proof.Sha512.X86.xr_nodup_sched t) s (c.inp (w' _) (by decide))
    (c.inp (w' _) (by decide)) (c.inp (w' _) (by decide)) (c.inp (w' _) (by decide))
    (c.out (w' _) (by decide))) fun s' ⟨hx, hP, hg, hm, hrd, hwr⟩ => ?_
  simp only [c.esi] at hm hP
  -- The four pairs of words it reads.
  have p : ∀ i, 1 ≤ i → i ≤ 16 → i ≠ 1 →
      qword (s.mem.readW (addr scr (wOff (t + 16 - i))) 128) 0 = W M (t - i) ∧
      qword (s.mem.readW (addr scr (wOff (t + 16 - i))) 128) 1 = W M (t - i + 1) := fun i hi hi' h1 => by
    rw [show wOff (t + 16 - i) = wOff (t - i) by simp only [wOff]; omega]
    exact VG.Proof.Sha512.X86.pair_words c hI (by omega) (by omega)
  obtain ⟨a2, b2⟩ := p 2 (by omega) (by omega) (by omega)
  obtain ⟨a7, b7⟩ := p 7 (by omega) (by omega) (by omega)
  obtain ⟨a15, b15⟩ := p 15 (by omega) (by omega) (by omega)
  obtain ⟨a16, b16⟩ := p 16 (by omega) (by omega) (by omega)
  rw [show t + 16 - 2 = t + 14 by omega] at a2 b2
  rw [show t + 16 - 7 = t + 9 by omega] at a7 b7
  rw [show t + 16 - 15 = t + 1 by omega] at a15 b15
  rw [show t + 16 - 16 = t by omega] at a16 b16
  have W0 : W M t = VG.Proof.Sha512.X86.schedOf (W M (t - 2)) (W M (t - 7)) (W M (t - 15)) (W M (t - 16)) := by
    rw [VG.Proof.Sha512.X86.schedOf, ssig1_chain, ssig0_chain, ← W_ge M h16]
  have W1 : W M (t + 1) =
      VG.Proof.Sha512.X86.schedOf (W M (t - 2 + 1)) (W M (t - 7 + 1)) (W M (t - 15 + 1)) (W M (t - 16 + 1)) := by
    rw [VG.Proof.Sha512.X86.schedOf, ssig1_chain, ssig0_chain, show t - 2 + 1 = t + 1 - 2 by omega,
      show t - 7 + 1 = t + 1 - 7 by omega, show t - 15 + 1 = t + 1 - 15 by omega,
      show t - 16 + 1 = t + 1 - 16 by omega, ← W_ge M (by omega)]
  rw [a2, b2, a7, b7, a15, b15, a16, b16, ← W0, ← W1] at hm hP
  have tl : t % 16 ≠ 15 := by omega
  -- The memory after the 16-byte store, and the copy of `Wₜ`.
  have rm : ∀ o, o + 8 ≤ 224 → (wOff t + 16 ≤ o ∨ o + 8 ≤ wOff t) →
      s'.mem.readW (addr scr o) 64 = s.mem.readW (addr scr o) 64 :=
    fun o ho h => by rw [hm, VG.Proof.Sha512.X86.readW64_write128_ne _ _ (by have := w' t; omega) (by omega) h]
  have r0 : s'.mem.readW (addr scr (wOff t)) 64 = W M t := by
    have e := VG.Proof.Sha512.X86.readW_writeW128_q s.mem (addr scr (wOff t)) (W M (t + 1) ++ W M t) (j := 0) (by decide)
    rw [VG.Proof.Sha512.X86.addr_add0] at e
    rw [hm, e, VG.Proof.Sha512.X86.qword_append_0]
  have r1 : s'.mem.readW (addr scr (wOff (t + 1))) 64 = W M (t + 1) := by
    rw [hm, ← VG.Proof.Sha512.X86.wOff_next tl, ← VG.Proof.Sha512.X86.addr_add8 (by have := w' t; omega), VG.Proof.Sha512.X86.readW_writeW128_q _ _ _ (by decide),
      VG.Proof.Sha512.X86.qword_append_1]
  have xk : ∀ k < 3, s'.xmm (xr t k) = s.xmm (xr t k) := fun k hk => by
    obtain ⟨n3, n4, nx, ny⟩ := VG.Proof.Sha512.X86.xr_sched_ne t k hk
    exact hx _ n3 n4 nx ny
  have mw : ∀ j, wOff j + 8 ≤ mirOff := fun j => by simp only [wOff, mirOff]; omega
  have mv : ∀ k, vOff t k + 8 ≤ wOff t := fun k => VG.Proof.Sha512.X86.vw_sep t k t
  -- The window after the store, but the copy.
  have win' : ∀ j, j < max (t + 2) 16 → t + 2 ≤ j + 16 → s'.mem.readW (addr scr (wOff j)) 64 = W M j :=
    fun j hj hj' => by
    by_cases hjt : j = t
    · subst hjt; exact r0
    by_cases hjt1 : j = t + 1
    · subst hjt1; exact r1
    · rw [rm _ (by have := VG.Proof.Sha512.X86.wOff_lt j; omega) (by simp only [wOff]; omega)]
      exact hI.win j (by omega) (by omega)
  -- The copy is stored only if `t mod 16 = 0`.
  split
  · rename_i h0
    refine WP.of_runBlock ?_
    have o := c.out (o := mirOff) (n := 8) (by decide) (by decide)
    simp only [stq, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store64, VG.Proof.Sha512.X86.ea_at, hg,
      show s'.wr = s.wr from hwr, o, ↓reduceIte, hP, VG.Proof.Sha512.X86.extractLsb'_qword, VG.Proof.Sha512.X86.qword_append_0,
      Option.some.injEq, exists_eq_left']
    refine ⟨fun k hk h0' h4 => ?_, ?_, ?_, ?_, fun j hj hj' => ?_, fun j hj hj' hj0 => ?_,
      fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · simp only [c.esi]
      rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by simp only [mirOff]; omega) (by have := VG.Proof.Sha512.X86.vOff_lt t k; omega)
        (.inr (by have := mv k; have := mw t; omega)), rm _ (by have := VG.Proof.Sha512.X86.vOff_lt t k; omega) (.inr (mv k))]
      exact hI.vars k hk h0' h4
    · rw [xk 0 (by decide)]; exact hI.xa
    · rw [xk 1 (by decide)]; exact hI.xe
    · rw [xk 2 (by decide)]; exact hI.xbc
    · simp only [c.esi]
      rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by simp only [mirOff]; omega) (by have := VG.Proof.Sha512.X86.wOff_lt j; omega)
        (.inr (mw j))]
      exact win' j hj hj'
    · have : j = t := by omega
      subst this
      simp only [c.esi, Mem.readW_writeW_self64]
    · exact hI.gpr r h1 h2 h3
    · exact hrd.trans hI.rd
    · exact hI.wr
    · simp only [c.esi]
      exact VG.Proof.Sha512.X86.frame_writeW (hm ▸ VG.Proof.Sha512.X86.frame_writeW16 hI.frame fit (by have := VG.Proof.Sha512.X86.wOff_pair t; omega) _) fit
        (by decide) _
  · rename_i h0
    refine WP.block_nil ⟨fun k hk h0' h4 => ?_, by rw [xk 0 (by decide)]; exact hI.xa,
      by rw [xk 1 (by decide)]; exact hI.xe, by rw [xk 2 (by decide)]; exact hI.xbc, win',
      fun j hj hj' hj0 => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [rm _ (by have := VG.Proof.Sha512.X86.vOff_lt t k; omega) (.inr (mv k))]
      exact hI.vars k hk h0' h4
    · rw [rm _ (by decide) (.inl (by simp only [wOff, mirOff]; omega))]
      exact hI.mir j (by omega) (by omega) hj0
    · rw [hg, hI.gpr r h1 h2 h3]
    · rw [hrd, hI.rd]
    · rw [hwr, hI.wr]
    · rw [hm]; exact VG.Proof.Sha512.X86.frame_writeW16 hI.frame fit (by have := VG.Proof.Sha512.X86.wOff_pair t; omega) _

/-! ## The rounds -/

/-- The window before step `t`: up to `Wₜ₋₁` (`Wₜ` too for odd `t`). -/
abbrev wEnd (t : Nat) : Nat := t + t % 2

theorem step_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State} {t : Nat}
    (c₀ : VG.Proof.Sha512.X86.Ctx scr s₀) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ (VG.Proof.Sha512.X86.wEnd t) t s) :
    WP isa (.block (VG.Impl.Sha512.X86.step t)) s (VG.Proof.Sha512.X86.RInv scr H M s₀ (VG.Proof.Sha512.X86.wEnd (t + 1)) (t + 1)) := by
  have c := c₀.of_rinv hI
  simp only [VG.Proof.Sha512.X86.wEnd] at hI ⊢
  unfold VG.Impl.Sha512.X86.step
  by_cases h16 : t < 16 ∨ t % 2 = 1
  · simp only [h16, ↓reduceIte]
    rcases h16 with h16 | hodd
    · exact WP.mono (VG.Proof.Sha512.X86.round_ok c (hI.early (u' := 0) (by omega) (by omega)) (by omega) (by omega))
        fun s' h => h.early (by omega) (by omega)
    · rw [show t + 1 + (t + 1) % 2 = t + t % 2 by omega]
      exact VG.Proof.Sha512.X86.round_ok c hI (by omega) (by omega)
  · simp only [h16, ↓reduceIte]
    rw [WP.block_append_iff]
    rw [show t + t % 2 = t by omega] at hI
    rw [show t + 1 + (t + 1) % 2 = t + 2 by omega]
    exact WP.mono (VG.Proof.Sha512.X86.schedule_ok c hI (by omega) (by omega)) fun s' h =>
      VG.Proof.Sha512.X86.round_ok (c₀.of_rinv h) h (by omega) (by omega)

theorem rounds_ok {scr : BitVec 32} {H : HashValue} {M : Block} {s₀ s : State}
    (c₀ : VG.Proof.Sha512.X86.Ctx scr s₀) (hI : VG.Proof.Sha512.X86.RInv scr H M s₀ 0 0 s) :
    ∀ t, WP isa (rounds t) s (VG.Proof.Sha512.X86.RInv scr H M s₀ (VG.Proof.Sha512.X86.wEnd t) t) := by
  intro t
  induction t with
  | zero => exact WP.block_nil hI
  | succ t ih => exact WP.seq (WP.mono ih fun s' h => VG.Proof.Sha512.X86.step_ok c₀ h)

end VG.Proof.Sha512.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.X86.Lit`. -/
section

/-!
# SHA-512 on x86 (32-bit): the code as literals

The compression function is fully unrolled (6,500 instructions): its
literal (`materialize_code`) spares the kernel building the instructions in
every check that evaluates the code (constant time, `spSafe`), and the
streaming functions call it.
-/

namespace VG.Impl.Sha512.X86

materialize_code VG.Impl.Sha512.X86.compress
materialize_code Stream.update
materialize_code Stream.finalize

end VG.Impl.Sha512.X86

end

/- Proofs formerly in `VerifiedGarbage.Proof.Sha512.X86.Compress`. -/
section

/-!
# SHA-512 compression function on x86 (32-bit): the whole function
-/

/-!
## SHA-512: the x86 (32-bit) contracts

The contracts the proofs are written against; the artifacts are emitted with
the shared contracts of `Spec/`, which imply these (`Contract.Implies`). The
contracts of the x86 (32-bit) implementations of the compression function and
of the streaming functions (`init`, `update`, `finalize`; see
`VG.Spec.Sha512.Repr`), in terms of `Spec/Sha512.lean`, with the arguments on
the stack (cdecl).
-/

namespace VG.Proof.Sha512

open Spec.Sha512

open VG.X86 in
/-- x86 (32-bit) contract for
`vg_sha512_compress(state: *mut [u64; 8], blocks: *const [u8; 128], n: usize, scratch: *mut [u64; 28])`:
updates the hash value at `state` with the `n` 128-byte blocks at `blocks`.

The code may read the arguments (16 bytes above the return address) and
`blocks` (`128 * n` bytes), and read and write `state` (64 bytes) and
`scratch` (224 bytes, whose contents on exit are unspecified). The writable
buffers may not overlap each other, the blocks, the arguments or the return
address, and nothing may wrap around the end of the (32-bit) address space.
`esp` and the arguments (the pointers and `n`) are public; the hash value
and the blocks are secret. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 64⟩
    let blocks : Region := ⟨(arg s 1).setWidth 64, 128 * (arg s 2).toNat⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 224⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [blocks, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ blocks.Disjoint state ∧ blocks.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧ ret.Disjoint state ∧ ret.Disjoint scratch ∧
    (arg s 0).toNat + 64 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 128 * (arg s 2).toNat ≤ 2 ^ 32 ∧
    (arg s 3).toNat + 224 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' :=
    stateAt s'.mem ((arg s 0).setWidth 64) =
      compressBlocks (stateAt s.mem ((arg s 0).setWidth 64)) s.mem ((arg s 1).setWidth 64)
        (arg s 2).toNat
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧
    arg s₁ 0 = arg s₂ 0 ∧ arg s₁ 1 = arg s₂ 1 ∧ arg s₁ 2 = arg s₂ 2 ∧ arg s₁ 3 = arg s₂ 3

open VG.X86 in
/-- The 64-bit `count` argument of `update`/`finalize`, in argument slots 1
and 2 (cdecl: the low word first). -/
def countX86 (s : X86.State) : BitVec 64 := arg s 2 ++ arg s 1

open VG.X86 in
/-- x86 (32-bit) contract for `vg_<alg>_init(state: *mut [u8; 192])`, where
`iv` is the initial hash value of `<alg>`: makes the streaming state at
`state` represent the empty message, hashed from `iv`.

The code may read the argument (4 bytes above the return address) and write
`state` (192 bytes), which may not overlap the argument or the return
address; nothing may wrap around the end of the (32-bit) address space.
`esp` and the pointer are public. -/
def initX86 (iv : HashValue) : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let args : Region := ⟨argAddr s 0, 4⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [args] ∧ s.wr = [state] ∧ args.Disjoint state ∧ ret.Disjoint state ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (s.gpr .esp).toNat + 8 ≤ 2 ^ 32
  post s s' := Repr iv s'.mem ((arg s 0).setWidth 64) []
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ arg s₁ 0 = arg s₂ 0

open VG.X86 in
/-- x86 (32-bit) contract for
`vg_sha512_update(state: *mut [u8; 192], count: u64, data: *const u8, len: usize, scratch: *mut [u64; 34])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `data`, `len`, `scratch`): if the streaming state at `state`
represents a message `m` of `count` bytes (modulo 2⁶⁴), hashed from any
initial hash value, then afterwards it represents `m` followed by the `len`
bytes at `data`, from the same one.

The code may read the arguments (24 bytes above the return address) and
`data` (`len` bytes), and read and write `state` (192 bytes) and `scratch`
(272 bytes, whose contents on exit are unspecified). The writable buffers
may not overlap each other, the data or the arguments; none of the buffers
may overlap the return address or the 20 bytes of stack below it, where the
calls of the compression function store their arguments and return address;
nothing may wrap around the end of the (32-bit) address space. `esp`, the
pointers, `count` and `len` are public; the state and the data are secret. -/
def updateX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let data : Region := ⟨(arg s 3).setWidth 64, (arg s 4).toNat⟩
    let scratch : Region := ⟨(arg s 5).setWidth 64, 272⟩
    let args : Region := ⟨argAddr s 0, 24⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [data, args] ∧ s.wr = [state, scratch] ∧
    state.Disjoint scratch ∧ data.Disjoint state ∧ data.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint scratch ∧ stack.Disjoint state ∧ stack.Disjoint scratch ∧
    stack.Disjoint data ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + (arg s 4).toNat ≤ 2 ^ 32 ∧
    (arg s 5).toNat + 272 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 28 ≤ 2 ^ 32
  post s s' := ∀ iv m, Repr iv s.mem ((arg s 0).setWidth 64) m → VG.Proof.Sha512.countX86 s = BitVec.ofNat 64 m.length →
    Repr iv s'.mem ((arg s 0).setWidth 64)
      (m ++ bytesAt s.mem ((arg s 3).setWidth 64) (arg s 4).toNat)
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 6, arg s₁ i = arg s₂ i

open VG.X86 in
/-- x86 (32-bit) contract for
`vg_sha512_finalize(state: *mut [u8; 192], count: u64, out: *mut [u8; 64], scratch: *mut [u64; 34])`,
whose arguments are on the stack (cdecl: `state`, the low and high words of
`count`, `out`, `scratch`): if the streaming state at `state` represents a
message `m` of `count` bytes, fewer than 2⁶⁴, hashed from the initial hash
value `iv`, writes the final hash value `H⁽ᴺ⁾` of `m` from `iv` (64 bytes;
`finalHash iv m`) to `out`.

The code may read the arguments (20 bytes above the return address), and
read and write `state` (192 bytes, whose contents on exit are unspecified),
`out` (64 bytes) and `scratch` (272 bytes, whose contents on exit are
unspecified). These may not overlap each other or the arguments; none of
them may overlap the return address or the 20 bytes of stack below it; and
nothing may wrap around the end of the (32-bit) address space. `esp`, the
pointers and `count` are public; the state is secret. -/
def finalizeX86 : Contract X86.isa where
  pre s :=
    let state : Region := ⟨(arg s 0).setWidth 64, 192⟩
    let out : Region := ⟨(arg s 3).setWidth 64, 64⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 272⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 20, 20⟩
    s.rd = [args] ∧ s.wr = [state, out, scratch] ∧
    state.Disjoint out ∧ state.Disjoint scratch ∧ out.Disjoint scratch ∧
    args.Disjoint state ∧ args.Disjoint out ∧ args.Disjoint scratch ∧
    ret.Disjoint state ∧ ret.Disjoint out ∧ ret.Disjoint scratch ∧
    stack.Disjoint state ∧ stack.Disjoint out ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + 192 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 64 ≤ 2 ^ 32 ∧
    (arg s 4).toNat + 272 ≤ 2 ^ 32 ∧ 20 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post s s' := ∀ iv m, Repr iv s.mem ((arg s 0).setWidth 64) m → m.length < 2 ^ 64 →
    VG.Proof.Sha512.countX86 s = BitVec.ofNat 64 m.length →
    bytesAt s'.mem ((arg s 3).setWidth 64) 64 = finalHash iv m
  pub s₁ s₂ :=
    s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 5, arg s₁ i = arg s₂ i

end VG.Proof.Sha512


namespace VG.Proof.Sha512.X86

open VG VG.X86 VG.Impl.Sha512.X86
open VG.Spec.Sha512 (HashValue Word Block W stateAt blockAt compress compressBlocks parseBlock)
open VG.Proof.Sha256.X86.Stream (contains_addr sub_offset Upd Mupd wp_store wp_addi wp_subi)
open VG.Proof.Sha512.Word64 (readW64 lo_append hi_append)

/-! ## Memory -/

theorem cat44 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32) : BitVec 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- A store, which leaves the registers and the flags alone. -/
theorem wp_storeF {s : State} {is : List Instr} {Q : State → Prop} {m : MemOp} {r : Reg} {a : Addr}
    (ha : s.ea m = a) (hout : InRegions s.wr a 4)
    (k : WP isa (.block is) { s with mem := s.mem.writeW a (s.gpr r) } Q) :
    WP isa (.block (.store m r :: is)) s Q := by
  refine Proof.Sha256.X86.Stream.WP.cons ?_ k
  simp [exec, State.store32, ha, hout]

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (st.setWidth 64))[k] = VG.Proof.Sha512.X86.rd64 m st (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn, VG.Proof.Sha512.X86.rd64]
  rw [readW64, show st.setWidth 64 + BitVec.ofNat 64 (8 * k) + 4 =
      st.setWidth 64 + BitVec.ofNat 64 (8 * k + 4) from Offset.add_ofNat_add_ofNat _ _ 4,
    ← addr_eq (by bdd_omega), ← addr_eq (by bdd_omega)]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue}
    (h : ∀ k (hk : k < 8), VG.Proof.Sha512.X86.rd64 m st (8 * k) = H[k]) : stateAt m (st.setWidth 64) = H := by
  ext k hk
  rw [VG.Proof.Sha512.X86.stateAt_get hfit m hk, h k hk]

/-- The block at `bk`'s words, as `loadW` makes them from its bytes. -/
def Raw (bk : BitVec 32) (M : Block) (m : Mem) : Prop :=
  ∀ j < 16, bswap (m.readW (addr bk (8 * j)) 32) ++ bswap (m.readW (addr bk (8 * j + 4)) 32) = W M j

/-- `loadW` makes the block's words from its bytes. -/
theorem raw_block {bk : BitVec 32} (hfit : bk.toNat + 128 ≤ 2 ^ 32) (m : Mem) :
    VG.Proof.Sha512.X86.Raw bk (blockAt m (bk.setWidth 64)) m := by
  intro j hj
  rw [W_lt _ hj]
  simp only [blockAt, parseBlock]
  rw [addr_eq (by bdd_omega), addr_eq (by bdd_omega), bswap_readW, bswap_readW]
  simp only [VG.Proof.Sha512.X86.add_one', Nat.add_assoc]
  exact VG.Proof.Sha512.X86.cat44 _ _ _ _ _ _ _ _

theorem compressBlocks_succ (H : HashValue) (m : Mem) (p : Addr) (i : Nat) :
    compressBlocks H m p (i + 1) =
      compress (compressBlocks H m p i) (blockAt m (p + BitVec.ofNat 64 (128 * i))) := by
  simp [compressBlocks, List.range_succ, List.foldl_append]

namespace Compress

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev st : BitVec 32 := arg s₀ 0
abbrev bp : BitVec 32 := arg s₀ 1
abbrev nb : Nat := (arg s₀ 2).toNat
abbrev scr : BitVec 32 := arg s₀ 3
abbrev stR : Region := ⟨(VG.Proof.Sha512.X86.Compress.st s₀).setWidth 64, 64⟩
abbrev blR : Region := ⟨(VG.Proof.Sha512.X86.Compress.bp s₀).setWidth 64, 128 * VG.Proof.Sha512.X86.Compress.nb s₀⟩
abbrev scrR : Region := ⟨(VG.Proof.Sha512.X86.Compress.scr s₀).setWidth 64, 224⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(VG.Proof.Sha512.X86.Compress.esp₀ s₀).setWidth 64, 4⟩
abbrev H₀ : HashValue := stateAt s₀.mem ((VG.Proof.Sha512.X86.Compress.st s₀).setWidth 64)

/-- Where block `i` starts. -/
abbrev blkAddr (i : Nat) : BitVec 32 := VG.Proof.Sha512.X86.Compress.bp s₀ + BitVec.ofNat 32 (128 * i)

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [VG.Proof.Sha512.X86.Compress.blR s₀, VG.Proof.Sha512.X86.Compress.argR s₀]
  wr : s₀.wr = [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀]
  st_scr : (VG.Proof.Sha512.X86.Compress.stR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.scrR s₀)
  blk_st : (VG.Proof.Sha512.X86.Compress.blR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.stR s₀)
  blk_scr : (VG.Proof.Sha512.X86.Compress.blR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.scrR s₀)
  arg_st : (VG.Proof.Sha512.X86.Compress.argR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.stR s₀)
  arg_scr : (VG.Proof.Sha512.X86.Compress.argR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.scrR s₀)
  ret_st : (VG.Proof.Sha512.X86.Compress.retR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.stR s₀)
  ret_scr : (VG.Proof.Sha512.X86.Compress.retR s₀).Disjoint (VG.Proof.Sha512.X86.Compress.scrR s₀)
  st_fits : (VG.Proof.Sha512.X86.Compress.st s₀).toNat + 64 ≤ 2 ^ 32
  blk_fits : (VG.Proof.Sha512.X86.Compress.bp s₀).toNat + 128 * VG.Proof.Sha512.X86.Compress.nb s₀ ≤ 2 ^ 32
  scr_fits : (VG.Proof.Sha512.X86.Compress.scr s₀).toNat + 224 ≤ 2 ^ 32
  esp_fits : (VG.Proof.Sha512.X86.Compress.esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Sha512.compressX86.pre s₀) : VG.Proof.Sha512.X86.Compress.Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

namespace Pre
variable {s₀ : State} (h : VG.Proof.Sha512.X86.Compress.Pre s₀)
include h

theorem ctx {s : State} (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀) (hw : s.wr = s₀.wr) : VG.Proof.Sha512.X86.Ctx (VG.Proof.Sha512.X86.Compress.scr s₀) s :=
  ⟨hesi, h.scr_fits, by rw [hw, h.wr]; simp⟩

theorem accS {s : State} (hw : s.wr = s₀.wr) : VG.Proof.Sha512.X86.Acc s.wr (VG.Proof.Sha512.X86.Compress.st s₀) 64 :=
  Acc.of_mem (by rw [hw, h.wr]; simp) h.st_fits

theorem accV {s : State} (hw : s.wr = s₀.wr) : VG.Proof.Sha512.X86.Acc s.wr (VG.Proof.Sha512.X86.Compress.scr s₀) 224 :=
  Acc.of_mem (by rw [hw, h.wr]; simp) h.scr_fits

theorem in_st {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 64) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha512.X86.Compress.st s₀) d) 4 :=
  VG.Proof.Sha512.X86.mem_rd (h.accS hw d hd)

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 224) :
    InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 4 :=
  VG.Proof.Sha512.X86.mem_rd (h.accV hw d hd)

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) d = (VG.Proof.Sha512.X86.Compress.esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := h.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (VG.Proof.Sha512.X86.Compress.argR s₀).Contains (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) d) 4 := by
  show (⟨addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [h.argAddr_eq (by bdd_omega), h.argAddr_eq (by bdd_omega)]
  exact Offset.contains _ hd (by bdd_omega) (by bdd_omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 20) : InRegions (s.rd ++ s.wr) (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) d) 4 :=
  ⟨VG.Proof.Sha512.X86.Compress.argR s₀, by simp [hrd, h.rd], h.arg_contains hd hd'⟩

/-- An argument slot is inside the argument region. -/
theorem arg_sub {i : Nat} (hi : i < 4) : Region.Sub ⟨argAddr s₀ i, 4⟩ (VG.Proof.Sha512.X86.Compress.argR s₀) := by
  show Region.Sub ⟨addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) (4 + 4 * i), 4⟩ ⟨addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) 4, 16⟩
  rw [h.argAddr_eq (by bdd_omega), h.argAddr_eq (by bdd_omega)]
  exact Offset.sub _ (by bdd_omega) (by bdd_omega)

/-- The arguments are unchanged while only the state and the scratch buffer are written. -/
theorem arg_frame {m : Mem} (hf : Frame [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem m) {i : Nat} (hi : i < 4) :
    m.readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) (4 + 4 * i)) 32 = arg s₀ i := by
  refine (hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) ?_ (by decide))
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.arg_st.sub_left (h.arg_sub hi), h.arg_scr.sub_left (h.arg_sub hi)⟩

theorem blk_toNat {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) : (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).toNat = (VG.Proof.Sha512.X86.Compress.bp s₀).toNat + 128 * i := by
  have := h.blk_fits
  simp only [VG.Proof.Sha512.X86.Compress.blkAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 128 * i) (by bdd_omega), Nat.mod_eq_of_lt (by bdd_omega)]

theorem blk_fit {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) : (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).toNat + 128 ≤ 2 ^ 32 := by
  have := h.blk_fits; rw [h.blk_toNat hi]; omega

theorem blk_addr {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) :
    (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).setWidth 64 = (VG.Proof.Sha512.X86.Compress.bp s₀).setWidth 64 + BitVec.ofNat 64 (128 * i) :=
  addr_eq (x := VG.Proof.Sha512.X86.Compress.bp s₀) (k := 128 * i) (by have := h.blk_fits; omega)

theorem blk_sub {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) : Region.Sub ⟨(VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).setWidth 64, 128⟩ (VG.Proof.Sha512.X86.Compress.blR s₀) := by
  have := h.blk_fits
  rw [h.blk_addr hi]; exact sub_offset (by bdd_omega) (by bdd_omega)

theorem blk_rd {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) {o : Nat} (ho : o + 4 ≤ 128) :
    InRegions (s₀.rd ++ s₀.wr) (addr (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i) o) 4 := by
  refine ⟨VG.Proof.Sha512.X86.Compress.blR s₀, by simp [h.rd], ?_⟩
  rw [show addr (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i) o = addr (VG.Proof.Sha512.X86.Compress.bp s₀) (128 * i + o) by
    simp only [addr, VG.Proof.Sha512.X86.Compress.blkAddr, BitVec.add_assoc, BitVec.ofNat_add]]
  exact contains_addr (by have : i + 1 ≤ VG.Proof.Sha512.X86.Compress.nb s₀ := hi; omega) (by bdd_omega) h.blk_fits

theorem blk_disj {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) :
    ∀ r ∈ [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀], Region.Disjoint ⟨(VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).setWidth 64, 128⟩ r := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.blk_st.sub_left (h.blk_sub hi), h.blk_scr.sub_left (h.blk_sub hi)⟩

theorem st_work : (VG.Proof.Sha512.X86.Compress.stR s₀).Disjoint (VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)) :=
  h.st_scr.sub_right (Region.sub_prefix (by bdd_omega))

/-- The saved registers and the block count (at offsets `200 … 220` of the
scratch buffer) are unchanged while only the working variables and the
message schedule, or the hash value, are written. -/
theorem high_frame {m m' : Mem} (hf : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] m m' ∨ Frame [VG.Proof.Sha512.X86.Compress.stR s₀] m m') {d : Nat}
    (hd : 200 ≤ d) (hd' : d + 4 ≤ 224) : m'.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 = m.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 := by
  have hc : (⟨addr (VG.Proof.Sha512.X86.Compress.scr s₀) d, 4⟩ : Region).Contains (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) (32 / 8) :=
    Region.contains_self _ _
  have := h.scr_fits
  rcases hf with hf | hf
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    rw [addr_eq (by bdd_omega)]
    exact Offset.disjoint_base _ hd (by bdd_omega)
  · refine hf.readW hc ?_ (by decide)
    simp only [List.mem_singleton, forall_eq]
    refine Region.Disjoint.sub_left h.st_scr.symm ?_
    rw [addr_eq (by bdd_omega)]
    exact Offset.sub_base _ (by bdd_omega)
end Pre

/-! ## The loop invariant -/

/-- The callee-saved registers are saved in the scratch buffer. -/
def compressSaved : Spill.Slots := [(.ebx, 200), (.esi, 204), (.edi, 208), (.ebp, 212)]

theorem compressSaved_fits : Spill.Fits 216 VG.Proof.Sha512.X86.Compress.compressSaved := by decide

abbrev Saved (s₀ : State) (m : Mem) : Prop := Spill.Saved m (addr (VG.Proof.Sha512.X86.Compress.scr s₀)) s₀.gpr VG.Proof.Sha512.X86.Compress.compressSaved

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  esi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀
  esp : s.gpr .esp = VG.Proof.Sha512.X86.Compress.esp₀ s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem s.mem
  state : stateAt s.mem ((VG.Proof.Sha512.X86.Compress.st s₀).setWidth 64) =
    compressBlocks (VG.Proof.Sha512.X86.Compress.H₀ s₀) s₀.mem ((VG.Proof.Sha512.X86.Compress.bp s₀).setWidth 64) i
  saved : VG.Proof.Sha512.X86.Compress.Saved s₀ s.mem

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends VG.Proof.Sha512.X86.Compress.Common s₀ i s where
  edi : s.gpr .edi = VG.Proof.Sha512.X86.Compress.blkAddr s₀ i
  cnt : s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) cntOff) 32 = BitVec.ofNat 32 (VG.Proof.Sha512.X86.Compress.nb s₀ - i)

theorem saved_frame {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {m m' : Mem} (h : VG.Proof.Sha512.X86.Compress.Saved s₀ m)
    (hf : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] m m' ∨ Frame [VG.Proof.Sha512.X86.Compress.stR s₀] m m') : VG.Proof.Sha512.X86.Compress.Saved s₀ m' :=
  h.of_readW fun p hp' => hp.high_frame hf (by revert p hp'; decide) (by have := compressSaved_fits.1 p hp'; omega)

/-! ## Loading the working variables and the message -/

theorem xr_0_0 : xr 0 0 = .xmm0 := rfl
theorem xr_0_1 : xr 0 1 = .xmm1 := rfl
theorem xr_0_2 : xr 0 2 = .xmm2 := rfl
theorem xr_80_0 : xr 80 0 = .xmm0 := rfl
theorem xr_80_1 : xr 80 1 = .xmm1 := rfl

section
variable {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀)
include hp

theorem in_st8 {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 8 ≤ 64) :
    InRegions s.wr (addr (VG.Proof.Sha512.X86.Compress.st s₀) d) 8 :=
  ⟨VG.Proof.Sha512.X86.Compress.stR s₀, by simp [hw, hp.wr], contains_addr hd (by decide) hp.st_fits⟩

theorem in_scr8 {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 8 ≤ 224) :
    InRegions s.wr (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 8 :=
  ⟨VG.Proof.Sha512.X86.Compress.scrR s₀, by simp [hw, hp.wr], contains_addr hd (by decide) hp.scr_fits⟩

theorem loadH_ok (k : Nat) (hk : k < 8) {s : State} (hecx : s.gpr .ecx = VG.Proof.Sha512.X86.Compress.st s₀)
    (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (loadH k)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) (s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64) := by
  have hi := VG.Proof.Sha512.X86.mem_rd (VG.Proof.Sha512.X86.Compress.in_st8 hp hwr (d := 8 * k) (by omega))
  have ho := VG.Proof.Sha512.X86.Compress.in_scr8 hp hwr (d := 8 * k) (by omega)
  apply WP.of_runBlock
  simp only [loadH, ldq, stq, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.load64,
    State.store64, VG.Proof.Sha512.X86.ea_at, hecx, hesi, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, VG.Proof.Sha512.X86.extractLsb'_qword, VG.Proof.Sha512.X86.qword_append_0, hi, ho, ↓reduceIte,
    Option.map_some]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

/-- After copying words `0 … n-1` of the hash value to the working variables. -/
structure LdInv (s : State) (n : Nat) (s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  vars : ∀ k < n, s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 = s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64
  frame : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] s.mem s'.mem

theorem loadHs_ok {s : State} (hecx : s.gpr .ecx = VG.Proof.Sha512.X86.Compress.st s₀) (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀)
    (hwr : s.wr = s₀.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap loadH)) s (VG.Proof.Sha512.X86.Compress.LdInv (s₀ := s₀) s n) := by
  intro n hn
  have fS := hp.st_fits
  have fV := hp.scr_fits
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, fun _ h => absurd h (by bdd_omega), Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by bdd_omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (VG.Proof.Sha512.X86.Compress.loadH_ok hp n (by bdd_omega) (by rw [h₁.gpr, hecx]) (by rw [h₁.gpr, hesi])
      (by rw [h₁.wr, hwr])) fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ =>
      ⟨by rw [g₂, h₁.gpr], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr], fun k hk => ?_, ?_⟩
    · have eS : s₁.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * n)) 64 = s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * n)) 64 :=
        h₁.frame.readW (contains_addr (by bdd_omega) (by decide) fS)
          (fun r hr => by simp at hr; subst hr; exact hp.st_work) (by decide)
      rw [m₂]
      by_cases hkn : k = n
      · subst hkn
        rw [Mem.readW_writeW_self64, eS]
      · rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
        exact h₁.vars k (by bdd_omega)
    · rw [m₂]
      exact VG.Proof.Sha512.X86.frame_writeW h₁.frame fV (by bdd_omega) _

/-- After making words `0 … n-1` of the message schedule. -/
structure WInv (s : State) (M : Block) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ≠ .ecx → r ≠ .edx → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  win : ∀ j < n, s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (wOff j)) 64 = W M j
  low : ∀ o, o + 8 ≤ 64 → s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) o) 64 = s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) o) 64
  frame : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] s.mem s'.mem

theorem loadWs_ok {s : State} {bk : BitVec 32} {M : Block} (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀)
    (hwr : s.wr = s₀.wr) (hedi : s.gpr .edi = bk) (fitB : bk.toNat + 128 ≤ 2 ^ 32)
    (disj : Region.Disjoint ⟨bk.setWidth 64, 128⟩ (VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)))
    (hrd : ∀ o, o + 4 ≤ 128 → InRegions (s.rd ++ s.wr) (addr bk o) 4) (hM : VG.Proof.Sha512.X86.Raw bk M s.mem) :
    ∀ n ≤ 16, WP isa (.block ((List.range n).flatMap fun t => loadW (8 * t) (wOff t))) s
      (VG.Proof.Sha512.X86.Compress.WInv (s₀ := s₀) s M n) := by
  intro n hn
  have fV := hp.scr_fits
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ _ => rfl, rfl, rfl, fun _ h => absurd h (by bdd_omega),
      fun _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by bdd_omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [← List.append_nil (loadW _ _)]
    have rdB : ∀ o, o + 4 ≤ 128 → s₁.mem.readW (addr bk o) 32 = s.mem.readW (addr bk o) 32 :=
      fun o ho => h₁.frame.readW (contains_addr ho (by decide) fitB)
        (fun r hr => by simp at hr; subst hr; exact disj) (by decide)
    have wl := VG.Proof.Sha512.X86.wOff_lt n
    refine VG.Proof.Sha512.X86.wp_loadW (N := 224) (by bdd_omega) (by rw [h₁.wr, hwr]; exact hp.accV rfl)
      (by rw [h₁.gpr _ (by decide) (by decide), hesi]) (by rw [h₁.gpr _ (by decide) (by decide), hedi])
      (by rw [h₁.rd, h₁.wr]; exact hrd _ (by bdd_omega)) (by rw [h₁.rd, h₁.wr]; exact hrd _ (by bdd_omega))
      fun s₂ w₂ => WP.block_nil ?_
    rw [rdB _ (by bdd_omega), rdB _ (by bdd_omega), hM n (by bdd_omega)] at w₂
    refine ⟨fun r h1 h2 => ?_, by rw [w₂.rd, h₁.rd], by rw [w₂.wr, h₁.wr], fun j hj => ?_,
      fun o ho => ?_, ?_⟩
    · rw [w₂.gpr r (by simp [Z0, Z1, h1, h2]), h₁.gpr r h1 h2]
    · have := VG.Proof.Sha512.X86.wOff_lt j
      rw [w₂.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega)]
      by_cases hjn : j = n
      · subst hjn; rw [VG.Proof.Sha512.X86.rd64_write64_self _ _ (by bdd_omega)]
      · rw [VG.Proof.Sha512.X86.rd64_write64_ne _ _ (by bdd_omega) (by bdd_omega) (VG.Proof.Sha512.X86.wOff_sep (by bdd_omega)),
          VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega)]
        exact h₁.win j (by bdd_omega)
    · rw [w₂.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega), VG.Proof.Sha512.X86.rd64_write64_ne _ _ (by bdd_omega) (by bdd_omega)
        (.inr (by simp only [wOff]; omega)), VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega)]
      exact h₁.low o ho
    · rw [w₂.mem]
      exact VG.Proof.Sha512.X86.frame_write64 (N := 200) h₁.frame (by simp) (by bdd_omega) (by omega) _

/-- The block's sixteen words, and the copy of `W₀` after the window. -/
theorem loadWsMir_ok {s : State} {bk : BitVec 32} {M : Block} (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀)
    (hwr : s.wr = s₀.wr) (hedi : s.gpr .edi = bk) (fitB : bk.toNat + 128 ≤ 2 ^ 32)
    (disj : Region.Disjoint ⟨bk.setWidth 64, 128⟩ (VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)))
    (hrd : ∀ o, o + 4 ≤ 128 → InRegions (s.rd ++ s.wr) (addr bk o) 4) (hM : VG.Proof.Sha512.X86.Raw bk M s.mem) :
    WP isa (.block loadWs) s fun s' =>
      VG.Proof.Sha512.X86.Compress.WInv (s₀ := s₀) s M 16 s' ∧ s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) mirOff) 64 = W M 0 := by
  have fV := hp.scr_fits
  rw [loadWs, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.X86.Compress.loadWs_ok hp hesi hwr hedi fitB disj hrd hM 16 (Nat.le_refl _)) fun s₁ h₁ => ?_
  rw [← List.append_nil (loadW _ _)]
  have rdB : ∀ o, o + 4 ≤ 128 → s₁.mem.readW (addr bk o) 32 = s.mem.readW (addr bk o) 32 :=
    fun o ho => h₁.frame.readW (contains_addr ho (by decide) fitB)
      (fun r hr => by simp at hr; subst hr; exact disj) (by decide)
  refine VG.Proof.Sha512.X86.wp_loadW (N := 224) (o := mirOff) (by decide) (by rw [h₁.wr, hwr]; exact hp.accV rfl)
    (by rw [h₁.gpr _ (by decide) (by decide), hesi]) (by rw [h₁.gpr _ (by decide) (by decide), hedi])
    (by rw [h₁.rd, h₁.wr]; exact hrd _ (by bdd_omega)) (by rw [h₁.rd, h₁.wr]; exact hrd _ (by bdd_omega))
    fun s₂ w₂ => WP.block_nil ?_
  rw [rdB _ (by bdd_omega), rdB _ (by bdd_omega), show (0 : Nat) + 4 = 8 * 0 + 4 from rfl,
    show (0 : Nat) = 8 * 0 from rfl, hM 0 (by decide)] at w₂
  have mw : ∀ j, wOff j + 8 ≤ mirOff := fun j => by simp only [wOff, mirOff]; omega
  refine ⟨⟨fun r h1 h2 => ?_, by rw [w₂.rd, h₁.rd], by rw [w₂.wr, h₁.wr], fun j hj => ?_,
    fun o ho => ?_, ?_⟩, ?_⟩
  · rw [w₂.gpr r (by simp [Z0, Z1, h1, h2]), h₁.gpr r h1 h2]
  · have := VG.Proof.Sha512.X86.wOff_lt j
    rw [w₂.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega), VG.Proof.Sha512.X86.rd64_write64_ne _ _ (by simp only [mirOff]; omega)
      (by bdd_omega) (.inr (mw j)), VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega)]
    exact h₁.win j hj
  · rw [w₂.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega), VG.Proof.Sha512.X86.rd64_write64_ne _ _ (by simp only [mirOff]; omega)
      (by bdd_omega) (.inr (by simp only [mirOff]; omega)), VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega)]
    exact h₁.low o ho
  · rw [w₂.mem]
    exact h₁.frame.trans (VG.Proof.Sha512.X86.frame_write64 (N := 200) (Frame.refl _ _) (by simp) (by bdd_omega) (by decide) _)
  · rw [w₂.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by simp only [mirOff]; omega), VG.Proof.Sha512.X86.rd64_write64_self _ _ (by simp only [mirOff]; omega)]

theorem enter_ok {s : State} {H : HashValue} (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀) (hwr : s.wr = s₀.wr)
    (hv : ∀ k (hk : k < 8), s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 = H[k]) :
    WP isa (.block enter) s fun s' =>
      qword (s'.xmm (xr 0 0)) 0 = H[0] ∧ qword (s'.xmm (xr 0 1)) 0 = H[4] ∧
      qword (s'.xmm (xr 0 2)) 0 = H[1] ^^^ H[2] ∧ s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  have i : ∀ k < 8, InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) (8 * k)) 8 := fun k hk => by
    rw [hesi]; exact VG.Proof.Sha512.X86.mem_rd (VG.Proof.Sha512.X86.Compress.in_scr8 hp hwr (by omega))
  have i0 := i 0 (by decide); have i1 := i 1 (by decide); have i2 := i 2 (by decide)
  have i4 := i 4 (by decide)
  have v0 := hv 0 (by decide); have v1 := hv 1 (by decide); have v2 := hv 2 (by decide)
  have v4 := hv 4 (by decide)
  simp only [Nat.mul_zero, Nat.reduceMul] at i0 i1 i2 i4 v0 v1 v2 v4
  rw [← hesi] at v0 v1 v2 v4
  apply WP.of_runBlock
  simp only [enter, VG.Proof.Sha512.X86.Compress.xr_0_0, VG.Proof.Sha512.X86.Compress.xr_0_1, VG.Proof.Sha512.X86.Compress.xr_0_2, ldq, xb, X, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, isa, State.load64, VG.Proof.Sha512.X86.ea_at, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm, VG.Proof.Sha512.X86.qword_append_0, VG.Proof.Sha512.X86.q_pxor, i0, i1, i2,
    i4, v0, v1, v2, v4, reduceCtorEq, ↓reduceIte, Option.map_some, and_self, Option.some.injEq,
    exists_eq_left']


/-! ## Adding them into the hash value -/

theorem exit_ok {s : State} (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block exit) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = (s.mem.writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) 0) (qword (s.xmm (xr 80 0)) 0)).writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) 32)
        (qword (s.xmm (xr 80 1)) 0) := by
  have o0 := VG.Proof.Sha512.X86.Compress.in_scr8 hp hwr (d := 0) (by decide)
  have o4 := VG.Proof.Sha512.X86.Compress.in_scr8 hp hwr (d := 32) (by decide)
  rw [← hesi] at o0 o4
  apply WP.of_runBlock
  simp only [exit, VG.Proof.Sha512.X86.Compress.xr_80_0, VG.Proof.Sha512.X86.Compress.xr_80_1, stq, runBlock_cons, runStep_some, runBlock_nil, exec, isa,
    State.store64, VG.Proof.Sha512.X86.ea_at, VG.Proof.Sha512.X86.extractLsb'_qword, o0, o4, ↓reduceIte]
  rw [hesi]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

theorem addH_ok (k : Nat) (hk : k < 8) {s : State} (hecx : s.gpr .ecx = VG.Proof.Sha512.X86.Compress.st s₀)
    (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀) (hwr : s.wr = s₀.wr) :
    WP isa (.block (addH k)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.mem = s.mem.writeW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k))
        (s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 + s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64) := by
  have hi := VG.Proof.Sha512.X86.mem_rd (VG.Proof.Sha512.X86.Compress.in_scr8 hp hwr (d := 8 * k) (by omega))
  have hs := VG.Proof.Sha512.X86.Compress.in_st8 hp hwr (d := 8 * k) (by omega)
  have hs' := VG.Proof.Sha512.X86.mem_rd hs
  apply WP.of_runBlock
  simp only [addH, ldq, stq, xb, X, Y, runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec, isa,
    State.load64, State.store64, VG.Proof.Sha512.X86.ea_at, hecx, hesi, RegUpd.gpr_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.mem_setXmm, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, VG.Proof.Sha512.X86.extractLsb'_qword, VG.Proof.Sha512.X86.qword_append_0,
    VG.Proof.Sha512.X86.q_paddq, hi, hs, hs', reduceCtorEq, not_false_eq_true, ↓reduceIte, Option.map_some]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

structure UInv (s : State) (n : Nat) (s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  done : ∀ k < n, s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64 =
    s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 + s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64
  todo : ∀ k, n ≤ k → k < 8 →
    s'.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64 = s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k)) 64
  frame : Frame [VG.Proof.Sha512.X86.Compress.stR s₀] s.mem s'.mem

theorem addHs_ok {s : State} (hecx : s.gpr .ecx = VG.Proof.Sha512.X86.Compress.st s₀) (hesi : s.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀)
    (hwr : s.wr = s₀.wr) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap addH)) s (VG.Proof.Sha512.X86.Compress.UInv (s₀ := s₀) s n) := by
  intro n hn
  have fS := hp.st_fits
  induction n with
  | zero => exact WP.block_nil ⟨rfl, rfl, rfl, fun _ h => absurd h (by bdd_omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by bdd_omega)) fun s₁ h₁ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    refine WP.mono (VG.Proof.Sha512.X86.Compress.addH_ok hp n (by bdd_omega) (by rw [h₁.gpr, hecx]) (by rw [h₁.gpr, hesi])
      (by rw [h₁.wr, hwr])) fun s₂ ⟨g₂, rd₂, wr₂, m₂⟩ =>
      ⟨by rw [g₂, h₁.gpr], by rw [rd₂, h₁.rd], by rw [wr₂, h₁.wr], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [m₂]
      by_cases hkn : k = n
      · subst hkn
        rw [Mem.readW_writeW_self64, h₁.todo k (by bdd_omega) (by bdd_omega),
          h₁.frame.readW (contains_addr (by bdd_omega) (by decide) hp.scr_fits)
            (fun r hr => by simp at hr; subst hr; exact hp.st_scr.symm) (by decide)]
      · rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
        exact h₁.done k (by bdd_omega)
    · rw [m₂, VG.Proof.Sha512.X86.readW64_write_ne _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
      exact h₁.todo k (by bdd_omega) hk'
    · rw [m₂]
      exact h₁.frame.writeW (by simp) _ (contains_addr (by bdd_omega) (by decide) fS)

end

/-! ## One block -/

theorem first_eq : load ++ loadWs ++ enter =
    .mov .ecx (.mem ⟨.esp, 4⟩) :: ((List.range 8).flatMap loadH ++ (loadWs ++ enter)) := rfl

theorem last_eq : exit ++ update ++ advance =
    exit ++ .mov .ecx (.mem ⟨.esp, 4⟩) :: ((List.range 8).flatMap addH ++ advance) := rfl

theorem harg_of {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {m : Mem} (hf : Frame [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem m) :
    m.readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) 4) 32 = VG.Proof.Sha512.X86.Compress.st s₀ :=
  hp.arg_frame hf (i := 0) (by decide)

theorem movArg_ok {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {s : State} {d : Reg} (hesp : s.gpr .esp = VG.Proof.Sha512.X86.Compress.esp₀ s₀)
    (hrd : s.rd = s₀.rd) {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (s.mem.readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) 4) 32) → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (.mem ⟨.esp, 4⟩) :: is)) s Q :=
  VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem (b := .esp) (d := 4) hesp (hp.in_arg hrd (by bdd_omega) (by bdd_omega))) k

theorem advance_ok {s : State} {Q : State → Prop} {B : BitVec 32} (hesi : s.gpr .esi = B)
    (hA : VG.Proof.Sha512.X86.Acc s.wr B 224)
    (k : ∀ s', s'.gpr .edi = s.gpr .edi + 128 →
      s'.zf = some (s.mem.readW (addr B cntOff) 32 - 1 == 0) →
      (∀ r, r ≠ .edi → r ≠ T → s'.gpr r = s.gpr r) →
      s'.mem = s.mem.writeW (addr B cntOff) (s.mem.readW (addr B cntOff) 32 - 1) → s'.rd = s.rd →
      s'.wr = s.wr → Q s') :
    WP isa (.block advance) s Q := by
  unfold advance
  refine wp_addi fun s₁ u₁ => ?_
  refine VG.Proof.Sha512.X86.wp_movS (VG.Proof.Sha512.X86.readSrc_mem (b := .esi) (d := cntOff) (by rw [u₁.other _ (by decide), hesi])
    (by rw [u₁.rd, u₁.wr]; exact VG.Proof.Sha512.X86.mem_rd (hA _ (by decide)))) fun s₂ u₂ => wp_subi fun s₃ u₃ hz => ?_
  refine VG.Proof.Sha512.X86.wp_storeF (VG.Proof.Sha512.X86.ea_of (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
                                            hesi]) _) (by rw [u₃.wr, u₂.wr, u₁.wr]; exact hA _ (by decide)) (WP.block_nil ?_)
  refine k _ ?_ ?_ (fun r h1 h2 => ?_) ?_ ?_ ?_
  · show s₃.gpr .edi = _
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  · show s₃.zf = _
    rw [hz, u₂.gpr, u₁.mem]
  · show s₃.gpr r = _
    rw [u₃.other _ h2, u₂.other _ h2, u₁.other _ h1]
  · show s₃.mem.writeW _ (s₃.gpr T) = _
    rw [u₃.gpr, u₃.mem, u₂.gpr, u₂.mem, u₁.mem]
  · show s₃.rd = _
    rw [u₃.rd, u₂.rd, u₁.rd]
  · show s₃.wr = _
    rw [u₃.wr, u₂.wr, u₁.wr]

theorem body_ok {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {i : Nat} (hi : i < VG.Proof.Sha512.X86.Compress.nb s₀) {s : State}
    (hL : VG.Proof.Sha512.X86.Compress.LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ VG.Proof.Sha512.X86.Compress.Common s₀ (VG.Proof.Sha512.X86.Compress.nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < VG.Proof.Sha512.X86.Compress.nb s₀ ∧ VG.Proof.Sha512.X86.Compress.LInv s₀ (i + 1) s') := by
  have fitS := hp.st_fits
  have fitV := hp.scr_fits
  have fitB := hp.blk_fit hi
  set H := stateAt s.mem ((VG.Proof.Sha512.X86.Compress.st s₀).setWidth 64) with hH
  set M := blockAt s₀.mem ((VG.Proof.Sha512.X86.Compress.blkAddr s₀ i).setWidth 64) with hMdef
  have c₀ : VG.Proof.Sha512.X86.Ctx (VG.Proof.Sha512.X86.Compress.scr s₀) s := hp.ctx hL.esi hL.wr
  -- Load the working variables, the message and the registers.
  refine WP.seq ?_
  rw [VG.Proof.Sha512.X86.Compress.first_eq]
  refine VG.Proof.Sha512.X86.Compress.movArg_ok hp hL.esp hL.rd fun s₀' u₀ => ?_
  rw [VG.Proof.Sha512.X86.Compress.harg_of hp hL.frame] at u₀
  have esi₀ : s₀'.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ := by rw [u₀.other _ (by decide), hL.esi]
  have wr₀ : s₀'.wr = s₀.wr := by rw [u₀.wr, hL.wr]
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.X86.Compress.loadHs_ok hp u₀.gpr esi₀ wr₀ 8 (Nat.le_refl _)) fun s₁ h₁ => ?_
  rw [WP.block_append_iff]
  have hM : VG.Proof.Sha512.X86.Raw (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i) M s₁.mem := fun j hj => by
    have e : ∀ o, o + 4 ≤ 128 → s₁.mem.readW (addr (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i) o) 32 =
        s₀.mem.readW (addr (VG.Proof.Sha512.X86.Compress.blkAddr s₀ i) o) 32 := fun o ho => by
      rw [h₁.frame.readW (contains_addr ho (by decide) fitB)
          (fun r hr => by
            simp at hr; subst hr
            exact (hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by bdd_omega)))
          (by decide), u₀.mem,
        hL.frame.readW (contains_addr ho (by bdd_omega) fitB) (hp.blk_disj hi) (by decide)]
    rw [e _ (by bdd_omega), e _ (by bdd_omega)]
    exact VG.Proof.Sha512.X86.raw_block fitB s₀.mem j hj
  refine WP.mono (VG.Proof.Sha512.X86.Compress.loadWsMir_ok hp (by rw [h₁.gpr, esi₀]) (by rw [h₁.wr, wr₀])
    (by rw [h₁.gpr, u₀.other _ (by decide), hL.edi]) fitB
    ((hp.blk_scr.sub_left (hp.blk_sub hi)).sub_right (Region.sub_prefix (by bdd_omega)))
    (fun o ho => by rw [h₁.rd, h₁.wr, u₀.rd, u₀.wr, hL.rd, hL.wr]; exact hp.blk_rd hi ho) hM) fun s₂ ⟨h₂, mir₂⟩ => ?_
  have esi₂ : s₂.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ := by rw [h₂.gpr _ (by decide) (by decide), h₁.gpr, esi₀]
  have wr₂ : s₂.wr = s₀.wr := by rw [h₂.wr, h₁.wr, wr₀]
  have hv : ∀ k (hk : k < 8), s₂.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 = H[k] := fun k hk => by
    rw [h₂.low _ (by bdd_omega), h₁.vars k hk, u₀.mem, ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega),
      ← VG.Proof.Sha512.X86.stateAt_get fitS _ hk]
  refine WP.mono (VG.Proof.Sha512.X86.Compress.enter_ok hp esi₂ wr₂ hv) fun s₃ ⟨xa, xe, xbc, g₃, m₃, rd₃, wr₃⟩ => ?_
  have f₁ : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] s.mem s₁.mem := by rw [← u₀.mem]; exact h₁.frame
  have hI : VG.Proof.Sha512.X86.RInv (VG.Proof.Sha512.X86.Compress.scr s₀) H M s 0 0 s₃ := by
    refine ⟨fun k hk h0 h4 => ?_, by rw [Proof.Sha512.rounds_zero]; exact xa,
      by rw [Proof.Sha512.rounds_zero]; exact xe, by rw [Proof.Sha512.rounds_zero]; exact xbc,
      fun j hj _ => ?_, fun j hj _ hj0 => ?_, fun r h1 h2 h3 => ?_, ?_, ?_, ?_⟩
    · rw [m₃, show vOff 0 k = 8 * k by simp only [vOff]; omega, hv k hk, Proof.Sha512.rounds_zero]
    · rw [m₃]; exact h₂.win j (by omega)
    · rw [m₃, mir₂, show j = 0 by omega]
    · rw [g₃, h₂.gpr r h2 h3, h₁.gpr, u₀.other r h2]
    · rw [rd₃, h₂.rd, h₁.rd, u₀.rd]
    · rw [wr₃, h₂.wr, h₁.wr, u₀.wr]
    · rw [m₃]; exact f₁.trans h₂.frame
  -- The rounds.
  refine WP.seq (WP.mono (VG.Proof.Sha512.X86.rounds_ok c₀ hI 80) fun s₄ h₄ => ?_)
  have c₄ := c₀.of_rinv h₄
  -- Store `a` and `e`, update the hash value, and advance.
  rw [VG.Proof.Sha512.X86.Compress.last_eq, WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.X86.Compress.exit_ok hp c₄.esi (by rw [h₄.wr, hL.wr])) fun s₅ ⟨g₅, rd₅, wr₅, m₅⟩ => ?_
  have hrd₅ : s₅.rd = s₀.rd := by rw [rd₅, h₄.rd, hL.rd]
  have hwr₅ : s₅.wr = s₀.wr := by rw [wr₅, h₄.wr, hL.wr]
  have m₂ : Frame [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)] s.mem s₅.mem := by
    rw [m₅]; exact VG.Proof.Sha512.X86.frame_writeW (VG.Proof.Sha512.X86.frame_writeW h₄.frame fitV (by decide) _) fitV (by decide) _
  have sw : ∀ r ∈ [VG.Proof.Sha512.X86.workR (VG.Proof.Sha512.X86.Compress.scr s₀)], ∃ r' ∈ [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀], Region.Sub r r' :=
    fun r hr => ⟨VG.Proof.Sha512.X86.Compress.scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (by bdd_omega)⟩
  have hframe₂ : Frame [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem s₅.mem := hL.frame.trans (m₂.sub sw)
  have esi₅ : s₅.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ := by rw [g₅, c₄.esi]
  have hvars : ∀ k (hk : k < 8),
      s₅.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) (8 * k)) 64 = (Spec.Sha512.rounds H M 80)[k] := fun k hk => by
    rw [m₅]
    by_cases h4 : k = 4
    · subst h4; rw [Mem.readW_writeW_self64, h₄.xe]
    rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]
    by_cases h0 : k = 0
    · subst h0; rw [Nat.mul_zero, Mem.readW_writeW_self64, h₄.xa]
    rw [VG.Proof.Sha512.X86.readW64_write_ne _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega),
      show 8 * k = vOff 80 k by simp only [vOff]; omega]
    exact h₄.vars k hk h0 h4
  refine VG.Proof.Sha512.X86.Compress.movArg_ok hp (by rw [g₅, h₄.gpr _ (by decide) (by decide) (by decide), hL.esp]) hrd₅
    fun s₆ u₆ => ?_
  rw [VG.Proof.Sha512.X86.Compress.harg_of hp hframe₂] at u₆
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Sha512.X86.Compress.addHs_ok hp u₆.gpr (by rw [u₆.other _ (by decide), esi₅]) (by rw [u₆.wr, hwr₅]) 8
    (Nat.le_refl _)) fun s₇ h₇ => ?_
  have esi₇ : s₇.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ := by rw [h₇.gpr, u₆.other _ (by decide), esi₅]
  refine VG.Proof.Sha512.X86.Compress.advance_ok esi₇ (hp.accV (by rw [h₇.wr, u₆.wr, hwr₅])) fun s₈ edi₈ z₈ g₈ m₈ rd₈ wr₈ => ?_
  -- Registers
  have g : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → r ≠ .edi → s₈.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => by
      rw [g₈ r h4 h1, h₇.gpr, u₆.other r h2, g₅, h₄.gpr r h1 h2 h3]
  have hrd : s₈.rd = s₀.rd := by rw [rd₈, h₇.rd, u₆.rd, hrd₅]
  have hwr : s₈.wr = s₀.wr := by rw [wr₈, h₇.wr, u₆.wr, hwr₅]
  -- Memory
  have hcnt₇ : s₇.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) cntOff) 32 = BitVec.ofNat 32 (VG.Proof.Sha512.X86.Compress.nb s₀ - i) := by
    rw [hp.high_frame (.inr h₇.frame) (by decide) (by decide), u₆.mem,
      hp.high_frame (.inl m₂) (by decide) (by decide), hL.cnt]
  have hframe : Frame [VG.Proof.Sha512.X86.Compress.stR s₀, VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem s₈.mem := by
    rw [m₈]
    refine ((hframe₂.trans ?_).trans (h₇.frame.mono (by simp))).writeW (r := VG.Proof.Sha512.X86.Compress.scrR s₀) (by simp) _
      (contains_addr (by decide) (by bdd_omega) fitV)
    rw [u₆.mem]; exact Frame.refl _ _
  have hstate : stateAt s₈.mem ((VG.Proof.Sha512.X86.Compress.st s₀).setWidth 64) = compress H M := by
    have e8 : ∀ k < 8, VG.Proof.Sha512.X86.rd64 s₈.mem (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k) = VG.Proof.Sha512.X86.rd64 s₇.mem (VG.Proof.Sha512.X86.Compress.st s₀) (8 * k) := fun k hk => by
      rw [m₈]
      simp only [VG.Proof.Sha512.X86.rd64]
      rw [Mem.readW_writeW_sep (hp.st_scr.sep (contains_addr (by bdd_omega) (by bdd_omega) fitS)
          (contains_addr (by decide) (by bdd_omega) fitV)) (by decide),
        Mem.readW_writeW_sep (hp.st_scr.sep (contains_addr (by bdd_omega) (by bdd_omega) fitS)
          (contains_addr (by decide) (by bdd_omega) fitV)) (by decide)]
    refine VG.Proof.Sha512.X86.stateAt_ext fitS fun k hk => ?_
    rw [e8 k hk, VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega), h₇.done k hk, u₆.mem, hvars k hk,
      m₂.readW (contains_addr (by bdd_omega) (by decide) fitS)
        (fun r hr => by simp at hr; subst hr; exact hp.st_work) (by decide),
      ← VG.Proof.Sha512.X86.rd64_eq_readW _ (by bdd_omega), ← VG.Proof.Sha512.X86.stateAt_get fitS _ hk]
    simp only [Spec.Sha512.compress, Vector.getElem_zipWith]
    rfl
  have hsaved : VG.Proof.Sha512.X86.Compress.Saved s₀ s₈.mem := by
    have s₇' : VG.Proof.Sha512.X86.Compress.Saved s₀ s₇.mem := by
      refine VG.Proof.Sha512.X86.Compress.saved_frame hp ?_ (.inr h₇.frame)
      rw [u₆.mem]
      exact VG.Proof.Sha512.X86.Compress.saved_frame hp hL.saved (.inl m₂)
    have e : ∀ d, 200 ≤ d → d + 4 ≤ 216 →
        s₈.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 = s₇.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 := fun d h1 h2 => by
      rw [m₈]
      exact Mem.readW_writeW_sep (Proof.Sha256.X86.Stream.addr_sep (by bdd_omega) (by simp [cntOff]; omega)
        (by simp [cntOff]; omega)) (by decide)
    exact s₇'.of_readW fun p h => e _ (by revert p h; decide) (compressSaved_fits.1 p h)
  have hnb : VG.Proof.Sha512.X86.Compress.nb s₀ < 2 ^ 32 := (arg s₀ 2).isLt
  have hc1 : s₇.mem.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) cntOff) 32 - 1 = BitVec.ofNat 32 (VG.Proof.Sha512.X86.Compress.nb s₀ - (i + 1)) := by
    rw [hcnt₇, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.ofNat_sub_ofNat (by bdd_omega),
      Nat.sub_sub]
  have hcommon : VG.Proof.Sha512.X86.Compress.Common s₀ (i + 1) s₈ := by
    refine ⟨by rw [g _ (by decide) (by decide) (by decide) (by decide), hL.esi],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hL.esp], hrd, hwr, hframe, ?_, hsaved⟩
    rw [hstate, VG.Proof.Sha512.X86.compressBlocks_succ, ← hL.state, hMdef, hp.blk_addr hi]
  have hev : eval .ne s₈ = some (!(BitVec.ofNat 32 (VG.Proof.Sha512.X86.Compress.nb s₀ - (i + 1)) == 0)) := by
    rw [Proof.Sha256.X86.Stream.eval_ne, z₈, hc1]; rfl
  by_cases hlast : i + 1 = VG.Proof.Sha512.X86.Compress.nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : VG.Proof.Sha512.X86.Compress.nb s₀ - (i + 1) ≠ 0 := by bdd_omega
    have h0 : BitVec.ofNat 32 (VG.Proof.Sha512.X86.Compress.nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by bdd_omega)] at h'
      exact hne h'
    refine ⟨by rw [hev]; simpa using h0, by bdd_omega, { hcommon with edi := ?_, cnt := ?_ }⟩
    · rw [edi₈, h₇.gpr, u₆.other _ (by decide), g₅, h₄.gpr _ (by decide) (by decide) (by decide), hL.edi]
      simp only [VG.Proof.Sha512.X86.Compress.blkAddr]
      rw [BitVec.add_assoc, show (128 : BitVec _) = BitVec.ofNat _ 128 from rfl, BitVec.ofNat_add_ofNat]
      rfl
    · rw [m₈, Mem.readW_writeW_self32, hc1]

/-! ## Prologue and epilogue -/

theorem prologue_eq : prologue = .mov .eax (.mem ⟨.esp, 16⟩) :: (Spill.saveCode .eax VG.Proof.Sha512.X86.Compress.compressSaved ++
    ([.mov .esi (.reg .eax), .mov .edi (.mem ⟨.esp, 8⟩), .mov .eax (.mem ⟨.esp, 12⟩),
      .store ⟨.esi, 216⟩ .eax, .alu .test .eax (.reg .eax)] : List Instr)) := rfl

theorem epilogue_eq :
    epilogue = Spill.restoreCode .esi ([(.ebx, 200), (.edi, 208), (.ebp, 212)] ++ [(.esi, 204)]) ++ [] :=
  rfl

/-- Reading an argument after writing the scratch buffer. -/
theorem readW_writeW_scr_arg {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 224) (he : 4 ≤ e) (he' : e + 4 ≤ 20) :
    (m.writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) v).readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) e) 32 = m.readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) e) 32 :=
  Mem.readW_writeW_sep (hp.arg_scr.sep (hp.arg_contains he he')
    (contains_addr hd (by bdd_omega) hp.scr_fits)) (by decide)

theorem readW_writeW_scr {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) (m : Mem) (v : BitVec 32) {d e : Nat}
    (hd : d + 4 ≤ 224) (he : e + 4 ≤ 224) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    (m.writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) e) v).readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 = m.readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 32 :=
  Proof.Sha256.X86.Stream.readW_writeW_addr m v (by have := hp.scr_fits; omega)
    (by have := hp.scr_fits; omega) h

/-- The memory after the prologue. -/
def saveMem (s₀ : State) : Mem :=
  (Spill.saveMem s₀.mem (addr (VG.Proof.Sha512.X86.Compress.scr s₀)) s₀.gpr VG.Proof.Sha512.X86.Compress.compressSaved).writeW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) 216) (arg s₀ 2)

theorem compressSaved_contains {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) : ∀ p ∈ VG.Proof.Sha512.X86.Compress.compressSaved, (VG.Proof.Sha512.X86.Compress.scrR s₀).Contains (addr (VG.Proof.Sha512.X86.Compress.scr s₀) p.2) 4 :=
  fun p h => contains_addr (by have := compressSaved_fits.1 p h; omega) (by bdd_omega) hp.scr_fits

theorem save_ok {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) :
    WP isa (.block prologue) s₀ fun s₁ =>
      s₁.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ ∧ s₁.gpr .edi = VG.Proof.Sha512.X86.Compress.bp s₀ ∧ s₁.gpr .esp = VG.Proof.Sha512.X86.Compress.esp₀ s₀ ∧ s₁.rd = s₀.rd ∧
      s₁.wr = s₀.wr ∧ s₁.mem = VG.Proof.Sha512.X86.Compress.saveMem s₀ ∧ s₁.zf = some (arg s₀ 2 &&& arg s₀ 2 == 0) := by
  have harg : ∀ d, 4 ≤ d → d + 4 ≤ 20 → (Spill.saveMem s₀.mem (addr (VG.Proof.Sha512.X86.Compress.scr s₀)) s₀.gpr VG.Proof.Sha512.X86.Compress.compressSaved).readW
      (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) d) 32 = s₀.mem.readW (addr (VG.Proof.Sha512.X86.Compress.esp₀ s₀) d) 32 := fun d hd hd' =>
    Spill.saveMem_readW_of_sep _ _ (by decide) _ _ fun p h =>
      hp.arg_scr.sep (hp.arg_contains hd hd') (VG.Proof.Sha512.X86.Compress.compressSaved_contains hp p h)
  have hout : ∀ {s : State}, s.wr = s₀.wr → ∀ d, d + 4 ≤ 224 → InRegions s.wr (addr (VG.Proof.Sha512.X86.Compress.scr s₀) d) 4 :=
    fun hw => hp.accV hw
  rw [VG.Proof.Sha512.X86.Compress.prologue_eq]
  refine Wp.wp_ldm rfl (hp.in_arg (s := s₀) rfl (d := 16) (by bdd_omega) (by bdd_omega)) fun s₁ u₁ => ?_
  refine Spill.save_ok VG.Proof.Sha512.X86.Compress.compressSaved (fun p h => by
    rw [u₁.gpr]; exact hout u₁.wr _ (by have := compressSaved_fits.1 p h; omega)) fun s₂ u₂ => ?_
  have hm : s₂.mem = Spill.saveMem s₀.mem (addr (VG.Proof.Sha512.X86.Compress.scr s₀)) s₀.gpr VG.Proof.Sha512.X86.Compress.compressSaved := by
    rw [u₂.mem, u₁.gpr, u₁.mem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p h => u₁.other _ (by revert p h; decide)
  have hesp : s₂.gpr .esp = VG.Proof.Sha512.X86.Compress.esp₀ s₀ := by rw [u₂.gpr, u₁.other _ (by decide)]
  have hrd : s₂.rd = s₀.rd := by rw [u₂.rd, u₁.rd]
  have hwr : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr]
  refine Wp.wp_mov fun s₃ u₃ => ?_
  have hesi : s₃.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀ := by rw [u₃.gpr, u₂.gpr, u₁.gpr]; rfl
  refine Wp.wp_ldm (by rw [u₃.other _ (by decide), hesp])
    (hp.in_arg (by rw [u₃.rd, hrd]) (d := 8) (by bdd_omega) (by bdd_omega)) fun s₄ u₄ => ?_
  refine Wp.wp_ldm (by rw [u₄.other _ (by decide), u₃.other _ (by decide), hesp])
    (hp.in_arg (by rw [u₄.rd, u₃.rd, hrd]) (d := 12) (by bdd_omega) (by bdd_omega)) fun s₅ u₅ => ?_
  have h12 : s₅.gpr .eax = arg s₀ 2 := by
    rw [u₅.gpr, u₄.mem, u₃.mem, hm, harg _ (by bdd_omega) (by bdd_omega)]; rfl
  refine Wp.wp_stm (by rw [u₅.other _ (by decide), u₄.other _ (by decide), hesi])
    (hout (by rw [u₅.wr, u₄.wr, u₃.wr, hwr]) _ (by bdd_omega)) fun s₆ u₆ =>
      Wp.wp_test fun s₇ f₇ z₇ => WP.block_nil ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), hesi]
  · rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.gpr, u₃.mem, hm, harg _ (by bdd_omega) (by bdd_omega)]; rfl
  · rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), hesp]
  · rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, hrd]
  · rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, hwr]
  · rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, hm, h12]; rfl
  · rw [z₇, u₆.gpr, h12]

theorem saveMem_saved {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) : VG.Proof.Sha512.X86.Compress.Saved s₀ (VG.Proof.Sha512.X86.Compress.saveMem s₀) :=
  (Spill.saveMem_saved_addr _ _ VG.Proof.Sha512.X86.Compress.compressSaved_fits (by have := hp.scr_fits; omega)).of_readW fun p h => by
    have := compressSaved_fits.1 p h
    rw [VG.Proof.Sha512.X86.Compress.saveMem, VG.Proof.Sha512.X86.Compress.readW_writeW_scr hp _ _ (by bdd_omega) (by bdd_omega) (by bdd_omega)]

theorem saveMem_cnt {s₀ : State} :
    (VG.Proof.Sha512.X86.Compress.saveMem s₀).readW (addr (VG.Proof.Sha512.X86.Compress.scr s₀) cntOff) 32 = arg s₀ 2 := by
  simp only [VG.Proof.Sha512.X86.Compress.saveMem, cntOff, Mem.readW_writeW_self32]

theorem saveMem_frame {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) : Frame [VG.Proof.Sha512.X86.Compress.scrR s₀] s₀.mem (VG.Proof.Sha512.X86.Compress.saveMem s₀) :=
  (Spill.saveMem_frame List.mem_cons_self _ _ _ _ (VG.Proof.Sha512.X86.Compress.compressSaved_contains hp)).writeW List.mem_cons_self _
    (contains_addr (d := 216) (by bdd_omega) (by bdd_omega) hp.scr_fits)

theorem common_zero {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {s₁ : State} (hesi : s₁.gpr .esi = VG.Proof.Sha512.X86.Compress.scr s₀)
    (hesp : s₁.gpr .esp = VG.Proof.Sha512.X86.Compress.esp₀ s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr)
    (hm : s₁.mem = VG.Proof.Sha512.X86.Compress.saveMem s₀) : VG.Proof.Sha512.X86.Compress.Common s₀ 0 s₁ := by
  refine ⟨hesi, hesp, hrd, hwr, ?_, ?_, by rw [hm]; exact VG.Proof.Sha512.X86.Compress.saveMem_saved hp⟩
  · rw [hm]; exact (VG.Proof.Sha512.X86.Compress.saveMem_frame hp).mono (by simp)
  · rw [hm]
    have hd : ∀ r ∈ [VG.Proof.Sha512.X86.Compress.scrR s₀], Region.Disjoint (VG.Proof.Sha512.X86.Compress.stR s₀) r := fun r hr => by
      simp at hr; subst hr; exact hp.st_scr
    refine VG.Proof.Sha512.X86.stateAt_ext hp.st_fits fun k hk => ?_
    rw [VG.Proof.Sha512.X86.rd64_frame (VG.Proof.Sha512.X86.Compress.saveMem_frame hp) hd hp.st_fits (by bdd_omega), ← VG.Proof.Sha512.X86.stateAt_get hp.st_fits _ hk]
    simp [compressBlocks]

theorem restore_ok {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) {s : State} (hc : VG.Proof.Sha512.X86.Compress.Common s₀ (VG.Proof.Sha512.X86.Compress.nb s₀) s) :
    WP isa (.block epilogue) s fun s' =>
      (∀ r ∈ calleeSaved, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem := by
  rw [VG.Proof.Sha512.X86.Compress.epilogue_eq]
  refine Spill.restoreBase_ok _ (by decide)
    (fun p h => by rw [hc.esi]; exact hp.in_scr hc.wr (by have := compressSaved_fits.1 p (by revert p h; decide); omega))
    (by rw [hc.esi]; exact hc.saved.sub (by decide)) fun s' u =>
      WP.block_nil ⟨u.abi (by decide) (by decide) hc.esp, u.mem⟩

/-! ## The whole function -/

theorem correct {s₀ : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s₀) :
    WP isa Impl.Sha512.X86.compress s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Sha512.compressX86.post s₀ s' := by
  refine WP.seq (WP.mono (VG.Proof.Sha512.X86.Compress.save_ok hp) fun s₁ ⟨hesi, hedi, hesp, hrd, hwr, hm, hz⟩ => ?_)
  refine WP.seq (WP.mono (Q := VG.Proof.Sha512.X86.Compress.Common s₀ (VG.Proof.Sha512.X86.Compress.nb s₀)) ?_ fun s₂ hc =>
    WP.mono (VG.Proof.Sha512.X86.Compress.restore_ok hp hc) fun s' ⟨hr, hm'⟩ => ⟨⟨hr, ?_⟩, ?_⟩)
  rotate_left
  · rw [hm']
    refine hc.frame.readW (Region.contains_self _ _) ?_ (by decide)
    simpa using ⟨hp.ret_st, hp.ret_scr⟩
  · show stateAt s'.mem _ = _
    rw [hm']; exact hc.state
  have hc₀ := VG.Proof.Sha512.X86.Compress.common_zero hp hesi hesp hrd hwr hm
  refine WP.ite (arg s₀ 2 &&& arg s₀ 2 == 0) (by simp [eval, hz]) (fun h => ?_) (fun h => ?_)
  · have h0 : VG.Proof.Sha512.X86.Compress.nb s₀ = 0 := by simp only [BitVec.and_self, beq_iff_eq] at h; simp [VG.Proof.Sha512.X86.Compress.nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < VG.Proof.Sha512.X86.Compress.nb s₀ := by
      simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = VG.Proof.Sha512.X86.Compress.nb s₀ - i ∧ i < VG.Proof.Sha512.X86.Compress.nb s₀ ∧ VG.Proof.Sha512.X86.Compress.LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval .ne s' = some false ∧ VG.Proof.Sha512.X86.Compress.Common s₀ (VG.Proof.Sha512.X86.Compress.nb s₀) s') ∨
        (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (VG.Proof.Sha512.X86.Compress.body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, VG.Proof.Sha512.X86.Compress.nb s₀ - (i + 1), by bdd_omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : VG.Proof.Sha512.X86.Compress.LInv s₀ 0 s₁ :=
      { hc₀ with
        edi := by rw [hedi]; simp [VG.Proof.Sha512.X86.Compress.blkAddr]
        cnt := by rw [hm, VG.Proof.Sha512.X86.Compress.saveMem_cnt]; simp [VG.Proof.Sha512.X86.Compress.nb] }
    exact WP.loop (M := isa) Inv hstep (VG.Proof.Sha512.X86.Compress.nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩

/-- Memory holding the arguments `0x1000, 0x2000, 0, 0x3000` at `0x4004`. -/
def satMem : Mem := fun a =>
  if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else if a = 0x4011 then 0x30 else 0

/-- A state satisfying the precondition (with no blocks). -/
def satState : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := VG.Proof.Sha512.X86.Compress.satMem
  rd := [⟨0x2000, 0⟩, ⟨0x4004, 16⟩]
  wr := [⟨0x1000, 64⟩, ⟨0x3000, 224⟩]

theorem sat_pre : Proof.Sha512.compressX86.pre VG.Proof.Sha512.X86.Compress.satState := by
  have a0 : arg VG.Proof.Sha512.X86.Compress.satState 0 = 0x1000 := by decide
  have a1 : arg VG.Proof.Sha512.X86.Compress.satState 1 = 0x2000 := by decide
  have a2 : arg VG.Proof.Sha512.X86.Compress.satState 2 = 0 := by decide
  have a3 : arg VG.Proof.Sha512.X86.Compress.satState 3 = 0x3000 := by decide
  have e : argAddr VG.Proof.Sha512.X86.Compress.satState 0 = 0x4004 := by decide
  simp only [Proof.Sha512.compressX86, a0, a1, a2, a3, e]
  refine ⟨by decide, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩ <;>
  exact Region.disjoint_of_sep (by decide)

/-- The taint analysis starts with the stack arguments public, and the words
holding `state` and `scratch` known to be the base addresses of the writable
regions. -/
def τ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [64, 224], argLen := 20, argBases := [(4, 0), (16, 1)] }

theorem wf₀ {s : State} (hp : VG.Proof.Sha512.X86.Compress.Pre s) : VG.X86.Taint.Wf VG.Proof.Sha512.X86.Compress.τ₀ s := by
  have hst := hp.st_fits; have hsc := hp.scr_fits; have hs := hp.esp_fits
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, VG.Proof.Sha512.X86.Compress.τ₀], by simpa [hp.wr] using hp.st_scr, ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl) <;> simp only [BitVec.toNat_setWidth] <;> omega
  · simp only [hp.wr, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_st hp.arg_st
    · exact VG.X86.Taint.frame_disjoint (n := 16) (by bdd_omega) hp.ret_scr hp.arg_scr
  · intro p hp'
    simp only [VG.Proof.Sha512.X86.Compress.τ₀, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl <;> refine ⟨by decide, ?_⟩ <;>
      simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Sha512.compressX86.pre s₁)
    (h₂ : Proof.Sha512.compressX86.pre s₂) (hpub : Proof.Sha512.compressX86.pub s₁ s₂) :
    VG.X86.Taint.Agree VG.Proof.Sha512.X86.Compress.τ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1, a2, a3⟩ := hpub
  have hp₁ := VG.Proof.Sha512.X86.Compress.pre_of _ h₁; have hp₂ := VG.Proof.Sha512.X86.Compress.pre_of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, VG.Proof.Sha512.X86.Compress.wf₀ hp₁, VG.Proof.Sha512.X86.Compress.wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => ?_⟩
  · simp only [VG.Proof.Sha512.X86.Compress.τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [VG.Proof.Sha512.X86.Compress.stR, VG.Proof.Sha512.X86.Compress.scrR, VG.Proof.Sha512.X86.Compress.st, VG.Proof.Sha512.X86.Compress.scr, a0, a3]
  · simp only [VG.Proof.Sha512.X86.Compress.τ₀] at hk
    rw [show VG.X86.Taint.depth τ₀.stk = 0 from rfl, Nat.zero_add]
    rw [VG.X86.Taint.argByte_eq hp₁.esp_fits h4 hk, VG.X86.Taint.argByte_eq hp₂.esp_fits h4 hk,
      Mem.readW_byte s₁.mem _ (Nat.mod_lt _ (by bdd_omega)), Mem.readW_byte s₂.mem _ (Nat.mod_lt _ (by bdd_omega))]
    have : (k - 4) / 4 = 0 ∨ (k - 4) / 4 = 1 ∨ (k - 4) / 4 = 2 ∨ (k - 4) / 4 = 3 := by bdd_omega
    rcases this with h | h | h | h <;> rw [h]
    · exact congrArg _ a0
    · exact congrArg _ a1
    · exact congrArg _ a2
    · exact congrArg _ a3

theorem compress_verified :
    Verified X86.target Impl.Sha512.X86.compress Proof.Sha512.compressX86 :=
  ⟨fun s hs => VG.Proof.Sha512.X86.Compress.correct (VG.Proof.Sha512.X86.Compress.pre_of s hs),
    VG.Taint.constantTime (A := sseTaint) VG.Proof.Sha512.X86.Compress.τ₀ (fun _ _ h₁ h₂ hpub => VG.Proof.Sha512.X86.Compress.agree₀ h₁ h₂ hpub) (by taint_decide),
    ⟨VG.Proof.Sha512.X86.Compress.satState, VG.Proof.Sha512.X86.Compress.sat_pre⟩⟩

end Compress

end VG.Proof.Sha512.X86

end
