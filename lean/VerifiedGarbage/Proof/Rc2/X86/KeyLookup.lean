module

import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
public import VerifiedGarbage.Proof.Rc2.X86.PiLookup
public import VerifiedGarbage.Proof.Rc2.X86.KeySteps
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseWord
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith

/-!
# RC2 on x86: the schedule's word in SSE2 registers

`keyLookup r` (`Impl/Rc2/X86/Lookup.lean`) leaves in ESI's low half word
`r & 63` of the schedule at EDI (`keyLookup_ok`). Each mask is all ones or
nothing by a bit of `r` (`idxMask_ok`), so `pick` is a choice (`pick_val`):
the row chosen is the one whose number is bits 5, 4 and 3 of `r`
(`pickRows_ok`), and shifted by the others its low word is the schedule's
(`slides_ok`). The word passes through the 8 bytes at `[ebp + 48]`.
-/

@[expose] public section

namespace VG.Proof.Rc2.X86

open VG VG.X86 VG.X86.Lanes VG.X86.RegUpd VG.Impl.Rc2.X86

/-! ## The values -/

/-- Word `j` of the schedule at `p`, as read there. -/
def sword (m : Mem) (p : BitVec 32) (j : Nat) : BitVec 16 :=
  m.readW (p.setWidth 64 + BitVec.ofNat 64 (2 * j)) 16

/-- Row `c` of the schedule at `p`. -/
def srow (m : Mem) (p : BitVec 32) (c : Nat) : BitVec 128 :=
  m.readW (p.setWidth 64 + BitVec.ofNat 64 (16 * c)) 128

/-- All ones or nothing. -/
def ones (p : Bool) : BitVec 128 := if p then BitVec.allOnes 128 else 0

theorem pick_val (d s : BitVec 128) (p : Bool) : d ^^^ ((s ^^^ d) &&& ones p) = if p then s else d := by
  cases p
  · simp only [ones, Bool.false_eq_true, ite_false]
    rw [show (0 : BitVec 128) = 0#128 from rfl, BitVec.and_zero, BitVec.xor_zero]
  · simp only [ones, ite_true, BitVec.and_allOnes]
    rw [BitVec.xor_comm s d, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- The registers `xs` of the XMM file may change, and nothing else. -/
structure XKeep (xs : List XReg) (s t : State) : Prop where
  xmm : ∀ x, x ∉ xs → t.xmm x = s.xmm x
  gpr : t.gpr = s.gpr
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem XKeep.trans {xs : List XReg} {s t u : State} (h : XKeep xs s t) (h' : XKeep xs t u) : XKeep xs s u :=
  ⟨fun x hx => (h'.xmm x hx).trans (h.xmm x hx), h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd,
    h'.wr.trans h.wr⟩

theorem XKeep.weaken {xs ys : List XReg} {s t : State} (h : XKeep xs s t) (hs : ∀ x ∈ xs, x ∈ ys) : XKeep ys s t :=
  ⟨fun x hx => h.xmm x fun hm => hx (hs x hm), h.gpr, h.mem, h.rd, h.wr⟩

/-! ## The masks -/

/-- `xmm7` holds the low half of `x` in every word. -/
def Idx (x : BitVec 32) (s : State) : Prop := ∀ i < 8, word (s.xmm .xmm7) i = x.setWidth 16

theorem idxWords_ok (s : State) (r : Reg) :
    WP isa (.block (idxWords r)) s fun t => Idx (s.gpr r) t ∧ XKeep [.xmm7] s t := by
  unfold idxWords
  lrun
  refine ⟨fun i hi => ?_, fun x hx => ?_, ?_, ?_, ?_, ?_⟩
  · rw [xmm_setXmm_self, word_punpcklqdq _ _ hi]
    have w (j : Nat) (hj : j < 4) :
        word (shufLowWords ((0 : BitVec 96) ++ s.gpr r) 0) j = (s.gpr r).setWidth 16 := by
      rw [shufLowWords, word_ofWords _ (by omega_using [hj]), ite_eq_left hj]
      have e : (BitVec.extractLsb' (2 * j) 2 (0 : BitVec 8)).toNat = 0 := by
        rcases cases4 hj with rfl | rfl | rfl | rfl <;> decide
      rw [e]
      apply BitVec.eq_of_getLsbD_eq; intro k hk
      rw [getLsbD_word _ _ _ hk, BitVec.getLsbD_append, BitVec.getLsbD_setWidth]
      simp only [Nat.mul_zero, Nat.zero_add, show k < 32 by omega_using [hk], ite_true, hk, decide_true, Bool.true_and]
    by_cases h : i < 4
    · rw [ite_eq_left h]; exact w i h
    · rw [ite_eq_right h]; exact w (i - 4) (by omega_using [hi])
  · simp only [List.mem_singleton] at hx
    rw [xmm_setXmm_of_ne _ _ hx, xmm_setXmm_of_ne _ _ hx, xmm_setXmm_of_ne _ _ hx]
  all_goals rfl

theorem sshiftRight15 (x : BitVec 16) : x.sshiftRight 15 = if x.getLsbD 15 then BitVec.allOnes 16 else 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_sshiftRight]
  have hm : x.msb = x.getLsbD 15 := by rw [BitVec.msb_eq_getLsbD_last]
  by_cases h0 : i = 0
  · subst h0; cases x.getLsbD 15 <;> simp
  · rw [hm, show decide (16 ≤ i) = false from decide_eq_false (by omega_using [hi])]
    simp only [show ¬ 15 + i < 16 by omega_using [h0], ite_false, Bool.not_false, Bool.true_and]
    cases x.getLsbD 15
    · simp
    · rw [ite_eq_left rfl, BitVec.getLsbD_allOnes, decide_eq_true hi]

/-- The mask of bit `b`, word by word: the shift puts bit `b` of the index on
top of each word, the shift back copies it to every bit. -/
theorem mask_word {X : BitVec 128} {x : BitVec 32} (hX : ∀ i < 8, word X i = x.setWidth 16) {b : Nat} (hb : b < 16) :
    XShiftOp.eval .psraw (XShiftOp.eval .pslld X (BitVec.ofNat 8 (15 - b))) 15 = ones (x.getLsbD b) := by
  refine ext_word fun i hi => ?_
  have hn : (BitVec.ofNat 8 (15 - b)).toNat = 15 - b := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [])
  rw [word_psraw _ _ hi, show min (15 : BitVec 8).toNat 16 = 15 from rfl, sshiftRight15]
  have bit : (word (XShiftOp.eval .pslld X (BitVec.ofNat 8 (15 - b))) i).getLsbD 15 = x.getLsbD b := by
    rw [getLsbD_word _ _ _ (by decide)]
    have hk : i / 2 < 4 := by omega_using [hi]
    have e : 16 * i + 15 = 32 * (i / 2) + (16 * (i % 2) + 15) := by omega_using []
    have d := dword_pslld X (BitVec.ofNat 8 (15 - b)) (by rw [hn]; omega_using []) hk
    rw [hn] at d
    have g := congrArg (fun y => y.getLsbD (16 * (i % 2) + 15)) d
    simp only [getLsbD_dword, show 16 * (i % 2) + 15 < 32 by omega_using [], decide_true, Bool.true_and] at g
    rw [e, g, BitVec.getLsbD_shiftLeft, decide_eq_true (show 16 * (i % 2) + 15 < 32 by omega_using []),
      decide_eq_false (show ¬ 16 * (i % 2) + 15 < 15 - b by omega_using [hb]), Bool.true_and, Bool.not_false,
      Bool.true_and, getLsbD_dword, decide_eq_true (show 16 * (i % 2) + 15 - (15 - b) < 32 by omega_using []),
      Bool.true_and,
      show 32 * (i / 2) + (16 * (i % 2) + 15 - (15 - b)) = 16 * i + b by omega_using [hb], ← getLsbD_word _ _ _ hb, hX i hi,
      BitVec.getLsbD_setWidth, decide_eq_true hb, Bool.true_and]
  rw [bit]
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  rw [getLsbD_word _ _ _ hk, ones]
  cases x.getLsbD b
  · simp
  · rw [ite_eq_left rfl, ite_eq_left rfl, BitVec.getLsbD_allOnes, BitVec.getLsbD_allOnes, decide_eq_true hk,
      decide_eq_true (show 16 * i + k < 128 by omega_using [hi, hk])]

theorem idxMask_ok {s : State} {x : BitVec 32} (h : Idx x s) {b : Nat} (hb : b < 16) :
    WP isa (.block (idxMask b)) s fun t => t.xmm .xmm6 = ones (x.getLsbD b) ∧ XKeep [.xmm6] s t := by
  unfold idxMask
  lrun
  refine ⟨?_, fun y hy => ?_, ?_, ?_, ?_, ?_⟩
  · rw [xmm_setXmm_self]; exact mask_word h hb
  · simp only [List.mem_singleton] at hy
    rw [xmm_setXmm_of_ne _ _ hy, xmm_setXmm_of_ne _ _ hy, xmm_setXmm_of_ne _ _ hy]
  all_goals rfl

/-! ## The choices -/

theorem pick_ok (s : State) {p : Bool} (h6 : s.xmm .xmm6 = ones p) {d t : XReg} (hd : d ≠ .xmm6) (ht : t ≠ .xmm6)
    (hdt : d ≠ t) :
    WP isa (.block (pick d t)) s fun u =>
      u.xmm d = (if p then s.xmm t else s.xmm d) ∧ XKeep [d, t] s u := by
  have hdt' := hdt.symm
  have hd' := hd.symm
  have ht' := ht.symm
  unfold pick
  lrun [ne_eq, hdt, hdt', hd, hd', ht, ht']
  refine ⟨?_, fun y hy => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [xmm_setXmm_self, h6]
    exact pick_val _ _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [xmm_setXmm_of_ne _ _ hy.1, xmm_setXmm_of_ne _ _ hy.2, xmm_setXmm_of_ne _ _ hy.2]
  all_goals rfl

theorem pickRow_ok (s : State) {p : Bool} (h6 : s.xmm .xmm6 = ones p) {c : Nat} (hc : c < 4) {d t : XReg}
    (hd : d ≠ .xmm6) (ht : t ≠ .xmm6) (hdt : d ≠ t)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi)) 128) :
    WP isa (.block (pickRow c d t)) s fun u =>
      u.xmm d = srow s.mem (s.gpr .edi) (c + if p then 4 else 0) ∧ XKeep [d, t] s u := by
  have load (s' : State) (gpr : s'.gpr = s.gpr) (mem : s'.mem = s.mem) (rd : s'.rd = s.rd) (wr : s'.wr = s.wr)
      (x : XReg) (e : Nat) (he : e < 8) :
      exec (.movdquLoad x (memOp .edi (16 * e))) s' = some (s'.setXmm x (srow s.mem (s.gpr .edi) e)) := by
    have hin : InRegions (s'.rd ++ s'.wr) (addr (s'.gpr .edi) (16 * e)) 16 := by
      rw [rd, wr, gpr, addr_eq (by omega_using [fit, he])]
      exact CallLay.inRegions_sub hr (by omega_using [he]) (by decide)
    have ha : addr (s'.gpr .edi) (16 * e) = (s.gpr .edi).setWidth 64 + BitVec.ofNat 64 (16 * e) := by
      rw [gpr, addr_eq (by omega_using [fit, he])]
    change (State.load128 s' (s'.ea (memOp .edi (16 * e)))).map _ = _
    rw [ea_memOp, State.load128, ite_eq_left hin, Option.map_some, ha, mem]
    rfl
  rw [pickRow, WP.block_append_iff]
  refine WP.of_runBlock ⟨_, by
    rw [runBlock_cons, load s rfl rfl rfl rfl d c (by omega_using [hc]), runStep_some, runBlock_cons,
      load (s.setXmm d (srow s.mem (s.gpr .edi) c)) rfl rfl rfl rfl t (c + 4) (by omega_using [hc]), runStep_some, runBlock_nil], ?_⟩
  refine WP.mono (pick_ok _ (p := p) ?_ hd ht hdt) fun u ⟨hu, hk⟩ => ⟨?_, ?_⟩
  · rw [xmm_setXmm_of_ne _ _ ht.symm, xmm_setXmm_of_ne _ _ hd.symm, h6]
  · rw [hu, xmm_setXmm_self, xmm_setXmm_of_ne _ _ hdt, xmm_setXmm_self]
    cases p <;> rfl
  · refine XKeep.trans (t := (s.setXmm d (srow s.mem (s.gpr .edi) c)).setXmm t (srow s.mem (s.gpr .edi) (c + 4)))
      ⟨fun y hy => ?_, rfl, rfl, rfl, rfl⟩ hk
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [xmm_setXmm_of_ne _ _ hy.2, xmm_setXmm_of_ne _ _ hy.1]

/-! ## The row -/

/-- What bit `b` of the index adds. -/
def bitAdd (x : BitVec 32) (b n : Nat) : Nat := if x.getLsbD b then n else 0

theorem bitAdd_le (x : BitVec 32) (b n : Nat) : bitAdd x b n ≤ n := by
  unfold bitAdd; split <;> omega_using []

theorem choose_row (x : BitVec 32) (b n c : Nat) (R : Nat → BitVec 128) :
    (if x.getLsbD b then R (c + n) else R c) = R (c + bitAdd x b n) := by
  unfold bitAdd; split <;> rfl

theorem choose_shift (x : BitVec 32) (b n : Nat) (v : BitVec 128) :
    (if x.getLsbD b then v >>> n else v) = v >>> bitAdd x b n := by
  unfold bitAdd; split
  · rfl
  · exact (BitVec.ushiftRight_zero v).symm

/-- The registers the look-up writes before it has the word. -/
abbrev lookRegs : List XReg := [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6]

theorem pickRows_ok (s : State) {x : BitVec 32} (hx : Idx x s)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi)) 128) :
    WP isa (.block pickRows) s fun t =>
      t.xmm .xmm0 = srow s.mem (s.gpr .edi) (bitAdd x 5 4 + bitAdd x 4 2 + bitAdd x 3 1) ∧ XKeep lookRegs s t := by
  simp only [pickRows, List.append_assoc]
  have idx {t : State} (k : XKeep lookRegs s t) : Idx x t := by
    intro i hi; rw [k.xmm .xmm7 (by decide)]; exact hx i hi
  have row {t : State} (k : XKeep lookRegs s t) (h6 : t.xmm .xmm6 = ones (x.getLsbD 5)) (c : Nat) (hc : c < 4)
      {d e : XReg} (hd : d ≠ .xmm6) (he : e ≠ .xmm6) (hde : d ≠ e) (md : d ∈ lookRegs) (me : e ∈ lookRegs) :
      WP isa (.block (pickRow c d e)) t fun u =>
        u.xmm d = srow s.mem (s.gpr .edi) (c + bitAdd x 5 4) ∧ XKeep [d, e] t u ∧ XKeep lookRegs s u := by
    refine WP.mono (pickRow_ok t h6 hc hd he hde (by rw [k.gpr]; exact fit)
      (by rw [k.rd, k.wr, k.gpr]; exact hr)) fun u ⟨hu, hk⟩ => ⟨?_, hk, k.trans (hk.weaken ?_)⟩
    · rw [hu, k.mem, k.gpr]; rfl
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> with_reducible assumption
  rw [WP.block_append_iff]
  refine WP.mono (idxMask_ok hx (b := 5) (by decide)) fun a ⟨m5, ka⟩ => ?_
  have Ka : XKeep lookRegs s a := ka.weaken (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (row Ka m5 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun b ⟨b0, kb, Kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (row Kb ((kb.xmm _ (by decide)).trans m5) 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun c ⟨c1, kc, Kc⟩ => ?_
  have c6 : c.xmm .xmm6 = ones (x.getLsbD 5) := (kc.xmm _ (by decide)).trans ((kb.xmm _ (by decide)).trans m5)
  rw [WP.block_append_iff]
  refine WP.mono (row Kc c6 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    fun d ⟨d2, kd, Kd⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (row Kd ((kd.xmm _ (by decide)).trans c6) 3 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)) fun e ⟨e3, ke, Ke⟩ => ?_
  have e0 := ((ke.xmm .xmm0 (by decide)).trans ((kd.xmm .xmm0 (by decide)).trans (kc.xmm .xmm0 (by decide)))).trans b0
  have e1 := ((ke.xmm .xmm1 (by decide)).trans (kd.xmm .xmm1 (by decide))).trans c1
  have e2 := (ke.xmm .xmm2 (by decide)).trans d2
  rw [WP.block_append_iff]
  refine WP.mono (idxMask_ok (idx Ke) (b := 4) (by decide)) fun f ⟨m4, kf⟩ => ?_
  have Kf : XKeep lookRegs s f := Ke.trans (kf.weaken (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (pick_ok f m4 (d := .xmm0) (t := .xmm2) (by decide) (by decide) (by decide)) fun g ⟨g0, kg⟩ => ?_
  rw [kf.xmm .xmm0 (by decide), kf.xmm .xmm2 (by decide), e0, e2,
    show 2 + bitAdd x 5 4 = (0 + bitAdd x 5 4) + 2 from by omega_using [],
    choose_row x 4 2 _ (srow s.mem (s.gpr .edi))] at g0
  have Kg : XKeep lookRegs s g := Kf.trans (kg.weaken (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (pick_ok g (p := x.getLsbD 4) ((kg.xmm _ (by decide)).trans m4) (d := .xmm1) (t := .xmm3) (by decide)
    (by decide) (by decide)) fun h ⟨h1, kh⟩ => ?_
  rw [kg.xmm .xmm1 (by decide), kg.xmm .xmm3 (by decide), kf.xmm .xmm1 (by decide), kf.xmm .xmm3 (by decide), e1, e3,
    show 3 + bitAdd x 5 4 = (1 + bitAdd x 5 4) + 2 from by omega_using [],
    choose_row x 4 2 _ (srow s.mem (s.gpr .edi))] at h1
  have Kh : XKeep lookRegs s h := Kg.trans (kh.weaken (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (idxMask_ok (idx Kh) (b := 3) (by decide)) fun i ⟨m3, ki⟩ => ?_
  have Ki : XKeep lookRegs s i := Kh.trans (ki.weaken (by decide))
  refine WP.mono (pick_ok i m3 (d := .xmm0) (t := .xmm1) (by decide) (by decide) (by decide)) fun j ⟨j0, kj⟩ => ?_
  rw [ki.xmm .xmm0 (by decide), ki.xmm .xmm1 (by decide), kh.xmm .xmm0 (by decide), g0, h1,
    show 1 + bitAdd x 5 4 + bitAdd x 4 2 = (0 + bitAdd x 5 4 + bitAdd x 4 2) + 1 from by omega_using [],
    choose_row x 3 1 _ (srow s.mem (s.gpr .edi))] at j0
  refine ⟨?_, Ki.trans (kj.weaken (by decide))⟩
  rw [j0, Nat.zero_add]

/-! ## The word -/

theorem slide_ok (s : State) {x : BitVec 32} (hx : Idx x s) {b n : Nat} (hb : b < 16) (hn : n ≤ 16) :
    WP isa (.block (slide b n)) s fun t =>
      t.xmm .xmm0 = s.xmm .xmm0 >>> bitAdd x b (8 * n) ∧ XKeep lookRegs s t := by
  simp only [slide, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (idxMask_ok hx hb) fun a ⟨m, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.of_runBlock ⟨_, rfl, ?_⟩
  refine WP.mono (pick_ok _ (p := x.getLsbD b) ?_ (d := .xmm0) (t := .xmm1) (by decide) (by decide) (by decide))
    fun u ⟨u0, ku⟩ => ?_
  · simp (disch := decide) only [XOp.exec, xmm_setXmm_of_ne]; exact m
  · have hk : (BitVec.ofNat 8 n).toNat = n := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega_using [hn])
    refine ⟨?_, (ka.weaken (by decide)).trans (?_ : XKeep lookRegs a u)⟩
    · rw [u0, ← choose_shift, ← ka.xmm .xmm0 (by decide)]
      simp (disch := decide) only [XOp.exec, xmm_setXmm_of_ne, xmm_setXmm_self, movdqa_L]
      rw [XShiftOp.eval]
      simp only [hk, Nat.min_eq_left hn, Nat.mul_comm n 8]
    · have ku' : XKeep lookRegs _ u := ku.weaken (by decide)
      refine XKeep.trans (t := (XOp.shift .psrldq .xmm1 (BitVec.ofNat 8 n)).exec
        ((XOp.bin .movdqa .xmm1 .xmm0).exec a)) ⟨fun y hy => ?_, rfl, rfl, rfl, rfl⟩ ku'
      have h1 : y ≠ .xmm1 := by rintro rfl; exact hy (by decide)
      simp only [XOp.exec, xmm_setXmm_of_ne _ _ h1]

theorem slides_ok (s : State) {x : BitVec 32} (hx : Idx x s) :
    WP isa (.block slides) s fun t =>
      t.xmm .xmm0 = s.xmm .xmm0 >>> (16 * (bitAdd x 2 4 + bitAdd x 1 2 + bitAdd x 0 1)) ∧ XKeep lookRegs s t := by
  simp only [slides, List.append_assoc]
  have idx {t : State} (k : XKeep lookRegs s t) : Idx x t := by
    intro i hi; rw [k.xmm .xmm7 (by decide)]; exact hx i hi
  rw [WP.block_append_iff]
  refine WP.mono (slide_ok s hx (b := 2) (n := 8) (by decide) (by decide)) fun a ⟨ha, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (slide_ok a (idx ka) (b := 1) (n := 4) (by decide) (by decide)) fun b ⟨hb, kb⟩ => ?_
  refine WP.mono (slide_ok b (idx (ka.trans kb)) (b := 0) (n := 2) (by decide) (by decide)) fun c ⟨hc, kc⟩ =>
    ⟨?_, (ka.trans kb).trans kc⟩
  rw [hc, hb, ha, ← BitVec.shiftRight_add, ← BitVec.shiftRight_add]
  congr 1
  unfold bitAdd
  cases x.getLsbD 2 <;> cases x.getLsbD 1 <;> cases x.getLsbD 0 <;> rfl

theorem bits_sum : ∀ i < 64, (if i.testBit 5 then 32 else 0) + (if i.testBit 4 then 16 else 0) +
    (if i.testBit 3 then 8 else 0) + (if i.testBit 2 then 4 else 0) + (if i.testBit 1 then 2 else 0) +
    (if i.testBit 0 then 1 else 0) = i := by decide

theorem bitAdd_scale (x : BitVec 32) (b n k : Nat) : k * bitAdd x b n = bitAdd x b (k * n) := by
  unfold bitAdd; split
  · rfl
  · exact Nat.mul_zero k

theorem index_sum (x : BitVec 32) :
    8 * (bitAdd x 5 4 + bitAdd x 4 2 + bitAdd x 3 1) + (bitAdd x 2 4 + bitAdd x 1 2 + bitAdd x 0 1) =
      (x.setWidth 6).toNat := by
  have h := bits_sum (x.setWidth 6).toNat (x.setWidth 6).isLt
  have t (b : Nat) (hb : b < 6) : (x.setWidth 6).toNat.testBit b = x.getLsbD b := by
    rw [BitVec.testBit_toNat, BitVec.getLsbD_setWidth, decide_eq_true hb, Bool.true_and]
  rw [t 5 (by decide), t 4 (by decide), t 3 (by decide), t 2 (by decide), t 1 (by decide), t 0 (by decide)] at h
  simp only [Nat.mul_add, bitAdd_scale, Nat.reduceMul]
  unfold bitAdd
  omega_using [h]

theorem shift_word (v : BitVec 128) (k : Nat) : (v >>> (16 * k)).setWidth 16 = word v k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, BitVec.getLsbD_ushiftRight, getLsbD_word _ _ _ hi]

/-! ## The end -/

theorem low32 (v : BitVec 128) : (v.extractLsb' 0 64).extractLsb' 0 32 = v.setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, Nat.zero_add,
    show i < 64 by omega_using [hi]]

theorem lookEnd_ok (s : State)
    (hw : InRegions s.wr (addr (s.gpr .ebp) 48) 8) :
    WP isa (.block lookEnd) s fun t =>
      t.gpr .esi = (s.xmm .xmm0).setWidth 32 ∧ (∀ r, r ≠ .esi → t.gpr r = s.gpr r) ∧
      t.mem = s.mem.writeW (addr (s.gpr .ebp) 48) ((s.xmm .xmm0).extractLsb' 0 64) ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) 48) 4 := by
    obtain ⟨r, hr, hc⟩ := CallLay.inRegions_sub (off := 0) (l := 4) hw (by decide) (by decide)
    refine ⟨r, List.mem_append_right _ hr, ?_⟩
    rwa [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at hc
  have e : (s.mem.writeW (addr (s.gpr .ebp) 48) ((s.xmm .xmm0).extractLsb' 0 64)).readW (addr (s.gpr .ebp) 48) 32 =
      (s.xmm .xmm0).setWidth 32 := by
    have h := readW_writeW_inside s.mem (addr (s.gpr .ebp) 48) ((s.xmm .xmm0).extractLsb' 0 64) (k := 0) (n := 4)
      (by decide) (by decide)
    rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero] at h
    exact h.trans (low32 _)
  unfold lookEnd
  lrun [State.store64, hw, hr, e]
  refine ⟨gpr_setReg_self _ _ _, fun r hr => gpr_setReg_of_ne _ _ hr, rfl, rfl, rfl⟩

/-! ## The lookup -/

theorem readW16 (m : Mem) (a : Addr) :
    m.readW a 16 = (m a).setWidth 16 ||| (m (a + BitVec.ofNat 64 1)).setWidth 16 <<< 8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.readW, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  rw [VG.X86.getLsbD_read _ _ (by omega_using [hi])]
  by_cases h : i < 8
  · simp [Nat.div_eq_of_lt h, Nat.mod_eq_of_lt h, h]
  · simp [show i / 8 = 1 by omega_using [h, hi], show i % 8 = i - 8 by omega_using [h, hi], h,
      show i - 8 < 16 by omega_using [hi], BitVec.getLsbD_of_ge (m a) i (by omega_using [h])]

theorem sword_eq (m : Mem) (p : BitVec 32) {j : Nat} (hj : j < 64) :
    sword m p j = (Spec.Rc2.scheduleAt m (addr32 p)).getD j 0 := by
  rw [scheduleAt_getD _ _ _ hj, sword, readW16, Offset.add_add]
  rfl

theorem srow_word (m : Mem) (p : BitVec 32) (c : Nat) {k : Nat} (hk : k < 8) :
    word (srow m p c) k = sword m p (8 * c + k) := by
  rw [srow, word_readW _ _ hk, Offset.add_add, sword, show 16 * c + 2 * k = 2 * (8 * c + k) by omega_using []]

/-- Word `r & 63` of the schedule at EDI, through the 8 bytes at `[ebp + 48]`. -/
theorem keyLookup_ok (s : State) (r : Reg)
    (fit : (s.gpr .edi).toNat + 128 ≤ 2 ^ 32)
    (readable : InRegions (s.rd ++ s.wr) (addr32 (s.gpr .edi)) 128)
    (writable : InRegions s.wr (addr (s.gpr .ebp) 48) 8) :
    WP isa (.block (keyLookup r)) s (fun s' =>
      (s'.gpr .esi).setWidth 16 = (Spec.Rc2.scheduleAt s.mem (addr32 (s.gpr .edi))).getD
        ((s.gpr r).setWidth 6).toNat 0 ∧
      (∀ q, q ≠ .esi → s'.gpr q = s.gpr q) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [⟨addr (s.gpr .ebp) 48, 8⟩] s.mem s'.mem) := by
  simp only [keyLookup, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (idxWords_ok s r) fun a ⟨ha, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (pickRows_ok a ha (by rw [ka.gpr]; exact fit) (by rw [ka.rd, ka.wr, ka.gpr]; exact readable))
    fun b ⟨hb, kb⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (slides_ok b (x := s.gpr r) fun i hi => by rw [kb.xmm .xmm7 (by decide)]; exact ha i hi)
    fun c ⟨hc, kc⟩ => ?_
  have gpr : c.gpr = s.gpr := kc.gpr.trans (kb.gpr.trans ka.gpr)
  have mem : c.mem = s.mem := kc.mem.trans (kb.mem.trans ka.mem)
  have wr : c.wr = s.wr := kc.wr.trans (kb.wr.trans ka.wr)
  refine WP.mono (lookEnd_ok c (by rw [wr, gpr]; exact writable))
    fun d ⟨hd, gd, md, rd, wd⟩ => ⟨?_, fun q hq => ?_, ?_, ?_, ?_⟩
  · have hk : bitAdd (s.gpr r) 2 4 + bitAdd (s.gpr r) 1 2 + bitAdd (s.gpr r) 0 1 < 8 := by
      have h2 := bitAdd_le (s.gpr r) 2 4
      have h1 := bitAdd_le (s.gpr r) 1 2
      have h0 := bitAdd_le (s.gpr r) 0 1
      omega_using [h0, h1, h2]
    rw [hd, hc, hb, ka.gpr, ka.mem, BitVec.setWidth_setWidth_of_le _ (by decide : 16 ≤ 32), shift_word,
      srow_word _ _ _ hk, index_sum, sword_eq _ _ (BitVec.isLt _)]
  · rw [gd q hq, gpr]
  · rw [rd, kc.rd, kb.rd, ka.rd]
  · rw [wd, wr]
  · rw [md, mem, gpr]
    exact (Frame.refl _ _).writeW List.mem_cons_self _ (Region.contains_self _ _)

end VG.Proof.Rc2.X86
