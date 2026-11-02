module

public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Front
public import VerifiedGarbage.Proof.RsaKeyGen.RISCV64.Key.Ops
public meta import VerifiedGarbage.Proof.Bignum.RISCV64.Run
import VerifiedGarbage.Proof.Rsa.RISCV64.KeyDiv
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-!
# `vg_rsa_keygen_key` on RISC-V: the body's state, the set-up, the reads and the constants

`St s0 used s`: `CB`, the working space in `w = wOf s0` with `nArr` arrays,
and the arrays not in `used` still zero. `St.step` carries it through a step
writing arrays and slots. `setup_ok` establishes it, `loads_ok` reads `p`,
`q` and `e`, and `consts_ok` writes the constants (`Consts`). `nP_ok`,
`nTwo_ok` and `nW_ok` are `invOf`'s counts.
-/

@[expose] public section

namespace VG.Proof.RsaKeyGen.RISCV64.Key

open VG VG.RISCV64 VG.RISCV64.RegUpd VG.Proof.Mont VG.Proof.Bignum.RISCV64 VG.Proof.Rsa.RISCV64.Keys
open VG.Impl.Rsa.RISCV64.Keys (seqs ptr setOne half load zeroArrays setW)
open VG.Impl.RsaKeyGen.RISCV64.Key (nArr setup loads consts setLow aOne aTwo aThree aC aC33 aTop aP0 aQ0 aE
  nP nTwo nW cnt8)

/-! ## The body's state -/

/-- The inputs' bytes, as read. -/
abbrev pB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a4) (pLen s0)
abbrev qB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (s0.gpr .a6) (pLen s0)
abbrev eB (s0 : State) : List Byte := Spec.Rsa.bytesAt s0.mem (stackArg s0 6) (stackArg s0 7).toNat

/-- The body's state: `CB`, the working space in `w = wOf s0` with `nArr` arrays, and the
arrays not in `used` still zero (over their `w + 2` words). -/
structure St (s0 : State) (used : List Nat) (s : State) : Prop where
  cb : CB s0 s0.mem s
  ws : Ws s (bOf s0) (zOf s0) (wOf s0) nArr
  free : ∀ j < nArr, j ∉ used → wordsVal s.mem (bOf s0) (arr (wOf s0) j) (wOf s0 + 2) = 0

theorem St.fit {s0 s : State} {used : List Nat} (h : St s0 used s) {j : Nat} (hj : j < nArr) :
    arr (wOf s0) j + S (wOf s0) ≤ 2 ^ 64 :=
  h.ws.fit64 hj

/-- A free array is zero. -/
theorem St.zero {s0 s : State} {used : List Nat} (h : St s0 used s) {j : Nat} (hj : j < nArr)
    (hu : j ∉ used) : num s.mem (bOf s0) (wOf s0) j = 0 :=
  wordsVal_zero_part (a := 0) (h.free j hj hu) (by omega)

/-- A step writing arrays `js` and slots `ds` (from 96 on, below `hdr`) and keeping
`cbRegs`. -/
theorem St.step {s0 s t : State} {used js ds : List Nat} (h : St s0 used s)
    (ws : Ws t (bOf s0) (zOf s0) (wOf s0) nArr)
    (f : VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) js ds s.mem t.mem) (hjs : ∀ j ∈ js, j < nArr)
    (hds : ∀ d ∈ ds, 96 ≤ d ∧ d + 8 ≤ hdr) {rs : List Reg} (k : Keep rs s t)
    (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) : St s0 (js ++ used) t := by
  have hz := h.ws.hdr_le
  refine ⟨h.cb.of_frame f (fun j hj => Nat.le_trans (arr_end (hjs j hj)) h.ws.fits) hds hz k hr, ws,
    fun j hj hu => ?_⟩
  have hu1 : j ∉ js := fun e => hu (List.mem_append_left _ e)
  have hu2 : j ∉ used := fun e => hu (List.mem_append_right _ e)
  rw [f.full (j := j) (fun k hk e => hu1 (e ▸ hk)) (fun d hd => (hds d hd).2) (h.fit hj)]
  exact h.free j hj hu2

/-- `St` through a step that changes only registers. -/
theorem St.regs {s0 s t : State} {used : List Nat} (h : St s0 used s) {rs : List Reg} (k : Keep rs s t)
    (hm : t.mem = s.mem) (hr : ∀ r ∈ cbRegs, r ∉ rs := by decide) (h9 : .s9 ∉ rs := by decide)
    (h10 : .s10 ∉ rs := by decide) (h11 : .s11 ∉ rs := by decide) : St s0 used t :=
  ⟨h.cb.of_keep k hm hr, h.ws.of_keep k h9 h10 h11, fun j hj hu => by rw [hm]; exact h.free j hj hu⟩

/-! ## The set-up -/

theorem pLen_ofNat {s0 : State} {s : State} (c : CB s0 s0.mem s) :
    s.gpr .a1 = BitVec.ofNat 64 (pLen s0) := by
  rw [c.a1, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem setup_ok {s0 s : State} (h : PreC s0) (c : CB s0 s0.mem s) : WP isa setup s (St s0 []) := by
  have ⟨f1, w1, w2⟩ := h.fits
  have hp := h.p512
  have hz := h.zk
  rw [setup, WP.seq_iff, WP.block_append_iff]
  have hb : WP isa (.block [.shift .sll .d .t6 .a1 1]) s fun u =>
      (u.gpr .t6 = BitVec.ofNat 64 (2 * pLen s0) ∧ u.mem = s.mem) ∧ Keep [.t6] s u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [pLen_ofNat c, shl1_ofNat _ (show 2 * pLen s0 < 2 ^ 64 by simp only [pLen] at hp ⊢; omega_arith)]
  refine WP.mono hb fun u ⟨⟨u6, um⟩, ku⟩ => ?_
  have cu := c.of_keep ku um
  refine WP.mono (setW_ok (k := 2 * pLen s0) u6 (by simp only [pLen] at hp ⊢; omega_arith))
    fun v ⟨⟨v9, v10, vm⟩, kv⟩ => ?_
  have cv := cu.of_keep kv vm
  have wv : Ws v (bOf s0) (zOf s0) (wOf s0) nArr :=
    ⟨Scr.of_mem (by rw [cv.wr]; exact h.sR_wr) h.ws h.al, f1, by omega_arith, by omega_arith, v9, v10, cv.s11⟩
  refine WP.mono (zeroArrays_ok wv (by decide) (by decide) (by decide)) fun t ⟨wt, ft, zt, kt⟩ => ?_
  refine ⟨cv.of_frame ft (fun j hj => Nat.le_trans (arr_end (List.mem_range.mp hj)) f1) (by simp)
    wv.hdr_le kt, wt, fun j hj _ => zt j hj⟩

/-! ## The reads -/

theorem PreC.pR_wr {s : State} (h : PreC s) : pR s ∈ s.wr := by rw [h.hwr]; simp
theorem PreC.qR_wr {s : State} (h : PreC s) : qR s ∈ s.wr := by rw [h.hwr]; simp
theorem PreC.eR_rd {s : State} (h : PreC s) : eR s ∈ s.rd := by rw [h.hrd]; simp

theorem inRegions_left {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    InRegions (rs ++ ws) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_left _ hr, hc⟩

theorem inRegions_right {rs ws : List Region} {a : Addr} {n : Nat} (h : InRegions ws a n) :
    InRegions (rs ++ ws) a n :=
  let ⟨r, hr, hc⟩ := h; ⟨r, List.mem_append_right _ hr, hc⟩

/-- One read: the `L` bytes of an input region at `P` into a free array `j`. -/
theorem ld1_ok {s0 t : State} {used : List Nat} (c : St s0 used t)
    {j : Nat} (hj : j < nArr) (hju : j ∉ used) {P : Addr} {L : Nat} {src len : Reg} (hl1 : len ≠ .t1)
    (hr : ∀ i < L, InRegions (s0.rd ++ s0.wr) (off P i) 1)
    (hd : (⟨P, L⟩ : Region).Disjoint (sR s0)) (hL64 : L ≤ 2 ^ 64)
    (hs : t.gpr src = P) (hl : t.gpr len = BitVec.ofNat 64 L) (hL : 1 ≤ L) (hLw : L ≤ 8 * wOf s0) :
    WP isa (load j src len) t fun u => St s0 (j :: used) u ∧
      VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) [j] [] t.mem u.mem ∧
      num u.mem (bOf s0) (wOf s0) j = Spec.Rsa.os2ip (Spec.Rsa.bytesAt s0.mem P L) := by
  refine WP.mono (load_ok c.ws hj (by decide) hl1 hs hl hL hLw
    (fun i hi => by rw [c.cb.rd, c.cb.wr]; exact hr i hi) (bytes_sep hd hL64) (c.zero hj hju))
    fun u ⟨wu, fu, vu, ku, _⟩ => ?_
  refine ⟨c.step wu fu (by simpa using hj) (by simp) ku, fu, ?_⟩
  rw [vu, c.cb.bytes hd hL64]

/-- After the reads: `[aP0] = p`, `[aQ0] = q`, `[aE] = e`. -/
theorem loads_ok {s0 s : State} (h : PreC s0) (c : St s0 [] s) :
    WP isa loads s fun t => St s0 [aE, aQ0, aP0] t ∧
      num t.mem (bOf s0) (wOf s0) aP0 = Spec.Rsa.os2ip (pB s0) ∧
      num t.mem (bOf s0) (wOf s0) aQ0 = Spec.Rsa.os2ip (qB s0) ∧
      num t.mem (bOf s0) (wOf s0) aE = Spec.Rsa.os2ip (eB s0) := by
  have hp := h.p32
  have hp2 := h.p512
  have he1 := h.e1
  have he2 := h.e2
  have hw : 4 * wOf s0 = (s0.gpr .a5).toNat := h.wOf_eq
  have hpl : pLen s0 = (s0.gpr .a5).toNat := rfl
  have ⟨_, w8, _⟩ := h.fits
  have wpq : (s0.gpr .a4).toNat + pLen s0 ≤ 2 ^ 64 := h.wp
  have wq : (s0.gpr .a6).toNat + pLen s0 ≤ 2 ^ 64 := by have := h.wq; rw [h.hq] at this; exact this
  have qR' : (⟨s0.gpr .a6, pLen s0⟩ : Region) = qR s0 := by simp only [qR, pLen, h.hq]
  unfold loads
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ld1_ok c (j := aP0) (by decide) (by simp) (by decide)
    (fun i hi => inRegions_right (bytes_in h.pR_wr (by omega_arith) i hi)) h.ps (by omega_arith)
    c.cb.s2 (pLen_ofNat c.cb) (by omega_arith) (by omega_arith)) fun t1 ⟨c1, f1, v1⟩ => ?_
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  refine WP.mono (ld1_ok c1 (j := aQ0) (by decide) (by simp [aP0, aQ0]) (by decide)
    (fun i hi => inRegions_right (bytes_in (by rw [qR']; exact h.qR_wr) (by omega_arith) i hi))
    (by rw [qR']; exact h.qs) (by omega_arith)
    c1.cb.s3 (pLen_ofNat c1.cb) (by omega_arith) (by omega_arith)) fun t2 ⟨c2, f2, v2⟩ => ?_
  simp only [seqs]
  refine WP.mono (ld1_ok c2 (j := aE) (by decide) (by simp [aP0, aQ0, aE]) (by decide)
    (fun i hi => inRegions_left (bytes_in h.eR_rd (by have := h.we; omega_arith) i hi)) h.es
    (by have := h.we; omega_arith) c2.cb.a0 (by rw [c2.cb.a7, BitVec.ofNat_toNat, BitVec.setWidth_eq])
    he1 (by omega_arith)) fun t ⟨c3, f3, v3⟩ => ?_
  refine ⟨c3, ?_, ?_, v3⟩
  · rw [f3.num (by simp [aP0, aE]) (by simp) (c2.fit (by decide)),
      f2.num (by simp [aP0, aQ0]) (by simp) (c1.fit (by decide)), v1]
  · rw [f3.num (by simp [aQ0, aE]) (by simp) (c2.fit (by decide)), v2]

/-! ## The constants -/

/-- The arrays the constants write. -/
abbrev constArrs : List Nat := [aOne, aTwo, aThree, aC, aC33, aTop]

/-- The constants: `[aOne] = 1`, `[aTwo] = 2`, `[aThree] = 3`, `[aC] = 2^(8 p_len) + 1`,
`[aC33] = 2^33`, `[aTop] = 2^(64 w - 1)`. -/
structure Consts (s0 : State) (m : Mem) : Prop where
  one : num m (bOf s0) (wOf s0) aOne = 1
  two : num m (bOf s0) (wOf s0) aTwo = 2
  three : num m (bOf s0) (wOf s0) aThree = 3
  c : num m (bOf s0) (wOf s0) aC = 2 ^ (8 * pLen s0) + 1
  c33 : num m (bOf s0) (wOf s0) aC33 = 2 ^ 33
  top : num m (bOf s0) (wOf s0) aTop = 2 ^ (64 * wOf s0 - 1)

/-- The word `L / 8` of an array holding 1 := 1: `1 + 2^(8 L)`. -/
theorem cHigh_ok {s : State} {B : Addr} {Z w N j L : Nat} (h : Ws s B Z w N) (hj : j < N) (hN : N ≤ 2048)
    (hl : s.gpr .a1 = BitVec.ofNat 64 L) (hL8 : L % 8 = 0) (hLw : L / 8 < w) (hL0 : 0 < L)
    (hv : num s.mem B w j = 1) :
    WP isa (.block (ptr .t0 j ++ ([.add .t0 .t0 .a1, .li .t5 1, .store .d .t5 .t0 0] : List Instr))) s
      fun t => Ws t B Z w N ∧ VG.Proof.Rsa.RISCV64.Keys.Frame B w [j] [] s.mem t.mem ∧ num t.mem B w j = 2 ^ (8 * L) + 1 ∧
        Keep opRegs s t := by
  have fit := h.arr_fit hj
  have nw := h.nowrap
  have hS : S w = 8 * (w + 2) := rfl
  have hle := h.wle
  refine ptr_ok h (by decide) (by decide) (show j < 2048 by omega_arith) ?_
  have hb : WP isa (.block [.add .t0 .t0 .a1, .li .t5 1, .store .d .t5 .t0 0]) (s.write .t0 (off B (arr w j)))
      fun u => (u.mem = s.mem.writeW (off B (arr w j + 8 * (L / 8))) (BitVec.ofNat 64 1)) ∧
        Keep [.t0, .t5] (s.write .t0 (off B (arr w j))) u := by
    refine WP.keep _ ?_ (by rfl) (by rfl)
    have e : off B (arr w j) + BitVec.ofNat 64 L = off B (arr w j + 8 * (L / 8)) := by
      rw [off_add, show arr w j + L = arr w j + 8 * (L / 8) by omega]
    brun [hl, e, keys_exec_li_one, h.scr.st (d := arr w j + 8 * (L / 8)) (n := 8) (by omega_arith),
      h.scr.al8 (d := arr w j + 8 * (L / 8)) (by omega_arith) (by have := arr_al w j; omega_arith)]
  refine WP.mono hb fun u ⟨um, ku⟩ => ?_
  have k₁ : Keep opRegs s u := ((Keep.write _ _ _).trans ku).mono (by decide)
  have o := writeW_outside s.mem B (d := arr w j + 8 * (L / 8)) (BitVec.ofNat 64 1) (by omega_arith)
  refine ⟨h.of_keep k₁, ?_, ?_, k₁⟩
  · rw [um]
    exact Frame.of_arr (d := 8 * (L / 8)) o (by omega_arith) (by simp)
  · -- The old number: 1 in the low `L / 8` words, 0 above.
    have hv' : wordsVal s.mem B (arr w j) w = 1 := hv
    have split := wordsVal_append s.mem B (d := arr w j) (a := L / 8) (b := w - L / 8)
    rw [show L / 8 + (w - L / 8) = w by omega, hv'] at split
    have split2 := wordsVal_append s.mem B (d := arr w j + 8 * (L / 8)) (a := 1) (b := w - L / 8 - 1)
    rw [show 1 + (w - L / 8 - 1) = w - L / 8 by omega] at split2
    have hp : 2 ≤ 2 ^ (64 * (L / 8)) := by
      have : 1 ≤ 64 * (L / 8) := by omega
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (64 * (L / 8)) := Nat.pow_le_pow_right (by decide) this
    have lo : wordsVal s.mem B (arr w j) (L / 8) = 1 := by
      rcases Nat.eq_zero_or_pos (wordsVal s.mem B (arr w j + 8 * (L / 8)) (w - L / 8)) with e | e
      · rw [e] at split; omega
      · have : 2 ^ (64 * (L / 8)) ≤ 2 ^ (64 * (L / 8)) * wordsVal s.mem B (arr w j + 8 * (L / 8)) (w - L / 8) :=
          Nat.le_mul_of_pos_right _ e
        omega
    have hi : wordsVal s.mem B (arr w j + 8 * (L / 8)) (w - L / 8) = 0 := by
      rw [lo] at split
      rcases Nat.eq_zero_or_pos (wordsVal s.mem B (arr w j + 8 * (L / 8)) (w - L / 8)) with e | e
      · exact e
      · have : 2 ^ (64 * (L / 8)) ≤ 2 ^ (64 * (L / 8)) * wordsVal s.mem B (arr w j + 8 * (L / 8)) (w - L / 8) :=
          Nat.le_mul_of_pos_right _ e
        omega
    have hi2 : wordsVal s.mem B (arr w j + 8 * (L / 8) + 8 * 1) (w - L / 8 - 1) = 0 := by
      rw [hi] at split2
      have := Nat.two_pow_pos (64 * 1)
      exact (Nat.mul_eq_zero.mp (show 2 ^ (64 * 1) *
        wordsVal s.mem B (arr w j + 8 * (L / 8) + 8 * 1) (w - L / 8 - 1) = 0 by omega)).resolve_left (by omega)
    show wordsVal u.mem B (arr w j) w = _
    rw [um, wordsVal_write_mid s.mem B hLw _ (by omega_arith), lo, show arr w j + 8 * (L / 8) + 8 =
      arr w j + 8 * (L / 8) + 8 * 1 by omega, show w - L / 8 - 1 = w - L / 8 - 1 from rfl, hi2]
    simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero]
    rw [show 8 * L = 64 * (L / 8) by omega]
    omega

/-- `[aC33] := 2^33` and `t4 := 1`, on the zero array. -/
theorem c33_ok {s : State} {B : Addr} {Z w N : Nat} (h : Ws s B Z w N) (hN : aC33 < N) (hN' : N ≤ 2048)
    (hz : num s.mem B w aC33 = 0) :
    WP isa (.block (ptr .t0 aC33 ++
      ([.li .t5 1, .shift .sll .d .t5 .t5 33, .store .d .t5 .t0 0, .li .t4 1] : List Instr)))
      s fun t => Ws t B Z w N ∧ VG.Proof.Rsa.RISCV64.Keys.Frame B w [aC33] [] s.mem t.mem ∧ num t.mem B w aC33 = 2 ^ 33 ∧
        t.gpr .t4 = 1#64 ∧ Keep opRegs s t := by
  rw [show ptr .t0 aC33 ++ ([.li .t5 1, .shift .sll .d .t5 .t5 33, .store .d .t5 .t0 0, .li .t4 1] : List Instr) =
    (ptr .t0 aC33 ++ ([.li .t5 1, .shift .sll .d .t5 .t5 33, .store .d .t5 .t0 0] : List Instr)) ++
      ([.li .t4 1] : List Instr) by simp,
    WP.block_append_iff]
  have fit := h.arr_fit hN
  have hS : S w = 8 * (w + 2) := rfl
  refine WP.mono (low_ok h hN hN' (f := fun _ => BitVec.ofNat 64 (2 ^ 33)) fun s₀ e0 em ew er => ?_)
    fun u ⟨wu, fu, vu, ku⟩ => ?_
  · refine WP.keep _ ?_ (by rfl) (by rfl)
    brun [e0, em, keys_exec_li_one, (h.scr.congr ew).st (d := arr w aC33) (n := 8) (by omega_arith),
      (h.scr.congr ew).al8 (d := arr w aC33) (by omega_arith) (arr_al _ _)]
    rfl
  · have hb : WP isa (.block [.li .t4 1]) u fun v => (v.gpr .t4 = 1#64 ∧ v.mem = u.mem) ∧ Keep [.t4] u v := by
      refine WP.keep _ ?_ (by rfl) (by rfl)
      brun [keys_exec_li_one]
    refine WP.mono hb fun t ⟨⟨t4, tm⟩, kt⟩ => ?_
    refine ⟨wu.of_keep kt, by rw [tm]; exact fu, by rw [tm, vu, hz]; rfl, t4,
      Keep.trans' ku (kt.mono (by decide))⟩

theorem consts_ok {s0 s : State} {used : List Nat} (h : PreC s0) (c : St s0 used s)
    (hu : ∀ j ∈ constArrs, j ∉ used) :
    WP isa (seqs consts) s fun t => St s0 (constArrs ++ used) t ∧ Consts s0 t.mem ∧
      (∀ j < nArr, j ∉ constArrs → num t.mem (bOf s0) (wOf s0) j = num s.mem (bOf s0) (wOf s0) j) := by
  have hp := h.p32
  have hp8 := h.p8
  have hw : 4 * wOf s0 = (s0.gpr .a5).toNat := h.wOf_eq
  have hpl : pLen s0 = (s0.gpr .a5).toNat := rfl
  have ⟨_, w8, w128⟩ := h.fits
  have z : ∀ j ∈ constArrs, num s.mem (bOf s0) (wOf s0) j = 0 := by
    intro j hj
    have hj' : j < nArr := by
      simp only [constArrs, List.mem_cons, List.mem_nil_iff, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact c.zero hj' (hu j hj)
  unfold consts
  rw [wp_seqs_cons (List.cons_ne_nil _ _)]
  simp only [List.append_assoc]
  -- `[aOne] := 1`
  rw [WP.block_append_iff]
  refine WP.mono (setOne_ok c.ws (j := aOne) (by decide) (by decide)) fun t1 ⟨w1, f1, v1, k1⟩ => ?_
  have c1 := c.step w1 f1 (by decide) (by simp) k1
  rw [WP.block_append_iff]
  refine WP.mono (setLow_ok w1 (j := aTwo) (x := 2) (by decide) (by decide) (by decide))
    fun t2 ⟨w2, f2, v2, k2⟩ => ?_
  have c2 := c1.step w2 f2 (by decide) (by simp) k2
  rw [WP.block_append_iff]
  refine WP.mono (setLow_ok w2 (j := aThree) (x := 3) (by decide) (by decide) (by decide))
    fun t3 ⟨w3, f3, v3, k3⟩ => ?_
  have c3 := c2.step w3 f3 (by decide) (by simp) k3
  rw [WP.block_append_iff]
  refine WP.mono (setOne_ok w3 (j := aC) (by decide) (by decide)) fun t4 ⟨w4, f4, v4, k4⟩ => ?_
  have c4 := c3.step w4 f4 (by decide) (by simp) k4
  -- The values so far, through the frames.
  have fit := fun j (hj : j < nArr) => c.fit hj
  have keepNum : ∀ {m m' : Mem} {o : Nat}, VG.Proof.Rsa.RISCV64.Keys.Frame (bOf s0) (wOf s0) [o] [] m m' → ∀ j < nArr, j ≠ o →
      num m' (bOf s0) (wOf s0) j = num m (bOf s0) (wOf s0) j := fun f j hj hjo =>
    f.num (fun _ hk => by rw [List.mem_singleton.mp hk]; exact Ne.symm hjo) (by simp) (fit j hj)
  have zC4 : num t3.mem (bOf s0) (wOf s0) aC = 0 := by
    rw [keepNum f3 _ (by decide) (by decide), keepNum f2 _ (by decide) (by decide),
      keepNum f1 _ (by decide) (by decide), z aC (by simp)]
  rw [zC4] at v4
  have hv4 : num t4.mem (bOf s0) (wOf s0) aC = 1 := by rw [v4]
  rw [← List.append_assoc, WP.block_append_iff]
  refine WP.mono (cHigh_ok w4 (j := aC) (L := pLen s0) (by decide) (by decide) (pLen_ofNat c4.cb)
    hp8 (by omega) (by omega) hv4) fun t5 ⟨w5, f5, v5, k5⟩ => ?_
  have c5 := c4.step w5 f5 (by decide) (by simp) k5
  have zC33 : num t5.mem (bOf s0) (wOf s0) aC33 = 0 := by
    rw [keepNum f5 _ (by decide) (by decide), keepNum f4 _ (by decide) (by decide),
      keepNum f3 _ (by decide) (by decide), keepNum f2 _ (by decide) (by decide),
      keepNum f1 _ (by decide) (by decide), z aC33 (by simp)]
  refine WP.mono (c33_ok w5 (by decide) (by decide) zC33) fun t6 ⟨w6, f6, v6, t46, k6⟩ => ?_
  have c6 := c5.step w6 f6 (by decide) (by simp) k6
  simp only [seqs]
  have zT : num t6.mem (bOf s0) (wOf s0) aTop = 0 := by
    rw [keepNum f6 _ (by decide) (by decide), keepNum f5 _ (by decide) (by decide),
      keepNum f4 _ (by decide) (by decide), keepNum f3 _ (by decide) (by decide),
      keepNum f2 _ (by decide) (by decide), keepNum f1 _ (by decide) (by decide), z aTop (by simp)]
  refine WP.mono (half_ok w6 (j := aTop) (by decide) (by decide) (by rw [t46]; decide))
    fun t ⟨wt, ft, vt, _, kt⟩ => ?_
  have c7 := c6.step wt ft (by decide) (by simp) kt
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun j hj hjn => ?_⟩
  · refine ⟨c7.cb, c7.ws, fun j hj hu' => c7.free j hj fun e => hu' ?_⟩
    simp only [List.mem_cons, constArrs, List.cons_append, List.nil_append] at e ⊢
    rcases e with e | e | e | e | e | e | e | e <;> simp [e]
  · rw [keepNum ft _ (by decide) (by decide), keepNum f6 _ (by decide) (by decide),
      keepNum f5 _ (by decide) (by decide), keepNum f4 _ (by decide) (by decide),
      keepNum f3 _ (by decide) (by decide), keepNum f2 _ (by decide) (by decide), v1,
      z aOne (by simp)]
  · rw [keepNum ft _ (by decide) (by decide), keepNum f6 _ (by decide) (by decide),
      keepNum f5 _ (by decide) (by decide), keepNum f4 _ (by decide) (by decide),
      keepNum f3 _ (by decide) (by decide), v2, keepNum f1 _ (by decide) (by decide), z aTwo (by simp)]
  · rw [keepNum ft _ (by decide) (by decide), keepNum f6 _ (by decide) (by decide),
      keepNum f5 _ (by decide) (by decide), keepNum f4 _ (by decide) (by decide), v3,
      keepNum f2 _ (by decide) (by decide), keepNum f1 _ (by decide) (by decide), z aThree (by simp)]
  · rw [keepNum ft _ (by decide) (by decide), keepNum f6 _ (by decide) (by decide), v5]
  · rw [keepNum ft _ (by decide) (by decide), v6]
  · rw [vt, zT, t46]
    have e : (1#64).toNat = 1 := rfl
    rw [e, Nat.zero_add, Nat.mul_one]
    obtain ⟨x, hx⟩ : ∃ x, 64 * wOf s0 = x + 1 := ⟨64 * wOf s0 - 1, by omega⟩
    rw [hx, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]
  · have ne : ∀ k ∈ constArrs, k ≠ j := fun k hk e => hjn (e ▸ hk)
    rw [keepNum ft _ hj (Ne.symm (ne _ (by simp))), keepNum f6 _ hj (Ne.symm (ne _ (by simp))),
      keepNum f5 _ hj (Ne.symm (ne _ (by simp))), keepNum f4 _ hj (Ne.symm (ne _ (by simp))),
      keepNum f3 _ hj (Ne.symm (ne _ (by simp))), keepNum f2 _ hj (Ne.symm (ne _ (by simp))),
      keepNum f1 _ hj (Ne.symm (ne _ (by simp)))]

/-! ## The counts of `invOf` -/

theorem nP_ok (s : State) {L : Nat} (hl : s.gpr .a1 = BitVec.ofNat 64 L) :
    WP isa (.block nP) s fun v => (v.gpr .s7 = BitVec.ofNat 64 (8 * L) ∧ v.mem = s.mem) ∧ Keep [.s7] s v := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [nP, cnt8, hl, shl3_ofNat]

theorem nTwo_ok (s : State) :
    WP isa (.block nTwo) s fun v => (v.gpr .s7 = BitVec.ofNat 64 64 ∧ v.mem = s.mem) ∧ Keep [.s7] s v := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  have e : exec (.li .s7 64) s = some (s.write .s7 (BitVec.ofNat 64 64)) := exec_li_small (x := 64) (by decide)
  brun [nTwo, e]

theorem nW_ok (s : State) {L : Nat} (hl : s.gpr .a1 = BitVec.ofNat 64 L) :
    WP isa (.block nW) s fun v => (v.gpr .s7 = BitVec.ofNat 64 (8 * L + 32) ∧ v.mem = s.mem) ∧
      Keep [.s7] s v := by
  refine WP.keep _ ?_ (by rfl) (by rfl)
  brun [nW, cnt8, hl, shl3_ofNat]
  exact (BitVec.ofNat_add _ _).symm

end VG.Proof.RsaKeyGen.RISCV64.Key
