module

public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Conn
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Out
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Step
public import VerifiedGarbage.Proof.Weierstrass.AArch64.InvPacked
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # A batch of the inversion modulo `p` on AArch64

A batch keeps the invariant (`batch_ok`): its divsteps are `dsM` (`pwords_ok`),
its rows are the matrix's combinations (`row_ok`, `rowF_int`, `rowU_int`),
shifted (`shift_ok`) or reduced (`reduce_ok`, `redV_cong`), so `step_inv`
applies; and it counts down. It writes only bytes 192 to 487. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64 VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs Keeps.regs)
open VG.Proof.Divstep (MSt msteps)
open VG.Proof.X25519.AArch64 (exec_movz)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (F G U V TF TG TU TV DSAVE batch shift reduce)

variable {large : Bool}

/-- The registers a batch may change. -/
abbrev batchRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x20]

/-- The low word of a field element, as an integer modulo `2⁶⁴`. -/
theorem low_rel {m : Mem} {base : Addr} {o : Nat} {f : Int} (h : sv (fe m base o) = f) :
    ((word m base o).toNat : Int) % 2 ^ 64 = f % 2 ^ 64 := by
  rw [← h]
  have := (word m base o).isLt
  have := (word m base (o + 8)).isLt
  have := (word m base (o + 16)).isLt
  have := (word m base (o + 24)).isLt
  unfold sv
  simp only [fe, val4]
  split <;> omega

theorem lds3_ok {s : State} {base : Addr} (hs : Scr s base large) :
    WP isa (.block [ld .x1 DSAVE, ld .x2 F, ld .x3 G]) s fun t =>
      t.gpr .x1 = word s.mem base DSAVE ∧ t.gpr .x2 = word s.mem base F ∧
      t.gpr .x3 = word s.mem base G ∧ Keeps [.x1, .x2, .x3] s t := by
  have _hmin := workSize_ge large
  change WP isa (.block (([ld .x1 DSAVE] : List Instr) ++ (([ld .x2 F] : List Instr) ++
    ([ld .x3 G] : List Instr)))) s _
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hs (by decide) (by simp only [DSAVE]; omega) .x1) fun a ⟨a1, ka⟩ => ?_
  have hsa := hs.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok hsa (by decide) (by simp only [F]; omega) .x2) fun b ⟨b2, kb⟩ => ?_
  have hsb := hsa.of_keeps kb (by decide)
  refine WP.mono (ld_ok hsb (by decide) (by simp only [G]; omega) .x3) fun t ⟨t3, kt⟩ => ?_
  refine ⟨by rw [kt.gpr _ (by decide), kb.gpr _ (by decide), a1],
    by rw [kt.gpr _ (by decide), b2, ka.mem], by rw [t3, kb.mem, ka.mem], ?_⟩
  exact (ka.mono (by decide)).trans ((kb.mono (by decide)).trans (kt.mono (by decide)))

/-- The registers after `mat`, for the matrix `T`. -/
structure MatRegs (T : MSt) (t : State) : Prop where
  z : t.gpr .x12 = 0
  u : t.gpr .x4 = absW (BitVec.ofInt 64 T.u)
  su : t.gpr .x14 = maskN (BitVec.ofInt 64 T.u)
  v : t.gpr .x5 = absW (BitVec.ofInt 64 T.v)
  sv' : t.gpr .x15 = maskN (BitVec.ofInt 64 T.v)
  q : t.gpr .x6 = absW (BitVec.ofInt 64 T.q)
  sq : t.gpr .x16 = maskN (BitVec.ofInt 64 T.q)
  r : t.gpr .x7 = absW (BitVec.ofInt 64 T.r)
  sr : t.gpr .x17 = maskN (BitVec.ofInt 64 T.r)
  c0 : t.gpr .x13 = (absW (BitVec.ofInt 64 T.u) &&& maskN (BitVec.ofInt 64 T.u)) +
    (absW (BitVec.ofInt 64 T.v) &&& maskN (BitVec.ofInt 64 T.v))
  c1 : t.gpr .x11 = (absW (BitVec.ofInt 64 T.q) &&& maskN (BitVec.ofInt 64 T.q)) +
    (absW (BitVec.ofInt 64 T.r) &&& maskN (BitVec.ofInt 64 T.r))

theorem MatRegs.keep {T : MSt} {t t' : State} (h : MatRegs T t)
    (k : KeepRegs [.x1, .x2, .x3, .x8, .x9, .x10] t t') : MatRegs T t' :=
  ⟨(k.gpr _ (by decide)).trans h.z, (k.gpr _ (by decide)).trans h.u, (k.gpr _ (by decide)).trans h.su,
    (k.gpr _ (by decide)).trans h.v, (k.gpr _ (by decide)).trans h.sv',
    (k.gpr _ (by decide)).trans h.q, (k.gpr _ (by decide)).trans h.sq,
    (k.gpr _ (by decide)).trans h.r, (k.gpr _ (by decide)).trans h.sr,
    (k.gpr _ (by decide)).trans h.c0, (k.gpr _ (by decide)).trans h.c1⟩

theorem absW_le {u : Int} (h : |u| ≤ 2 ^ 59) : (absW (BitVec.ofInt 64 u)).toNat ≤ 2 ^ 62 := by
  rw [absN_word]
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega

theorem absN_le {u : Int} (h : |u| ≤ 2 ^ 59) : absN (BitVec.ofInt 64 u) ≤ 2 ^ 59 := by
  unfold absN
  rw [VG.Proof.Divstep.toInt_small h]
  rw [Int.abs_eq_natAbs] at h
  omega

/-- A row of `f` and `g` as the code leaves it, as integers. -/
theorem rowF_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV true (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV true (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * sv (fe m base xo) + b * sv (fe m base yo)) % 2 ^ 320 := by
  rw [corrV_true_eq, corrV_true_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  have e := rowF_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

/-- A row of `u` and `v` as the code leaves it, as integers. -/
theorem rowU_rel {m m' : Mem} {base : Addr} {t xo yo : Nat} {a b : Int}
    (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59)
    (h : (val5 m' base t + 2 ^ 256 *
          ((corrV false (word m base (xo + 24) ^^^ maskN (BitVec.ofInt 64 a)) (absW (BitVec.ofInt 64 a))
              (maskN (BitVec.ofInt 64 a))).toNat +
            (corrV false (word m base (yo + 24) ^^^ maskN (BitVec.ofInt 64 b)) (absW (BitVec.ofInt 64 b))
              (maskN (BitVec.ofInt 64 b))).toNat)) % (2 ^ 256 * 2 ^ 64) =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % (2 ^ 256 * 2 ^ 64)) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * fe m base xo + b * fe m base yo) % 2 ^ 320 := by
  rw [corrV_false_eq, corrV_false_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  have e := rowU_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

theorem prod_bnd {a : Int} {U : Nat} (ha : |a| ≤ 2 ^ 59) (hU : U < 2 ^ 256) :
    -(2 ^ 59 * 2 ^ 256) ≤ a * U ∧ a * U ≤ 2 ^ 59 * 2 ^ 256 := by
  have h0 : (0 : Int) ≤ U := by positivity
  have h1 : (U : Int) ≤ 2 ^ 256 := by exact_mod_cast hU.le
  rw [abs_le] at ha
  have p1 := mul_nonneg (by linarith : (0 : Int) ≤ a + 2 ^ 59) h0
  have p2 := mul_nonneg (by linarith : (0 : Int) ≤ 2 ^ 59 - a) h0
  rw [add_mul] at p1
  rw [sub_mul] at p2
  constructor <;> linarith

theorem sum_bnd {a b : Int} {U V : Nat} (ha : |a| ≤ 2 ^ 59) (hb : |b| ≤ 2 ^ 59) (hU : U < 2 ^ 256)
    (hV : V < 2 ^ 256) : -2 ^ 317 ≤ a * U + b * V ∧ a * U + b * V < 2 ^ 317 := by
  have h1 := prod_bnd ha hU
  have h2 := prod_bnd hb hV
  have hK : (0 : Int) < 2 ^ 59 * 2 ^ 256 := by positivity
  rw [show (2 : Int) ^ 317 = 2 ^ 59 * 2 ^ 256 * 2 ^ 2 by rw [← pow_add, ← pow_add]]
  generalize (2 : Int) ^ 59 * 2 ^ 256 = K at h1 h2 hK ⊢
  constructor <;> linarith

theorem val5_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) : val5 m' base t = val5 m base t := by
  simp only [val5]
  rw [h.fe (by omega) (by omega), h.word (by omega) (by omega)]

theorem cnt_val {i : Nat} (hi : i < 10) :
    BitVec.ofNat 64 (10 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (10 - (i + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem scr_of {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base large)
    (h : KeepRegs rs s s') (hr : .x0 ∉ rs) : Scr s' base large :=
  ⟨(h.gpr _ hr).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

/-- The counter one down. -/
theorem cnt_ok (s : State) {i : Nat} (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block [.subImm .x .x20 .x20 1]) s fun t =>
      t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧ Keeps [.x20] s t :=
  WP.block_cons_iff.mpr ⟨_, exec_subImm_x (imm := 1) (by decide), WP.block_nil
    ⟨by
      rw [RegUpd.gpr_write_self, BitVec.setWidth_eq]
      simp only [State.read, hc]
      exact cnt_val hi,
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩

/-- The five words at `t` reduced, as they were before bytes outside them changed. -/
theorem redV_out {base : Addr} {o n t : Nat} {m m' : Mem} (h : Outside base o n m m')
    (ht : t + 40 ≤ o ∨ o + n ≤ t) (hl : t + 40 < 2 ^ 64) :
    redV (word m' base t) (word m' base (t + 8)) (word m' base (t + 16)) (word m' base (t + 24))
        (word m' base (t + 32)) =
      redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
        (word m base (t + 32)) := by
  rw [h.word (by omega) (by omega), h.word (by omega) (by omega), h.word (by omega) (by omega),
    h.word (by omega) (by omega), h.word (by omega) (by omega)]

/-- Five words at `t` reduced. -/
abbrev red5 (m : Mem) (base : Addr) (t : Nat) : Nat :=
  redV (word m base t) (word m base (t + 8)) (word m base (t + 16)) (word m base (t + 24))
    (word m base (t + 32))

/-- The rows shifted and reduced, and the counter one down. -/
theorem outs_ok {s : State} {base : Addr} (hs : Scr s base large) (hz : s.gpr .x12 = 0) {i : Nat}
    (hi : i < 10) (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block (shift F TF ++ (shift G TG ++ ([.movz .x .x13 19 0] ++ (reduce U TU ++
        (reduce V TV ++ ([.subImm .x .x20 .x20 1] : List Instr))))))) s
      fun t =>
        fe t.mem base F = val5 s.mem base TF / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base G = val5 s.mem base TG / 2 ^ 59 % 2 ^ 256 ∧
        fe t.mem base U = red5 s.mem base TU ∧ fe t.mem base V = red5 s.mem base TV ∧
        t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧
        word t.mem base DSAVE = word s.mem base DSAVE ∧
        Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hs (o := F) (t := TF) ⟨by decide, by simp only [F]; omega⟩
    ⟨by decide, by simp only [TF]; omega⟩) fun a ⟨a1, oa, ka⟩ => ?_
  have hsa := scr_of hs ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (shift_ok hsa (o := G) (t := TG) ⟨by decide, by simp only [G]; omega⟩
    ⟨by decide, by simp only [TG]; omega⟩) fun b ⟨b1, ob, kb⟩ => ?_
  have hsb := scr_of hsa kb (by decide)
  rw [WP.block_append_iff]
  have hm : WP isa (.block [.movz .x .x13 19 0]) b fun c => c.gpr .x13 = 19 ∧ Keeps [.x13] b c :=
    WP.block_cons_iff.mpr ⟨_, exec_movz, WP.block_nil ⟨(RegUpd.gpr_write_self _ _ _ _).trans (by decide),
      ⟨fun r hr => RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr),
        rfl, rfl, rfl, rfl⟩⟩⟩
  refine WP.mono hm fun c ⟨c13, kc⟩ => ?_
  have hsc := hsb.of_keeps kc (by decide)
  have zc : c.gpr .x12 = 0 := by
    rw [kc.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hz]
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsc (o := U) (t := TU) zc c13 ⟨by decide, by simp only [U]; omega⟩
    ⟨by decide, by simp only [TU]; omega⟩) fun d ⟨d1, od, kd⟩ => ?_
  have hsd := scr_of hsc kd (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (reduce_ok hsd (o := V) (t := TV) ((kd.gpr _ (by decide)).trans zc)
    ((kd.gpr _ (by decide)).trans c13) ⟨by decide, by simp only [V]; omega⟩
    ⟨by decide, by simp only [TV]; omega⟩) fun e ⟨e1, oe, ke⟩ => ?_
  have hse := scr_of hsd ke (by decide)
  have mc : c.mem = b.mem := kc.mem
  have cnt : e.gpr .x20 = BitVec.ofNat 64 (10 - i) := by
    rw [ke.gpr _ (by decide), kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide),
      ka.gpr _ (by decide), hc]
  refine WP.mono (cnt_ok e hi cnt) fun t ⟨t20, kt⟩ => ?_
  have ot : Outside base 488 0 e.mem t.mem := by rw [kt.mem]; exact Outside.refl _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, t20, ?_, ?_, ?_⟩
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, ob.fe (by decide) (by decide), a1]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), od.fe (by decide) (by decide),
      mc, b1, val5_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), oe.fe (by decide) (by decide), d1, mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.fe (by decide) (by decide), e1, redV_out od (by decide) (by decide), mc,
      redV_out ob (by decide) (by decide), redV_out oa (by decide) (by decide)]
  · rw [ot.word (by decide) (by decide), oe.word (by decide) (by decide),
      od.word (by decide) (by decide), mc, ob.word (by decide) (by decide),
      oa.word (by decide) (by decide)]
  · exact ((((oa.mono (by decide) (by decide)).trans (ob.mono (by decide) (by decide))).trans
      (mc ▸ (od.mono (by decide) (by decide)))).trans (oe.mono (by decide) (by decide))).trans
      (ot.mono (by decide) (by decide))
  · exact ((((ka.mono (by decide)).trans (kb.mono (by decide))).trans
      (((Keeps.regs kc).mono (by decide)).trans (kd.mono (by decide)))).trans (ke.mono (by decide))).trans
      ((Keeps.regs kt).mono (by decide))

/-- A batch: the invariant one batch on, and the counter one down. -/
theorem batch_ok {s : State} {base : Addr} (hs : Scr s base large) {x i : Nat} (hx : x < P)
    (hi : i < 10)
    (h : RInv x i (word s.mem base DSAVE) (fe s.mem base F) (fe s.mem base G) (fe s.mem base U)
      (fe s.mem base V))
    (hc : s.gpr .x20 = BitVec.ofNat 64 (10 - i)) :
    WP isa (.block batch) s fun t =>
      RInv x (i + 1) (word t.mem base DSAVE) (fe t.mem base F) (fe t.mem base G) (fe t.mem base U)
        (fe t.mem base V) ∧
      t.gpr .x20 = BitVec.ofNat 64 (10 - (i + 1)) ∧
      Outside base 192 296 s.mem t.mem ∧ KeepRegs batchRegs s t := by
  have _hmin := workSize_ge large
  have _hcap := workSize_le large
  obtain ⟨hD, hF, hG, hFl, hGl, hUl, hVl, _, _, _⟩ := id h
  have hd30 : |(dsI x i).1| ≤ 2 ^ 30 := by
    have := dsI_d x i
    have : (59 * i : Int) ≤ 59 * 9 := by exact_mod_cast (by omega : 59 * i ≤ 59 * 9)
    linarith
  obtain ⟨bu, bv, bq, br⟩ := dsM_bnd x i
  simp only [batch, List.append_assoc]
  -- the divsteps
  rw [WP.block_append_iff]
  refine WP.mono (lds3_ok hs) fun a ⟨a1, a2, a3, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (VG.Proof.Weierstrass.AArch64.pwords_ok a (f := (dsI x i).2.1) (g := (dsI x i).2.2)
    hd30 (dsI_odd x i).2 (a1.trans hD)
    (by rw [a2]; exact low_rel hF) (by rw [a3]; exact low_rel hG))
    fun b ⟨b1, b4, b5, b6, b7, kb⟩ => ?_
  have hsb : Scr b base large := (hs.of_keeps ka (by decide)).of_keeps kb (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (st_ok hsb (d := DSAVE) (by decide) (by simp only [DSAVE]; omega) .x1)
    fun c ⟨mc, kc⟩ => ?_
  have hsc : Scr c base large := ⟨(kc.gpr _ (by decide)).trans hsb.x0, kc.wr ▸ hsb.wr, hs.nowrap⟩
  rw [WP.block_append_iff]
  refine WP.mono (mat_ok c) fun d ⟨d12, d4, d14, d5, d15, d6, d16, d7, d17, d13, d19, kd⟩ => ?_
  have hsd : Scr d base large := hsc.of_keeps kd (by decide)
  have gc : ∀ r, c.gpr r = b.gpr r := fun r => kc.gpr r (by simp)
  have md : MatRegs (dsM x i) d := ⟨d12, by rw [d4, gc, b4], by rw [d14, gc, b4], by rw [d5, gc, b5],
    by rw [d15, gc, b5], by rw [d6, gc, b6], by rw [d16, gc, b6], by rw [d7, gc, b7],
    by rw [d17, gc, b7], by rw [d13, gc, gc, b4, b5], by rw [d19, gc, gc, b6, b7]⟩
  -- the memory the rows read
  have mb : b.mem = s.mem := by rw [kb.mem, ka.mem]
  have mdm : d.mem = s.mem.writeW (off base DSAVE) (BitVec.ofInt 64 (dsM x i).d) := by
    rw [kd.mem, mc, mb, b1]
  have od : Outside base 480 8 s.mem d.mem := by
    rw [mdm]; exact writeW_outside _ _ _ (by decide)
  have fd : ∀ o, o + 32 ≤ 480 → fe d.mem base o = fe s.mem base o := fun o ho =>
    od.fe (Or.inl ho) (by omega)
  -- the rows
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hsd true (t := TF) (xo := F) (yo := G) (by decide) (by decide) md.z
    (by rw [md.u]; exact absW_le bu) (by rw [md.v]; exact absW_le bv)
    ⟨by decide, by simp only [TF]; omega⟩ ⟨by decide, by simp only [F]; omega⟩
    ⟨by decide, by simp only [G]; omega⟩ (by decide) (by decide)) fun e1 ⟨r1, o1, k1⟩ => ?_
  have hs1 : Scr e1 base large := ⟨(k1.gpr _ (by decide)).trans hsd.x0, k1.wr ▸ hsd.wr, hs.nowrap⟩
  have m1 := md.keep k1
  rw [md.u, md.su, md.v, md.sv', md.c0] at r1
  have hWF := rowF_rel (m := d.mem) (m' := e1.mem) (base := base) (t := TF) (xo := F) (yo := G) bu bv r1
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs1 true (t := TG) (xo := F) (yo := G) (by decide) (by decide) m1.z
    (by rw [m1.q]; exact absW_le bq) (by rw [m1.r]; exact absW_le br)
    ⟨by decide, by simp only [TG]; omega⟩ ⟨by decide, by simp only [F]; omega⟩
    ⟨by decide, by simp only [G]; omega⟩ (by decide) (by decide)) fun e2 ⟨r2, o2, k2⟩ => ?_
  have hs2 : Scr e2 base large := ⟨(k2.gpr _ (by decide)).trans hs1.x0, k2.wr ▸ hs1.wr, hs.nowrap⟩
  have m2 := m1.keep k2
  rw [m1.q, m1.sq, m1.r, m1.sr, m1.c1] at r2
  have hWG := rowF_rel (m := e1.mem) (m' := e2.mem) (base := base) (t := TG) (xo := F) (yo := G) bq br r2
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs2 false (t := TU) (xo := U) (yo := V) (by decide) (by decide) m2.z
    (by rw [m2.u]; exact absW_le bu) (by rw [m2.v]; exact absW_le bv)
    ⟨by decide, by simp only [TU]; omega⟩ ⟨by decide, by simp only [U]; omega⟩
    ⟨by decide, by simp only [V]; omega⟩ (by decide) (by decide)) fun e3 ⟨r3, o3, k3⟩ => ?_
  have hs3 : Scr e3 base large := ⟨(k3.gpr _ (by decide)).trans hs2.x0, k3.wr ▸ hs2.wr, hs.nowrap⟩
  have m3 := m2.keep k3
  rw [m2.u, m2.su, m2.v, m2.sv', m2.c0] at r3
  have hWU := rowU_rel (m := e2.mem) (m' := e3.mem) (base := base) (t := TU) (xo := U) (yo := V) bu bv r3
  rw [WP.block_append_iff]
  refine WP.mono (row_ok hs3 false (t := TV) (xo := U) (yo := V) (by decide) (by decide) m3.z
    (by rw [m3.q]; exact absW_le bq) (by rw [m3.r]; exact absW_le br)
    ⟨by decide, by simp only [TV]; omega⟩ ⟨by decide, by simp only [U]; omega⟩
    ⟨by decide, by simp only [V]; omega⟩ (by decide) (by decide)) fun e4 ⟨r4, o4, k4⟩ => ?_
  have hs4 : Scr e4 base large := ⟨(k4.gpr _ (by decide)).trans hs3.x0, k4.wr ▸ hs3.wr, hs.nowrap⟩
  have m4 := m3.keep k4
  rw [m3.q, m3.sq, m3.r, m3.sr, m3.c1] at r4
  have hWV := rowU_rel (m := e3.mem) (m' := e4.mem) (base := base) (t := TV) (xo := U) (yo := V) bq br r4
  -- the shifts, the reductions and the counter
  have cnt4 : e4.gpr .x20 = BitVec.ofNat 64 (10 - i) := by
    rw [k4.gpr _ (by decide), k3.gpr _ (by decide), k2.gpr _ (by decide), k1.gpr _ (by decide),
      kd.gpr _ (by decide), kc.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hc]
  refine WP.mono (outs_ok hs4 m4.z hi cnt4) fun t ⟨tF, tG, tU, tV, t20, tD, ot, kt⟩ => ?_
  -- what the rows read, as it was in `s`
  have f1 : ∀ o, o + 32 ≤ TF → fe e1.mem base o = fe s.mem base o := fun o ho => by
    rw [o1.fe (Or.inl ho) (by simp only [TF] at ho; omega), fd o (by simp only [TF] at ho; omega)]
  have f2 : ∀ o, o + 32 ≤ TF → fe e2.mem base o = fe s.mem base o := fun o ho => by
    rw [o2.fe (Or.inl (by simp only [TF, TG] at ho ⊢; omega)) (by simp only [TF] at ho; omega), f1 o ho]
  rw [f1 _ (by decide), f1 _ (by decide), hF, hG] at hWG
  rw [fd _ (by decide), fd _ (by decide), hF, hG] at hWF
  have f3 : ∀ o, o + 32 ≤ TF → fe e3.mem base o = fe s.mem base o := fun o ho => by
    rw [o3.fe (Or.inl (by simp only [TF, TU] at ho ⊢; omega)) (by simp only [TF] at ho; omega), f2 o ho]
  rw [f2 _ (by decide), f2 _ (by decide)] at hWU
  rw [f3 _ (by decide), f3 _ (by decide)] at hWV
  -- the rows where the shifts and reductions read them
  have vF : val5 e4.mem base TF = val5 e1.mem base TF := by
    rw [val5_out o4 (by decide) (by decide), val5_out o3 (by decide) (by decide),
      val5_out o2 (by decide) (by decide)]
  have vG : val5 e4.mem base TG = val5 e2.mem base TG := by
    rw [val5_out o4 (by decide) (by decide), val5_out o3 (by decide) (by decide)]
  have vU : red5 e4.mem base TU = red5 e3.mem base TU := redV_out o4 (by decide) (by decide)
  have hU := redV_cong _ _ _ _ _ hWU (sum_bnd bu bv hUl hVl)
  have hV := redV_cong _ _ _ _ _ hWV (sum_bnd bq br hUl hVl)
  have hR := step_inv hx h hWF hWG hU (Nat.mod_lt _ (by decide)) hV (Nat.mod_lt _ (by decide))
  have dD : word t.mem base DSAVE = BitVec.ofInt 64 (dsM x i).d := by
    rw [tD, o4.word (by decide) (by decide), o3.word (by decide) (by decide),
      o2.word (by decide) (by decide), o1.word (by decide) (by decide), mdm, word_writeW_self]
  refine ⟨?_, t20, ?_, ?_⟩
  · rw [dD, tF, tG, tU, tV, vF, vG, vU]
    exact hR
  · exact ((((od.mono (by decide) (by decide)).trans (o1.mono (by decide) (by decide))).trans
      (o2.mono (by decide) (by decide))).trans ((o3.mono (by decide) (by decide)).trans
      (o4.mono (by decide) (by decide)))).trans ot
  · exact ((((Keeps.regs ka).mono (by decide)).trans ((Keeps.regs kb).mono (by decide))).trans
      ((kc.mono (by decide)).trans ((Keeps.regs kd).mono (by decide)))).trans
      ((((k1.mono (by decide)).trans (k2.mono (by decide))).trans
        ((k3.mono (by decide)).trans (k4.mono (by decide)))).trans kt)

end VG.Proof.Ed25519.AArch64.Inv
