module
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Mat
public import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Row
public import VerifiedGarbage.Proof.Divstep.BatchBasic

import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Conn
import VerifiedGarbage.Proof.Ed25519.AArch64.Inv.Out
import VerifiedGarbage.Proof.X25519.AArch64.Ops
import VerifiedGarbage.Proof.Divstep.Tc
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd

/-! # A batch of the inversion modulo `p` on AArch64

What a batch's proof (`DivstepSound.batch_ok`) is built from: its rows are the
matrix's combinations (`row_ok`, `rowF_rel`, `rowU_rel`), shifted and reduced
(`outs_ok`: `shift_ok`, `reduce_ok`), and it counts down. -/

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
    WP isa (.block (shift F TF ++ (shift G TG ++ (([.movz .x .x13 19 0] : List Instr) ++ (reduce U TU ++
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

end VG.Proof.Ed25519.AArch64.Inv
