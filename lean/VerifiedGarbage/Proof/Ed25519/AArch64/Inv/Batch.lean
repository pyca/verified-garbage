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
applies; and it counts down. It writes only bytes 192 to 495. -/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64.Inv

open VG VG.AArch64 VG.Proof.Ed25519.Word64 VG.Proof.Ed25519.AArch64 VG.Spec.X25519
open VG.Proof.Mont.AArch64 (KeepRegs)
open VG.Proof.Divstep (MSt msteps)
open VG.Impl.Ed25519.AArch64 (ld st)
open VG.Impl.Ed25519.AArch64.Divstep (F G U V TF TG TU TV DSAVE CNT batch)

variable {large : Bool}

/-- The registers a batch may change. -/
abbrev batchRegs : List Reg :=
  [.x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17, .x19]

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
  c1 : t.gpr .x19 = (absW (BitVec.ofInt 64 T.q) &&& maskN (BitVec.ofInt 64 T.q)) +
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
              (maskN (BitVec.ofInt 64 b))).toNat)) % 2 ^ 320 =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % 2 ^ 320) :
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
              (maskN (BitVec.ofInt 64 b))).toNat)) % 2 ^ 320 =
        (((absW (BitVec.ofInt 64 a) &&& maskN (BitVec.ofInt 64 a)) +
            (absW (BitVec.ofInt 64 b) &&& maskN (BitVec.ofInt 64 b))).toNat +
          flip4 m base xo (maskN (BitVec.ofInt 64 a)) * (absW (BitVec.ofInt 64 a)).toNat +
          flip4 m base yo (maskN (BitVec.ofInt 64 b)) * (absW (BitVec.ofInt 64 b)).toNat) % 2 ^ 320) :
    (val5 m' base t : Int) % 2 ^ 320 = (a * fe m base xo + b * fe m base yo) % 2 ^ 320 := by
  rw [corrV_false_eq, corrV_false_eq, car_eq _ _ (by have := absN_le ha; have := absN_le hb; omega),
    flip4_eq, flip4_eq, absN_word, absN_word] at h
  have e := rowU_int (val4_lt _ _ _ _) (val4_lt _ _ _ _) h
  rwa [VG.Proof.Divstep.toInt_small ha, VG.Proof.Divstep.toInt_small hb] at e

end VG.Proof.Ed25519.AArch64.Inv
