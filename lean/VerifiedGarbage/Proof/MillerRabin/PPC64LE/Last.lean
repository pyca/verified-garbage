module

import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import Mathlib.Tactic.SplitIfs

/-! ### `MillerRabin.PPC64LE.Exp`, which this module and modules that import it used -/

section

/-! ### `MillerRabin.PPC64LE.Window`, which this module and modules that import it used -/

section

/-!
# The Miller–Rabin round on PPC64LE: a window

`y` is `Y R mod c` in array 6 and the flag `P` is a mask in `r23`.
`square_ok`: `RsaKeyGen.wSq`, a squaring that or's the flag with `y = −1`;
`select_ok`: `T_d` into array 5 by a scan of the whole table; `update_ok`:
the flag after `y := y T_d`; `window_ok`: `RsaKeyGen.wWin`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (mont_val mont_eq_m1 mont_eq_one wSq wWin)

theorem mask_or (p q : Bool) : mask p ||| mask q = mask (p || q) := by cases p <;> cases q <;> rfl

/-- The registers a squaring writes. -/
def sqRegs : List Reg := Pub.montRegs ++ eqRegs .r20 ++ [.r23]

/-- `square`: `y := y²`, the flag or'ed with `y = −1` (`wSq c true`). -/
theorem square_ok {s : State} {B : Addr} {Z w c Y : Nat} {P : Bool} (h : MCtx s B Z w)
    (hc : Consts s.mem B w c) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c) (h23 : s.gpr .r23 = mask P) :
    WP isa square s fun t =>
      (arr t.mem B w aY = (wSq c true (Y, P)).1 * 2 ^ (64 * w) % c ∧ (wSq c true (Y, P)).1 < c ∧
        t.gpr .r23 = mask (wSq c true (Y, P)).2 ∧
        Outs B (montRanges w 6) s.mem t.mem ∧ w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) ∧
      Keep sqRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain hn : slot w 28 ≤ 2 ^ 64 := by have := h.hs.nowrap; have := h.hZ; omega_arith
  have hcc := hc.cand
  unfold square
  refine WP.seq (WP.mono (mont_ok h (o := 6) (a := 6) (b := 6) (by simp) (by simp) (by simp)
    (by rw [show (6 : Nat) = aY from rfl, hy, hcc]; exact Nat.mod_lt _ (by omega_arith)))
    fun u ⟨⟨hlt, heq, hout, h0⟩, ku⟩ => ?_)
  obtain hu := h.keep ku (by decide) h0
  rw [hcc] at hlt heq
  obtain uy : arr u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := mont_val hR hlt heq hy hy
  obtain u10 : arr u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
    rw [Outs.arrEq_mont hout (by decide) (by decide) (by decide) (by decide) hn, hc.minus]
  refine WP.seq (WP.mono (eqMask_ok hu.toEnv .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v20, vm⟩, kv⟩ => ?_)
  obtain hblk : WP isa (.block [.logic .or .r23 .r23 .r20]) v fun t =>
      (t.gpr .r23 = v.gpr .r23 ||| v.gpr .r20 ∧ t.mem = v.mem) ∧ Keep [.r23] v t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨⟨?_, Nat.mod_lt _ (by omega_arith), ?_, ?_, ?_⟩, ?_⟩
  · rw [tm, vm, uy]; rfl
  · have e : (decide (arr u.mem B w aY = arr u.mem B w aMinus)) = decide (Y * Y % c = c - 1) := by
      rw [uy, u10]
      exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega_arith) (Nat.mod_lt _ (by omega_arith)))
    rw [t23, v20, (kv.gpr .r23 (by decide)).trans ((ku.gpr .r23 (by decide)).trans h23), e, mask_or]
    rfl
  · rw [tm, vm]; exact hout
  · rw [tm, vm, h0]
  · exact ((ku.trans kv).trans kt).mono (by simp [sqRegs])

/-! ## Selecting `T_d` -/

theorem isDigit_ok {s : State} {j d : Nat} (h30 : s.gpr .r30 = BitVec.ofNat 64 j)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) :
    WP isa (.block isDigit) s fun t => (t.gpr .r20 = mask (decide (j = d)) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r3, .r20] s t := by
  obtain hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  obtain he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by decide)
  unfold isDigit
  prun [h30, h28, sub1_sign hx]
  by_cases e : j = d
  · simp [e]
  · simp [e, show ¬ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0#64) from fun h => e (he.mp h)]

/-- The registers a choice of an entry writes. -/
def pickRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- Array `o := j = d ? T_j : [t]`, for `j` in `r30` and `d` in `r28`. -/
theorem pick_ok {s : State} {B : Addr} {Z w j d : Nat} (h : Env s B Z w) (h30 : s.gpr .r30 = BitVec.ofNat 64 j)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) {o t : Nat}
    (hot : o = 3 ∧ t = 5 ∨ o = 5 ∧ t = 3) :
    WP isa (.seq (.block (isDigit ++ entry ++ PublicChecked.base .r9 t ++ PublicChecked.base .r5 o)) selectAcc64) s
      fun s' => (arr s'.mem B w o = (if j = d then arr s.mem B w (11 + j) else arr s.mem B w t) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem s'.mem) ∧ Keep pickRegs s s' := by
  obtain ho : o < 28 := by omega_arith
  obtain ht : t < 28 := by omega_arith
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isDigit_ok h30 h28 hj hd) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  obtain e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) e1 (by rw [k1.gpr .r30 (by decide), h30])) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  obtain e2 := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2.base (rd := .r9) (by decide) (by decide) t) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  obtain e3 := e2.keep k3 (by decide)
  refine WP.mono (e3.base (rd := .r5) (by decide) (by decide) o) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  obtain e4 := e3.keep k4 (by decide)
  obtain hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok e4 (b := decide (j = d)) (o := o) (a := 11 + j) (t := t) ho (by omega_arith) ht
      (by omega_arith) (by omega_arith) a5
      (by rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8])
      (by rw [k4.gpr .r9 (by decide), a9])
      (by rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), h20]))
    fun s' ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  refine ⟨⟨by rw [hv]; by_cases e : j = d <;> simp [e], hout⟩, ?_⟩
  exact ((((k1.trans k2).trans k3).trans k4).trans k).mono (by simp [pickRegs])

theorem wp_seq_assoc {a b c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.seq a b) s fun t => WP isa c t Q) : WP isa (.seq a (.seq b c)) s Q := by
  obtain ⟨_, _, he, _, _, he', hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, .seq e1 (.seq e2 he'), hq⟩

theorem wp_seq_inv {a b : Prog isa} {s : State} {Q : State → Prop} (h : WP isa (.seq a b) s Q) :
    WP isa a s fun t => WP isa b t Q := by
  obtain ⟨_, _, he, hq⟩ := h
  cases he with
  | seq e1 e2 => exact ⟨_, _, e1, _, _, e2, hq⟩

theorem wp_block_prefix_seq {l₁ l₂ : List Instr} {c : Prog isa} {s : State} {Q : State → Prop}
    (h : WP isa (.block l₁) s fun t => WP isa (.seq (.block l₂) c) t Q) :
    WP isa (.seq (.block (l₁ ++ l₂)) c) s Q := by
  refine WP.seq ?_
  rw [WP.block_append_iff]
  exact WP.mono h fun _ h' => wp_seq_inv h'

/-- What the selection of `T_d` writes. -/
def selectRanges (w : Nat) : List (Nat × Nat) := [(slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2))]

/-- The registers the selection writes. -/
def selectRegs : List Reg := pickRegs ++ [.r30, .r4]

/-- `select`: array 5 := `T_d`, for `d` in `r28`. -/
theorem select_ok {s : State} {B : Addr} {Z w d : Nat} (h : Env s B Z w) (h28 : s.gpr .r28 = BitVec.ofNat 64 d)
    (hd : d < 16) :
    WP isa select s fun t =>
      (arr t.mem B w 5 = arr s.mem B w (11 + d) ∧ Outs B (selectRanges w) s.mem t.mem) ∧ Keep selectRegs s t := by
  obtain hn : slot w 28 ≤ 2 ^ 64 := by have := h.hs.nowrap; have := h.hZ; omega_arith
  obtain keepT : ∀ {m : Mem}, Outs B (selectRanges w) s.mem m → ∀ i < 16, arr m B w (11 + i) = arr s.mem B w (11 + i) :=
    fun hm i hi => Outs.arrEq hm (by omega_arith) (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slot_sep (by omega_arith)) hn
  obtain fr3 : ∀ {m m' : Mem}, Outside B (slot w 3) (8 * (w + 2)) m m' → Outs B (selectRanges w) m m' :=
    fun h => Outs.of_outside h (by simp [selectRanges])
  obtain fr5 : ∀ {m m' : Mem}, Outside B (slot w 5) (8 * (w + 2)) m m' → Outs B (selectRanges w) m m' :=
    fun h => Outs.of_outside h (by simp [selectRanges])
  unfold select
  obtain hpre : WP isa (.block [.li .r30 0]) s fun t => (t.gpr .r30 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ∧
      Keep [.r30] s t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.seq (WP.mono hpre fun t₀ ⟨⟨a30, m0⟩, k0⟩ => ?_)
  let I : Nat → State → Prop := fun k t => Env t B Z w ∧ t.gpr .r28 = BitVec.ofNat 64 d ∧
    t.gpr .r30 = BitVec.ofNat 64 (2 * k) ∧
    arr t.mem B w 5 = (if d < 2 * k then arr s.mem B w (11 + d) else arr s.mem B w 5) ∧
    Outs B (selectRanges w) s.mem t.mem ∧ Keep selectRegs s t
  refine WP.mono (count_loop (n := 8) (cr := .r4) (by decide) I (fun k hk t ⟨et, t28, t30, t5, tout, kt⟩ => ?_)
    ⟨h.keep k0 (by decide), by rw [k0.gpr .r28 (by decide), h28], a30, (by rw [m0]; simp),
      (by rw [m0]; exact Outs.refl _ _ _), k0.mono (by decide)⟩) fun t ⟨_, _, _, t5, tout, kt⟩ => ⟨⟨by rw [t5, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))],
        tout⟩, kt⟩
  -- the first entry of the pair
  refine wp_seq_assoc (WP.mono (pick_ok et t30 t28 (by omega_arith) hd (o := 3) (t := 5) (by simp))
    fun u ⟨⟨u3, uo⟩, ku⟩ => ?_)
  obtain eu := et.keep ku (by decide)
  -- the second
  rw [show ([.addi .r30 .r30 1] ++ isDigit ++ entry ++ PublicChecked.base .r9 aT ++ PublicChecked.base .r5 aW) =
      [.addi .r30 .r30 1] ++ (isDigit ++ entry ++ PublicChecked.base .r9 aT ++ PublicChecked.base .r5 aW) by
    simp only [List.append_assoc]]
  refine wp_seq_assoc (wp_block_prefix_seq ?_)
  obtain hinc : WP isa (.block [.addi .r30 .r30 1]) u fun v =>
      (v.gpr .r30 = BitVec.ofNat 64 (2 * k + 1) ∧ v.mem = u.mem) ∧ Keep [.r30] u v := by
    refine WP.keep _ ?_ (by decide)
    prun [(ku.gpr .r30 (by decide)).trans t30, ← BitVec.ofNat_add]
  refine WP.mono hinc fun v ⟨⟨v30, vm⟩, kv⟩ => ?_
  obtain ev := eu.keep kv (by decide)
  refine (WP.mono (pick_ok ev v30 (by rw [kv.gpr .r28 (by decide), ku.gpr .r28 (by decide), t28])
    (by omega_arith) hd (o := 5) (t := 3) (by simp)) fun x ⟨⟨x5, xo⟩, kx⟩ => ?_)
  obtain ex := ev.keep kx (by decide)
  obtain hend : WP isa (.block [.addi .r30 .r30 1, .subi .r4 .r30 16]) x fun y =>
      (y.gpr .r30 = BitVec.ofNat 64 (2 * (k + 1)) ∧
        y.gpr .r4 = BitVec.ofNat 64 (2 * (k + 1)) - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧ Keep [.r30, .r4] x y := by
    refine WP.keep _ ?_ (by decide)
    prun [(kx.gpr .r30 (by decide)).trans v30, ← BitVec.ofNat_add,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega_arith]
  refine WP.mono hend fun y ⟨⟨y30, y4, ym⟩, ky⟩ => ⟨⟨ex.keep ky (by decide), by
    rw [ky.gpr .r28 (by decide), kx.gpr .r28 (by decide), kv.gpr .r28 (by decide), ku.gpr .r28 (by decide), t28],
    y30, ?_, ?_, ?_⟩, ?_⟩
  · -- array 5
    obtain o5 : Outs B (selectRanges w) s.mem x.mem :=
      Outs.trans (Outs.trans tout (fr3 uo)) (by rw [← vm]; exact fr5 xo)
    rw [ym, x5, vm, u3, t5, keepT (Outs.trans tout (fr3 uo)) _ (by omega_arith), keepT tout _ (by omega_arith)]
    split_ifs <;> (try subst_vars) <;> first | rfl | (exfalso; omega_arith)
  · rw [ym]
    exact Outs.trans (Outs.trans tout (fr3 uo)) (by rw [← vm]; exact fr5 xo)
  · exact (kt.trans ((((ku.trans kv).trans kx).trans ky))).mono (by simp [selectRegs, pickRegs])
  · rw [y4, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

/-! ## The flag after a window -/

theorem upd_arith (p P z : Bool) :
    mask P ^^^ ((mask p ^^^ mask P) &&& mask z) = mask (if z then p else P) := by
  cases p <;> cases P <;> cases z <;> decide

theorem nz_mask {d : Nat} (hd : d < 16) :
    BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - BitVec.ofNat 64 d) >>> 63 = mask (decide (d ≠ 0)) := by
  have : (BitVec.ofNat 64 0 - BitVec.ofNat 64 d) >>> 63 = BitVec.ofNat 64 (if d ≠ 0 then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    split <;> omega_arith
  rw [this]
  by_cases e : d ≠ 0 <;> simp [e, mask]

/-- The registers the update of the flag writes. -/
def updRegs : List Reg := eqRegs .r20 ++ eqRegs .r19 ++ [.r23]

/-- `update`: after `y := y T_d`, `P := d ≠ 0 ? (y = 1 ∨ y = −1) : P`. -/
theorem update_ok {s : State} {B : Addr} {Z w c Y d : Nat} {P : Bool} (h : Env s B Z w)
    (hc : Consts s.mem B w c) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c) (hY : Y < c) (h23 : s.gpr .r23 = mask P)
    (h28 : s.gpr .r28 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa update s fun t =>
      (t.gpr .r23 = mask (if d = 0 then P else decide (Y = 1) || decide (Y = c - 1)) ∧ t.mem = s.mem) ∧
        Keep updRegs s t := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold update
  refine WP.seq (WP.mono (eqMask_ok h .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun u ⟨⟨u20, um⟩, ku⟩ => ?_)
  obtain eu := h.keep ku (by decide)
  refine WP.seq (WP.mono (eqMask_ok eu .r19 (a := aY) (b := aOne) (by decide) (by decide))
    fun v ⟨⟨v19, vm⟩, kv⟩ => ?_)
  obtain hblk : WP isa (.block [.logic .or .r20 .r20 .r19, .li .r0 0, .sub .r3 .r0 .r28, .lsr .d .r3 .r3 63,
      .sub .r3 .r0 .r3, .logic .xor .r20 .r20 .r23, .logic .and .r20 .r20 .r3, .logic .xor .r23 .r23 .r20]) v
      fun t => (t.gpr .r23 = v.gpr .r23 ^^^ (((v.gpr .r20 ||| v.gpr .r19) ^^^ v.gpr .r23) &&&
        (BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - v.gpr .r28) >>> 63)) ∧ t.mem = v.mem) ∧
        Keep [.r0, .r3, .r20, .r23] v t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, vm, um]⟩, ((ku.trans kv).trans kt).mono
    (by simp [updRegs, eqRegs])⟩
  obtain e1 : decide (arr s.mem B w aY = arr s.mem B w aMinus) = decide (Y = c - 1) := by
    rw [hy, hc.minus]
    exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega_arith) hY)
  obtain e2 : decide (arr s.mem B w aY = arr s.mem B w aOne) = decide (Y = 1) := by
    rw [hy, hc.one]
    exact decide_eq_decide.mpr (mont_eq_one hR (by omega_arith) hY)
  rw [t23, kv.gpr .r23 (by decide), ku.gpr .r23 (by decide), h23, kv.gpr .r20 (by decide), u20, v19, um,
    kv.gpr .r28 (by decide), ku.gpr .r28 (by decide), h28, nz_mask hd, e1, e2, mask_or, upd_arith]
  by_cases e : d = 0 <;> simp [e, Bool.or_comm]

/-! ## A window -/

/-- The arrays a window writes. -/
def winRanges (w : Nat) : List (Nat × Nat) :=
  [(slot w 2, 8 * (w + 2)), (slot w 3, 8 * (w + 2)), (slot w 5, 8 * (w + 2)), (slot w 6, 8 * (w + 2))]

/-- The registers a window writes. -/
def winRegs : List Reg := tabRegs ++ [.r23, .r24, .r28]

/-- What the windows keep, from `s₀`, writing only the registers `rs`. -/
structure WSt (rs : List Reg) (s₀ t : State) (B : Addr) (Z w c b : Nat) : Prop where
  ctx : MCtx t B Z w
  consts : Consts t.mem B w c
  tab : TabOK t.mem B w c b
  outs : Outs B (winRanges w) s₀.mem t.mem
  keep : Keep rs s₀ t
  hm : ∀ r ∈ mctxRegs, r ∉ rs
  hw : ∀ r ∈ winRegs, r ∈ rs

theorem winRanges_mut {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (winRanges w) m m') : Mut B w m m' :=
  Outs.widen h fun r hr => ⟨r, by
    simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> simp [roundRanges], by omega_arith, by omega_arith⟩

theorem WSt.step {s₀ s t : State} {B : Addr} {Z w c b : Nat} {rs rs' : List Reg} (h : WSt rs s₀ s B Z w c b)
    (hout : Outs B (winRanges w) s.mem t.mem) (k : Keep rs' s t) (hrs : ∀ r ∈ rs', r ∈ rs)
    (h0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) : WSt rs s₀ t B Z w c b := by
  obtain hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega_arith
  refine ⟨h.ctx.keep k (fun r hr hr' => h.hm r hr (hrs r hr')) h0,
    h.consts.of_mut (winRanges_mut hout) hn, fun i hi => ?_,
    Outs.trans h.outs hout, (h.keep.trans k).mono fun r hr => ?_, h.hm, h.hw⟩
  · rw [Outs.arrEq hout (by omega_arith) (fun r hr => by
      simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact slot_sep (by omega_arith)) hn]
    exact h.tab i hi
  · rcases List.mem_append.mp hr with hr | hr
    · exact hr
    · exact hrs r hr

/-- A step that writes only registers a window writes. -/
theorem WSt.stepW {s₀ s t : State} {B : Addr} {Z w c b : Nat} {rs rs' : List Reg} (h : WSt rs s₀ s B Z w c b)
    (hout : Outs B (winRanges w) s.mem t.mem) (k : Keep rs' s t) (hrs : ∀ r ∈ rs', r ∈ winRegs := by decide)
    (h0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) : WSt rs s₀ t B Z w c b :=
  h.step hout k (fun r hr => h.hw r (hrs r hr)) h0

theorem montRanges_win {B : Addr} {w o : Nat} {m m' : Mem} (h : Outs B (montRanges w o) m m') (ho : o = 5 ∨ o = 6) :
    Outs B (winRanges w) m m' :=
  Outs.widen h fun r hr => ⟨r, by
    simp only [montRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp [winRanges], by omega_arith, by omega_arith⟩

theorem selectRanges_win {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (selectRanges w) m m') :
    Outs B (winRanges w) m m' :=
  Outs.widen h fun r hr => ⟨r, by
    simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [winRanges], by omega_arith, by omega_arith⟩

theorem square_step {rs : List Reg} {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool}
    (h : WSt rs s₀ s B Z w c b)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c)
    (h23 : s.gpr .r23 = mask P) :
    WP isa square s fun t => WSt rs s₀ t B Z w c b ∧
      arr t.mem B w aY = (wSq c true (Y, P)).1 * 2 ^ (64 * w) % c ∧ (wSq c true (Y, P)).1 < c ∧
      t.gpr .r23 = mask (wSq c true (Y, P)).2 ∧ t.gpr .r24 = s.gpr .r24 :=
  WP.mono (square_ok h.ctx h.consts hc3 hodd hy h23) fun t ⟨⟨ty, tlt, t23, tout, t0⟩, kt⟩ =>
    ⟨h.stepW (montRanges_win tout (by simp)) kt (by simp [sqRegs, Pub.montRegs, tailRegs, eqRegs, winRegs, tabRegs])
      t0, ty, tlt, t23, kt.gpr .r24 (by simp [sqRegs, Pub.montRegs, tailRegs, eqRegs])⟩

/-- A window: `RsaKeyGen.wWin` for the digit at the top of `r24`. -/
theorem window_ok {rs : List Reg} {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool} {V : BitVec 64}
    (h : WSt rs s₀ s B Z w c b) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c) (h23 : s.gpr .r23 = mask P) (h24 : s.gpr .r24 = V) :
    WP isa window s fun t => WSt rs s₀ t B Z w c b ∧
      arr t.mem B w aY = (wWin c b (V >>> 60).toNat (Y, P)).1 * 2 ^ (64 * w) % c ∧
      (wWin c b (V >>> 60).toNat (Y, P)).1 < c ∧
      t.gpr .r23 = mask (wWin c b (V >>> 60).toNat (Y, P)).2 ∧ t.gpr .r24 = V <<< 4 := by
  obtain hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  obtain hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega_arith
  unfold window
  refine WP.seq (WP.mono (square_step h hc3 hodd hy h23) fun t₁ ⟨f1, y1, _, p1, v1⟩ => ?_)
  refine WP.seq (WP.mono (square_step f1 hc3 hodd y1 p1) fun t₂ ⟨f2, y2, _, p2, v2⟩ => ?_)
  refine WP.seq (WP.mono (square_step f2 hc3 hodd y2 p2) fun t₃ ⟨f3, y3, _, p3, v3⟩ => ?_)
  refine WP.seq (WP.mono (square_step f3 hc3 hodd y3 p3) fun t₄ ⟨f4, y4, l4, p4, v4⟩ => ?_)
  obtain h4 : t₄.gpr .r24 = V := by rw [v4, v3, v2, v1, h24]
  obtain hdl : (V >>> 60).toNat < 16 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := V.isLt
    omega_arith
  obtain hdig : WP isa (.block [.lsr .d .r28 .r24 60]) t₄ fun u =>
      (u.gpr .r28 = BitVec.ofNat 64 (V >>> 60).toNat ∧ u.mem = t₄.mem) ∧ Keep [.r28] t₄ u := by
    refine WP.keep _ ?_ (by decide)
    prun [h4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono hdig fun u ⟨⟨u28, um⟩, ku⟩ => ?_)
  obtain fu := f4.stepW (by rw [um]; exact Outs.refl _ _ _) ku (by decide) (by rw [um])
  refine WP.seq (WP.mono (select_ok fu.ctx.toEnv u28 hdl) fun v ⟨⟨v5, vout⟩, kv⟩ => ?_)
  obtain fv := fu.stepW (selectRanges_win vout) kv (by decide) (Outs.w32_0 vout (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_lt (by decide)
      · exact slot_lt (by decide)) hn)
  -- `y := y T_d`
  obtain vy : arr v.mem B w aY = (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).1 * 2 ^ (64 * w) % c := by
    rw [Outs.arrEq vout (by decide) (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slot_sep (by decide)) hn, um, y4]
  obtain vd : arr v.mem B w 5 = b ^ (V >>> 60).toNat % c * 2 ^ (64 * w) % c := by
    rw [v5]; exact fu.tab _ hdl
  have vc := fv.consts.cand
  refine WP.seq (WP.mono (mont_ok fv.ctx (o := 6) (a := 6) (b := 5) (by simp) (by simp) (by simp)
    (by rw [vd, vc]; exact Nat.mod_lt _ (by omega_arith))) fun x ⟨⟨xlt, xeq, xout, x0⟩, kx⟩ => ?_)
  obtain fx := fv.stepW (montRanges_win xout (by simp)) kx (by simp [Pub.montRegs, tailRegs, winRegs, tabRegs]) x0
  rw [vc] at xlt xeq
  obtain xy : arr x.mem B w aY = (wWin c b (V >>> 60).toNat (Y, P)).1 * 2 ^ (64 * w) % c := by
    simp only [wWin, VG.Proof.Bignum.powMod_eq]
    exact mont_val hR xlt xeq vy vd
  obtain xl : (wWin c b (V >>> 60).toNat (Y, P)).1 < c := by
    simp only [wWin]; exact Nat.mod_lt _ (by omega_arith)
  obtain x23 : x.gpr .r23 = mask (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).2 := by
    rw [kx.gpr .r23 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r23 (by decide), ku.gpr .r23 (by decide), p4]
  obtain x28 : x.gpr .r28 = BitVec.ofNat 64 (V >>> 60).toNat := by
    rw [kx.gpr .r28 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r28 (by decide), u28]
  refine WP.seq (WP.mono (update_ok fx.ctx.toEnv fx.consts hc3 hodd xy xl x23 x28 hdl)
    fun y ⟨⟨y23, ym⟩, ky⟩ => ?_)
  obtain fy := fx.stepW (by rw [ym]; exact Outs.refl _ _ _) ky (by decide) (by rw [ym])
  obtain y24 : y.gpr .r24 = V := by
    rw [ky.gpr .r24 (by decide), kx.gpr .r24 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r24 (by decide),
      ku.gpr .r24 (by decide), h4]
  obtain hsh : WP isa (.block [.lsl .r24 .r24 4]) y fun z =>
      (z.gpr .r24 = V <<< 4 ∧ z.mem = y.mem) ∧ Keep [.r24] y z := by
    refine WP.keep _ ?_ (by decide)
    prun [y24]
  refine WP.mono hsh fun z ⟨⟨z24, zm⟩, kz⟩ => ⟨fy.stepW (by rw [zm]; exact Outs.refl _ _ _) kz (by decide)
    (by rw [zm]), by rw [zm, ym, xy], xl, ?_, z24⟩
  rw [kz.gpr .r23 (by decide), y23]
  rfl

end VG.Proof.MillerRabin.PPC64LE

end

end

/-!
# The Miller–Rabin round on PPC64LE: the windows of the exponent

`windows_ok`: the windows of `E` (array 27), its words from the top, 16
windows each: `RsaKeyGen.wRun` over all `16 w` windows, from `y = 1` and a
clear flag.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wRun wWin win_digit shl4_succ)

/-- A 64-bit word of a number of 32-bit digits. -/
theorem word_digit (m : Mem) (B : Addr) (d n i : Nat) (hi : i < n) :
    (word m B (d + 8 * i)).toNat = val32 m B d (2 * n) / 2 ^ (64 * i) % 2 ^ 64 := by
  have e : val32 m B d (2 * n) = val32 m B d (2 * i) + 2 ^ (32 * (2 * i)) *
      (val32 m B (d + 4 * (2 * i)) 2 + 2 ^ (32 * 2) * val32 m B (d + 4 * (2 * i) + 4 * 2) (2 * (n - i - 1))) := by
    rw [← val32_append, ← val32_append, show 2 * i + (2 + 2 * (n - i - 1)) = 2 * n by omega_arith]
  have hL : val32 m B d (2 * i) < 2 ^ (64 * i) := by
    have := val32_lt m B d (2 * i)
    rwa [show 32 * (2 * i) = 64 * i by omega_arith] at this
  rw [word_eq_w32, e, show 32 * (2 * i) = 64 * i by omega_arith, show 4 * (2 * i) = 8 * i by omega_arith,
    Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hL, Nat.zero_add,
    show (2 : Nat) ^ (32 * 2) = 2 ^ 64 by decide, Nat.add_mul_mod_self_left]
  simp only [val32, Nat.mul_zero, Nat.add_zero]
  have h1 := (m.readW (off B (d + 8 * i)) 32).isLt
  have h2 := (m.readW (off B (d + 8 * i + 4)) 32).isLt
  exact (Nat.mod_eq_of_lt (by simp only [w32]; omega_arith)).symm

/-- A window state anchored at `u`, from one anchored earlier. -/
theorem WSt.fresh {rs : List Reg} {s₀ u : State} {B : Addr} {Z w c b : Nat} (h : WSt rs s₀ u B Z w c b) :
    WSt winRegs u u B Z w c b :=
  ⟨h.ctx, h.consts, h.tab, Outs.refl _ _ _, Keep.refl _ _, by decide, fun _ h => h⟩

theorem WSt.join {rs : List Reg} {s₀ u t : State} {B : Addr} {Z w c b : Nat} (h : WSt rs s₀ u B Z w c b)
    (h' : WSt winRegs u t B Z w c b) : WSt rs s₀ t B Z w c b := by
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega_arith
  exact h.stepW h'.outs h'.keep (fun _ h => h) (Outs.w32_0 h'.outs (fun r hr => by
    simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact slot_lt (by decide)) hn)

/-- The registers the windows write. -/
def expRegs : List Reg := winRegs ++ [.r25, .r26, .r27]

/-- The state of the windows after the top `j` of the `16 w` windows. -/
structure ExpAt (s₀ t : State) (B : Addr) (Z w c b j : Nat) : Prop where
  ws : WSt expRegs s₀ t B Z w c b
  y : arr t.mem B w aY = (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).1 * 2 ^ (64 * w) % c
  lt : (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).1 < c
  p : t.gpr .r23 = mask (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) j).2

theorem off_sub8 (B : Addr) (y : Nat) : off B (y + 8) - BitVec.ofNat 64 8 = off B y := by
  rw [← off_add, BitVec.add_sub_cancel]

/-- The inner loop: the 16 windows of the word `V`, from window `16 k`. -/
theorem inner_ok {s₀ u : State} {B : Addr} {Z w c b k : Nat} {V : BitVec 64} (hk : k < w)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hV : V.toNat = VG.Proof.RsaKeyGen.mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64)
    (h : ExpAt s₀ u B Z w c b (16 * k)) (h24 : u.gpr .r24 = V) (h27 : u.gpr .r27 = BitVec.ofNat 64 16) :
    WP isa (.loop (.seq window (.block [.subi .r27 .r27 1])) (.nonzero .d .r27)) u fun t =>
      ExpAt s₀ t B Z w c b (16 * (k + 1)) ∧ t.gpr .r25 = u.gpr .r25 ∧ t.gpr .r26 = u.gpr .r26 := by
  let I : Nat → State → Prop := fun i t => ExpAt s₀ t B Z w c b (16 * k + i) ∧ t.gpr .r24 = V <<< (4 * i) ∧
    t.gpr .r25 = u.gpr .r25 ∧ t.gpr .r26 = u.gpr .r26
  refine WP.mono (wp_countdown (body := .seq window (.block [.subi .r27 .r27 1])) (cnt := .r27) (N := 16)
    (by decide) (by decide) I (fun i hi t ⟨ht, t24, t25, t26⟩ _ => ?_) ⟨by simpa using h, by simp [h24], rfl, rfl⟩ h27)
    fun t ⟨ht, _, t25, t26⟩ => ⟨by rw [show 16 * (k + 1) = 16 * k + 16 by omega_arith]; exact ht, t25, t26⟩
  refine WP.seq (WP.mono (window_ok ht.ws.fresh hc3 hodd ht.y ht.p t24) fun x ⟨hx, xy, xl, x23, x24⟩ => ?_)
  have hd : ((V <<< (4 * i)) >>> 60).toNat =
      VG.Proof.RsaKeyGen.mrE c / 16 ^ (16 * w - 1 - (16 * k + i)) % 16 := by
    rw [win_digit (k := w - k) (by rw [hV, show w - k - 1 = w - 1 - k by omega_arith]) hi]
    rw [show 16 * (w - k - 1) + (15 - i) = 16 * w - 1 - (16 * k + i) by omega_arith]
  have hrun : wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i + 1) =
      wWin c b ((V <<< (4 * i)) >>> 60).toNat
        ((wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i)).1,
          (wRun c b (VG.Proof.RsaKeyGen.mrE c) (16 * w) (16 * k + i)).2) := by
    rw [hd, wRun]
  have hsub : WP isa (.block [.subi .r27 .r27 1]) x fun z =>
      (z.gpr .r27 = x.gpr .r27 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.r27] x z := by
    refine WP.keep _ ?_ (by decide)
    prun
  have hj := ht.ws.join hx
  refine WP.mono hsub fun z ⟨⟨z27, zm⟩, kz⟩ => ⟨⟨⟨hj.step (by rw [zm]; exact Outs.refl _ _ _) kz (by decide) (by rw [zm]),
    ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [zm, xy, ← hrun]; rfl
  · rw [← hrun] at xl; exact xl
  · rw [kz.gpr .r23 (by decide), x23, ← hrun]; rfl
  · rw [kz.gpr .r24 (by decide), x24, shl4_succ]
  · rw [kz.gpr .r25 (by decide), hx.keep.gpr .r25 (by decide), t25]
  · rw [kz.gpr .r26 (by decide), hx.keep.gpr .r26 (by decide), t26]
  · rw [z27, hx.keep.gpr .r27 (by decide)]

theorem shl3_ofNat (w : Nat) : BitVec.ofNat 64 w <<< 3 = BitVec.ofNat 64 (8 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega_arith

theorem shr1_ofNat (w : Nat) (hw : w ≤ 128) : BitVec.ofNat 64 (2 * w) >>> 1 = BitVec.ofNat 64 w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega_arith

/-- The windows of `E`: `RsaKeyGen.wRun` over all `16 w` windows, from
`y = R mod c` (`1`) and a clear flag. -/
theorem windows_ok {s : State} {B : Addr} {Z w c b : Nat} (h : WSt expRegs s s B Z w c b) (hc3 : 3 ≤ c)
    (hodd : c % 2 = 1) (hy : arr s.mem B w aY = 2 ^ (64 * w) % c) :
    WP isa windows s fun t => ExpAt s t B Z w c b (16 * w) := by
  have hw := h.ctx.hw
  have hw' := h.ctx.hw'
  have hZ := h.ctx.hZ
  have hnw := h.ctx.hs.nowrap
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  unfold windows
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.li .r23 0, .lsr .d .r26 .r11 1]) s fun t =>
      (t.gpr .r23 = mask false ∧ t.gpr .r26 = BitVec.ofNat 64 w ∧ t.mem = s.mem) ∧ Keep [.r23, .r26] s t := by
    refine WP.keep _ ?_ (by decide)
    prun [h.ctx.h11, shr1_ofNat w hw']
    rfl
  refine WP.mono h1 fun t₁ ⟨⟨a23, a26, m1⟩, k1⟩ => ?_
  have f1 := h.step (by rw [m1]; exact Outs.refl _ _ _) k1 (by decide) (by rw [m1])
  rw [WP.block_append_iff]
  refine WP.mono (f1.ctx.base (rd := .r25) (by decide) (by decide) aE) fun t₂ ⟨⟨a25, m2⟩, k2⟩ => ?_
  have f2 := f1.step (by rw [m2]; exact Outs.refl _ _ _) k2 (by decide) (by rw [m2])
  have h3 : WP isa (.block [.lsl .r0 .r26 3, .add .r25 .r25 .r0]) t₂ fun t =>
      (t.gpr .r25 = off B (slot w aE + 8 * w) ∧ t.mem = t₂.mem) ∧ Keep [.r0, .r25] t₂ t := by
    refine WP.keep _ ?_ (by decide)
    prun [k2.gpr .r26 (by decide), a26, a25, shl3_ofNat w, off_add]
  refine WP.mono h3 fun t₃ ⟨⟨b25, m3⟩, k3⟩ => ?_
  have f3 := f2.step (by rw [m3]; exact Outs.refl _ _ _) k3 (by decide) (by rw [m3])
  have e0 : ExpAt s t₃ B Z w c b (16 * 0) :=
    ⟨f3, by rw [m3, m2, m1, hy]; simp [wRun], by simp [wRun]; omega_arith,
      by rw [k3.gpr .r23 (by decide), k2.gpr .r23 (by decide), a23]; rfl⟩
  have c26 : t₃.gpr .r26 = BitVec.ofNat 64 w := by rw [k3.gpr .r26 (by decide), k2.gpr .r26 (by decide), a26]
  let I : Nat → State → Prop := fun k t => ExpAt s t B Z w c b (16 * k) ∧
    t.gpr .r25 = off B (slot w aE + 8 * (w - k))
  refine WP.mono (wp_countdown (cnt := .r26) (N := w) (by omega_arith) (by omega_arith) I
    (fun k hk t ⟨ht, t25⟩ _ => ?_) ⟨e0, by rw [b25, Nat.sub_zero]⟩ c26) fun t ⟨ht, _⟩ => ht
  -- the next word
  have hy8 : slot w aE + 8 * (w - k) = (slot w aE + 8 * (w - 1 - k)) + 8 := by omega_arith
  have hld : WP isa (.block [.subi .r25 .r25 8, .load .d .r24 .r25 0, .li .r27 16]) t fun u =>
      (u.gpr .r25 = off B (slot w aE + 8 * (w - 1 - k)) ∧
        u.gpr .r24 = word t.mem B (slot w aE + 8 * (w - 1 - k)) ∧ u.gpr .r27 = BitVec.ofNat 64 16 ∧
        u.mem = t.mem) ∧ Keep [.r24, .r25, .r27] t u := by
    refine WP.keep _ ?_ (by decide)
    prun [t25, hy8, off_sub8, (ht.ws.ctx.hs).ld (show slot w aE + 8 * (w - 1 - k) + 8 ≤ Z by omega_arith)]
  refine WP.seq (WP.mono hld fun u ⟨⟨u25, u24, u27, um⟩, ku⟩ => ?_)
  have eu : ExpAt s u B Z w c b (16 * k) :=
    ⟨ht.ws.step (by rw [um]; exact Outs.refl _ _ _) ku (by decide) (by rw [um]), by rw [um]; exact ht.y, ht.lt,
      by rw [ku.gpr .r23 (by decide)]; exact ht.p⟩
  have hV : (word t.mem B (slot w aE + 8 * (w - 1 - k))).toNat =
      VG.Proof.RsaKeyGen.mrE c / 2 ^ (64 * (w - 1 - k)) % 2 ^ 64 := by
    rw [word_digit _ _ _ _ _ (show w - 1 - k < w by omega_arith)]
    rw [show val32 t.mem B (slot w aE) (2 * w) = arr t.mem B w aE from rfl, ht.ws.consts.e]
  refine WP.seq (WP.mono (inner_ok hk hc3 hodd hV eu u24 u27) fun x ⟨ex, x25, x26⟩ => ?_)
  have hsub : WP isa (.block [.subi .r26 .r26 1]) x fun z =>
      (z.gpr .r26 = x.gpr .r26 - BitVec.ofNat 64 1 ∧ z.mem = x.mem) ∧ Keep [.r26] x z := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hsub fun z ⟨⟨z26, zm⟩, kz⟩ => ⟨⟨⟨ex.ws.step (by rw [zm]; exact Outs.refl _ _ _) kz (by decide)
    (by rw [zm]), by rw [zm]; exact ex.y, ex.lt, by rw [kz.gpr .r23 (by decide)]; exact ex.p⟩, ?_⟩, ?_⟩
  · rw [kz.gpr .r25 (by decide), x25, u25, show w - 1 - k = w - (k + 1) by omega_arith]
  · rw [z26, x26, ku.gpr .r26 (by decide)]

end VG.Proof.MillerRabin.PPC64LE

end

end

/-!
# The Miller–Rabin round on PPC64LE: the last squarings

`last_ok j`: `y := y²` and the flag or'ed with `y = −1` under the mask of
`σ > j`, from the lowest set bit `l` of `c − 1`'s lowest nonzero word, after
`E` (`RsaKeyGen.sig_mask1`–`3`): `wSq c (σ > j)`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (wSq mrSig mrA sigOf)

/-- `K` of `σ > j`, as `repeat16` builds it. -/
def sigK64 (j : Nat) : BitVec 64 :=
  if j = 1 then 0xDDDDDDDDDDDDDDDD#64 else if j = 2 then 0x9999999999999999#64 else 0x1111111111111111#64

theorem repeat16_val (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    ((((sigK j ++ (0 : BitVec 16)).signExtend 64 ||| (sigK j).setWidth 64) <<< 32 |||
      (sigK j).setWidth 64 <<< 16) ||| (sigK j).setWidth 64) = sigK64 j := by
  rcases hj with rfl | rfl | rfl <;> decide

theorem sig_mask (j : Nat) (hj : j = 1 ∨ j = 2 ∨ j = 3) {k : Nat} (hk : k < 64) :
    (BitVec.twoPow 64 k &&& sigK64 j = 0) = ¬ (j < sigOf k) := by
  rcases hj with rfl | rfl | rfl
  · exact VG.Proof.RsaKeyGen.sig_mask1 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask2 k hk
  · exact VG.Proof.RsaKeyGen.sig_mask3 k hk

/-- The mask of a word being nonzero. -/
theorem nz64_mask (x : BitVec 64) :
    BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - (x >>> 1 ||| x &&& BitVec.ofNat 64 1)) >>> 63 =
      mask (decide (x ≠ 0)) := by
  have ht : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat < 2 ^ 63 := by
    rw [BitVec.toNat_or]
    apply Nat.or_lt_two_pow
    · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := x.isLt; omega_arith
    · rw [BitVec.toNat_and]; exact Nat.lt_of_le_of_lt (Nat.and_le_right) (by decide)
  have hz : (x >>> 1 ||| x &&& BitVec.ofNat 64 1) = 0 ↔ x = 0 := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff]
    constructor
    · rintro ⟨h1, h2⟩
      apply BitVec.eq_of_toNat_eq
      have a := congrArg BitVec.toNat h1
      have b := congrArg BitVec.toNat h2
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_and, BitVec.toNat_ofNat,
        Nat.reducePow, Nat.reduceMod, Nat.and_one_is_mod] at a b
      simp only [BitVec.toNat_ofNat]
      omega_arith
    · rintro rfl; decide
  by_cases e : x = 0
  · subst e; decide
  · have hne : (x >>> 1 ||| x &&& BitVec.ofNat 64 1).toNat ≠ 0 :=
      fun h => e (hz.mp (BitVec.eq_of_toNat_eq h))
    have hs : (BitVec.ofNat 64 0 - (x >>> 1 ||| x &&& BitVec.ofNat 64 1)) >>> 63 = BitVec.ofNat 64 1 := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega_arith
    rw [hs, show decide (x ≠ 0) = true from decide_eq_true e]
    rfl

theorem mask_and (p q : Bool) : mask p &&& mask q = mask (p && q) := by cases p <;> cases q <;> rfl

/-- The mask of `σ > j` from the word after `E`. -/
theorem sig_word {c j : Nat} (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0) = decide (j < mrSig c) := by
  have h := sig_mask j hj (k := mrA c % 64) (Nat.mod_lt _ (by decide))
  rw [VG.Proof.RsaKeyGen.sigOf_mod] at h
  apply decide_eq_decide.mpr
  rw [show mrSig c = sigOf (mrA c) from rfl, ne_eq, h, Decidable.not_not]

/-- A squaring after the windows: `wSq c (σ > j)`. -/
theorem last_ok {rs : List Reg} {s₀ s : State} {B : Addr} {Z w c b Y : Nat} {P : Bool}
    (h : WSt rs s₀ s B Z w c b) (hc3 : 3 ≤ c) (hodd : c % 2 = 1)
    (hy : arr s.mem B w aY = Y * 2 ^ (64 * w) % c) (h23 : s.gpr .r23 = mask P) {j : Nat}
    (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    WP isa (last j) s fun t => WSt rs s₀ t B Z w c b ∧
      arr t.mem B w aY = (wSq c (decide (j < mrSig c)) (Y, P)).1 * 2 ^ (64 * w) % c ∧
      (wSq c (decide (j < mrSig c)) (Y, P)).1 < c ∧ t.gpr .r23 = mask (wSq c (decide (j < mrSig c)) (Y, P)).2 := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega_arith
  have hcc := h.consts.cand
  have hw' := h.ctx.hw'
  have hZ := h.ctx.hZ
  have hE := slot_lt (w := w) (show aE < 28 by decide)
  unfold last
  refine WP.seq (WP.mono (mont_ok h.ctx (o := 6) (a := 6) (b := 6) (by simp) (by simp) (by simp)
    (by rw [show (6 : Nat) = aY from rfl, hy, hcc]; exact Nat.mod_lt _ (by omega_arith)))
    fun u ⟨⟨hlt, heq, hout, h0⟩, ku⟩ => ?_)
  have fu := h.stepW (montRanges_win hout (by simp)) ku (by simp [Pub.montRegs, tailRegs, winRegs, tabRegs]) h0
  rw [hcc] at hlt heq
  have uy : arr u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := VG.Proof.RsaKeyGen.mont_val hR hlt heq hy hy
  refine WP.seq (WP.mono (eqMask_ok fu.ctx.toEnv .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v20, vm⟩, kv⟩ => ?_)
  have fv := fu.stepW (by rw [vm]; exact Outs.refl _ _ _) kv (by decide) (by rw [vm])
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (fv.ctx.base (rd := .r3) (by decide) (by decide) aE) fun x ⟨⟨x3, xm⟩, kx⟩ => ?_
  have fx := fv.stepW (by rw [xm]; exact Outs.refl _ _ _) kx (by decide) (by rw [xm])
  have hl : x.mem.readW (off B (slot w aE + 8 * w)) 64 = BitVec.twoPow 64 (mrA c % 64) := fx.consts.l
  have hblk : WP isa (.block ([.lsr .d .r0 .r11 1, .lsl .r0 .r0 3, .add .r3 .r3 .r0, .load .d .r3 .r3 0] ++
      (repeat16 (sigK j) ++ [.logic .and .r3 .r3 .r4, .lsr .d .r4 .r3 1, .li .r0 1, .logic .and .r0 .r3 .r0,
        .logic .or .r3 .r4 .r0, .li .r0 0, .sub .r3 .r0 .r3, .lsr .d .r3 .r3 63, .sub .r3 .r0 .r3,
        .logic .and .r20 .r20 .r3, .logic .or .r23 .r23 .r20]))) x fun t =>
      (t.gpr .r23 = x.gpr .r23 ||| (x.gpr .r20 &&& mask (decide (BitVec.twoPow 64 (mrA c % 64) &&& sigK64 j ≠ 0))) ∧
        t.mem = x.mem) ∧ Keep [.r0, .r3, .r4, .r20, .r23] x t := by
    refine WP.keep _ ?_ (by rfl)
    unfold repeat16
    prun [fx.ctx.h11, shr1_ofNat w hw', shl3_ofNat w, x3, fx.ctx.hs.ld (show slot w aE + 8 * w + 8 ≤ Z by omega_arith),
      hl, exec_lis, exec_ori, exec_oris, repeat16_val j hj, nz64_mask]
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨fx.stepW (by rw [tm]; exact Outs.refl _ _ _) kt (by decide)
    (by rw [tm]), ?_, Nat.mod_lt _ (by omega_arith), ?_⟩
  · rw [tm, xm, vm, uy]; rfl
  · have e : decide (arr u.mem B w aY = arr u.mem B w aMinus) = decide (Y * Y % c = c - 1) := by
      have u10 : arr u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
        rw [Outs.arrEq_mont hout (by decide) (by decide) (by decide) (by decide) hn]; exact h.consts.minus
      rw [uy, u10]
      exact decide_eq_decide.mpr (VG.Proof.RsaKeyGen.mont_eq_m1 hR (by omega_arith) (Nat.mod_lt _ (by omega_arith)))
    rw [t23, kx.gpr .r23 (by decide), kv.gpr .r23 (by decide), ku.gpr .r23 (by simp [Pub.montRegs, tailRegs]),
      h23, kx.gpr .r20 (by decide), v20, e, sig_word hj, mask_and, mask_or]
    simp only [wSq, Bool.and_comm]

end VG.Proof.MillerRabin.PPC64LE
