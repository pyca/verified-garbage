module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq
public import VerifiedGarbage.Proof.Bignum.PPC64LE.MontCore
public import VerifiedGarbage.Proof.Bignum.PPC64LE.PubMont

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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.hs.nowrap; have := h.hZ; omega
  have hcc := hc.cand
  unfold square
  refine WP.seq (WP.mono (mont_ok h (o := 6) (a := 6) (b := 6) (by simp) (by simp) (by simp)
    (by rw [show (6 : Nat) = aY from rfl, hy, hcc]; exact Nat.mod_lt _ (by omega)))
    fun u ⟨⟨hlt, heq, hout, h0⟩, ku⟩ => ?_)
  have hu := h.keep ku (by decide) h0
  rw [hcc] at hlt heq
  have uy : arr u.mem B w aY = Y * Y % c * 2 ^ (64 * w) % c := mont_val hR hlt heq hy hy
  have u10 : arr u.mem B w aMinus = c - 2 ^ (64 * w) % c := by
    rw [Outs.arrEq_mont hout (by decide) (by decide) (by decide) (by decide) hn, hc.minus]
  refine WP.seq (WP.mono (eqMask_ok hu.toEnv .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun v ⟨⟨v20, vm⟩, kv⟩ => ?_)
  have hblk : WP isa (.block [.logic .or .r23 .r23 .r20]) v fun t =>
      (t.gpr .r23 = v.gpr .r23 ||| v.gpr .r20 ∧ t.mem = v.mem) ∧ Keep [.r23] v t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨⟨?_, Nat.mod_lt _ (by omega), ?_, ?_, ?_⟩, ?_⟩
  · rw [tm, vm, uy]; rfl
  · have e : (decide (arr u.mem B w aY = arr u.mem B w aMinus)) = decide (Y * Y % c = c - 1) := by
      rw [uy, u10]
      exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega) (Nat.mod_lt _ (by omega)))
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
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    exact Nat.xor_lt_two_pow (by omega) (by omega)
  have he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
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
  have ho : o < 28 := by omega
  have ht : t < 28 := by omega
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isDigit_ok h30 h28 hj hd) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) e1 (by rw [k1.gpr .r30 (by decide), h30])) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e2.base (rd := .r9) (by decide) (by decide) t) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  refine WP.mono (e3.base (rd := .r5) (by decide) (by decide) o) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have e4 := e3.keep k4 (by decide)
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok e4 (b := decide (j = d)) (o := o) (a := 11 + j) (t := t) ho (by omega) ht
      (by omega) (by omega) a5
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
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.hs.nowrap; have := h.hZ; omega
  have keepT : ∀ {m : Mem}, Outs B (selectRanges w) s.mem m → ∀ i < 16, arr m B w (11 + i) = arr s.mem B w (11 + i) :=
    fun hm i hi => Outs.arrEq hm (by omega) (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slot_sep (by omega)) hn
  have fr3 : ∀ {m m' : Mem}, Outside B (slot w 3) (8 * (w + 2)) m m' → Outs B (selectRanges w) m m' :=
    fun h => Outs.of_outside h (by simp [selectRanges])
  have fr5 : ∀ {m m' : Mem}, Outside B (slot w 5) (8 * (w + 2)) m m' → Outs B (selectRanges w) m m' :=
    fun h => Outs.of_outside h (by simp [selectRanges])
  unfold select
  have hpre : WP isa (.block [.li .r30 0]) s fun t => (t.gpr .r30 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ∧
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
      (by rw [m0]; exact Outs.refl _ _ _), k0.mono (by decide)⟩) fun t ⟨_, _, _, t5, tout, kt⟩ => ⟨⟨by rw [t5, ite_eq_left_of_eq_true _ _ (eq_true (by omega))],
        tout⟩, kt⟩
  -- the first entry of the pair
  refine wp_seq_assoc (WP.mono (pick_ok et t30 t28 (by omega) hd (o := 3) (t := 5) (by simp))
    fun u ⟨⟨u3, uo⟩, ku⟩ => ?_)
  have eu := et.keep ku (by decide)
  -- the second
  rw [show ([.addi .r30 .r30 1] ++ isDigit ++ entry ++ PublicChecked.base .r9 aT ++ PublicChecked.base .r5 aW) =
      [.addi .r30 .r30 1] ++ (isDigit ++ entry ++ PublicChecked.base .r9 aT ++ PublicChecked.base .r5 aW) by
    simp only [List.append_assoc]]
  refine wp_seq_assoc (wp_block_prefix_seq ?_)
  have hinc : WP isa (.block [.addi .r30 .r30 1]) u fun v =>
      (v.gpr .r30 = BitVec.ofNat 64 (2 * k + 1) ∧ v.mem = u.mem) ∧ Keep [.r30] u v := by
    refine WP.keep _ ?_ (by decide)
    prun [(ku.gpr .r30 (by decide)).trans t30, ← BitVec.ofNat_add]
  refine WP.mono hinc fun v ⟨⟨v30, vm⟩, kv⟩ => ?_
  have ev := eu.keep kv (by decide)
  refine (WP.mono (pick_ok ev v30 (by rw [kv.gpr .r28 (by decide), ku.gpr .r28 (by decide), t28])
    (by omega) hd (o := 5) (t := 3) (by simp)) fun x ⟨⟨x5, xo⟩, kx⟩ => ?_)
  have ex := ev.keep kx (by decide)
  have hend : WP isa (.block [.addi .r30 .r30 1, .subi .r4 .r30 16]) x fun y =>
      (y.gpr .r30 = BitVec.ofNat 64 (2 * (k + 1)) ∧
        y.gpr .r4 = BitVec.ofNat 64 (2 * (k + 1)) - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧ Keep [.r30, .r4] x y := by
    refine WP.keep _ ?_ (by decide)
    prun [(kx.gpr .r30 (by decide)).trans v30, ← BitVec.ofNat_add,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  refine WP.mono hend fun y ⟨⟨y30, y4, ym⟩, ky⟩ => ⟨⟨ex.keep ky (by decide), by
    rw [ky.gpr .r28 (by decide), kx.gpr .r28 (by decide), kv.gpr .r28 (by decide), ku.gpr .r28 (by decide), t28],
    y30, ?_, ?_, ?_⟩, ?_⟩
  · -- array 5
    have o5 : Outs B (selectRanges w) s.mem x.mem :=
      Outs.trans (Outs.trans tout (fr3 uo)) (by rw [← vm]; exact fr5 xo)
    rw [ym, x5, vm, u3, t5, keepT (Outs.trans tout (fr3 uo)) _ (by omega), keepT tout _ (by omega)]
    split_ifs <;> (try subst_vars) <;> first | rfl | (exfalso; omega)
  · rw [ym]
    exact Outs.trans (Outs.trans tout (fr3 uo)) (by rw [← vm]; exact fr5 xo)
  · exact (kt.trans ((((ku.trans kv).trans kx).trans ky))).mono (by simp [selectRegs, pickRegs])
  · rw [y4, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega

/-! ## The flag after a window -/

theorem upd_arith (p P z : Bool) :
    mask P ^^^ ((mask p ^^^ mask P) &&& mask z) = mask (if z then p else P) := by
  cases p <;> cases P <;> cases z <;> decide

theorem nz_mask {d : Nat} (hd : d < 16) :
    BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - BitVec.ofNat 64 d) >>> 63 = mask (decide (d ≠ 0)) := by
  have : (BitVec.ofNat 64 0 - BitVec.ofNat 64 d) >>> 63 = BitVec.ofNat 64 (if d ≠ 0 then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    split <;> omega
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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  unfold update
  refine WP.seq (WP.mono (eqMask_ok h .r20 (a := aY) (b := aMinus) (by decide) (by decide))
    fun u ⟨⟨u20, um⟩, ku⟩ => ?_)
  have eu := h.keep ku (by decide)
  refine WP.seq (WP.mono (eqMask_ok eu .r19 (a := aY) (b := aOne) (by decide) (by decide))
    fun v ⟨⟨v19, vm⟩, kv⟩ => ?_)
  have hblk : WP isa (.block [.logic .or .r20 .r20 .r19, .li .r0 0, .sub .r3 .r0 .r28, .lsr .d .r3 .r3 63,
      .sub .r3 .r0 .r3, .logic .xor .r20 .r20 .r23, .logic .and .r20 .r20 .r3, .logic .xor .r23 .r23 .r20]) v
      fun t => (t.gpr .r23 = v.gpr .r23 ^^^ (((v.gpr .r20 ||| v.gpr .r19) ^^^ v.gpr .r23) &&&
        (BitVec.ofNat 64 0 - (BitVec.ofNat 64 0 - v.gpr .r28) >>> 63)) ∧ t.mem = v.mem) ∧
        Keep [.r0, .r3, .r20, .r23] v t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.mono hblk fun t ⟨⟨t23, tm⟩, kt⟩ => ⟨⟨?_, by rw [tm, vm, um]⟩, ((ku.trans kv).trans kt).mono
    (by simp [updRegs, eqRegs])⟩
  have e1 : decide (arr s.mem B w aY = arr s.mem B w aMinus) = decide (Y = c - 1) := by
    rw [hy, hc.minus]
    exact decide_eq_decide.mpr (mont_eq_m1 hR (by omega) hY)
  have e2 : decide (arr s.mem B w aY = arr s.mem B w aOne) = decide (Y = 1) := by
    rw [hy, hc.one]
    exact decide_eq_decide.mpr (mont_eq_one hR (by omega) hY)
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
    rcases hr with rfl | rfl | rfl | rfl <;> simp [roundRanges], by omega, by omega⟩

theorem WSt.step {s₀ s t : State} {B : Addr} {Z w c b : Nat} {rs rs' : List Reg} (h : WSt rs s₀ s B Z w c b)
    (hout : Outs B (winRanges w) s.mem t.mem) (k : Keep rs' s t) (hrs : ∀ r ∈ rs', r ∈ rs)
    (h0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) : WSt rs s₀ t B Z w c b := by
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega
  refine ⟨h.ctx.keep k (fun r hr hr' => h.hm r hr (hrs r hr')) h0,
    h.consts.of_mut (winRanges_mut hout) hn, fun i hi => ?_,
    Outs.trans h.outs hout, (h.keep.trans k).mono fun r hr => ?_, h.hm, h.hw⟩
  · rw [Outs.arrEq hout (by omega) (fun r hr => by
      simp only [winRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact slot_sep (by omega)) hn]
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
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp [winRanges], by omega, by omega⟩

theorem selectRanges_win {B : Addr} {w : Nat} {m m' : Mem} (h : Outs B (selectRanges w) m m') :
    Outs B (winRanges w) m m' :=
  Outs.widen h fun r hr => ⟨r, by
    simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp [winRanges], by omega, by omega⟩

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
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega
  unfold window
  refine WP.seq (WP.mono (square_step h hc3 hodd hy h23) fun t₁ ⟨f1, y1, _, p1, v1⟩ => ?_)
  refine WP.seq (WP.mono (square_step f1 hc3 hodd y1 p1) fun t₂ ⟨f2, y2, _, p2, v2⟩ => ?_)
  refine WP.seq (WP.mono (square_step f2 hc3 hodd y2 p2) fun t₃ ⟨f3, y3, _, p3, v3⟩ => ?_)
  refine WP.seq (WP.mono (square_step f3 hc3 hodd y3 p3) fun t₄ ⟨f4, y4, l4, p4, v4⟩ => ?_)
  have h4 : t₄.gpr .r24 = V := by rw [v4, v3, v2, v1, h24]
  have hdl : (V >>> 60).toNat < 16 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have := V.isLt
    omega
  have hdig : WP isa (.block [.lsr .d .r28 .r24 60]) t₄ fun u =>
      (u.gpr .r28 = BitVec.ofNat 64 (V >>> 60).toNat ∧ u.mem = t₄.mem) ∧ Keep [.r28] t₄ u := by
    refine WP.keep _ ?_ (by decide)
    prun [h4, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.seq (WP.mono hdig fun u ⟨⟨u28, um⟩, ku⟩ => ?_)
  have fu := f4.stepW (by rw [um]; exact Outs.refl _ _ _) ku (by decide) (by rw [um])
  refine WP.seq (WP.mono (select_ok fu.ctx.toEnv u28 hdl) fun v ⟨⟨v5, vout⟩, kv⟩ => ?_)
  have fv := fu.stepW (selectRanges_win vout) kv (by decide) (Outs.w32_0 vout (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact slot_lt (by decide)
      · exact slot_lt (by decide)) hn)
  -- `y := y T_d`
  have vy : arr v.mem B w aY = (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).1 * 2 ^ (64 * w) % c := by
    rw [Outs.arrEq vout (by decide) (fun r hr => by
      simp only [selectRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact slot_sep (by decide)) hn, um, y4]
  have vd : arr v.mem B w 5 = b ^ (V >>> 60).toNat % c * 2 ^ (64 * w) % c := by
    rw [v5]; exact fu.tab _ hdl
  have vc := fv.consts.cand
  refine WP.seq (WP.mono (mont_ok fv.ctx (o := 6) (a := 6) (b := 5) (by simp) (by simp) (by simp)
    (by rw [vd, vc]; exact Nat.mod_lt _ (by omega))) fun x ⟨⟨xlt, xeq, xout, x0⟩, kx⟩ => ?_)
  have fx := fv.stepW (montRanges_win xout (by simp)) kx (by simp [Pub.montRegs, tailRegs, winRegs, tabRegs]) x0
  rw [vc] at xlt xeq
  have xy : arr x.mem B w aY = (wWin c b (V >>> 60).toNat (Y, P)).1 * 2 ^ (64 * w) % c := by
    simp only [wWin, VG.Proof.Bignum.powMod_eq]
    exact mont_val hR xlt xeq vy vd
  have xl : (wWin c b (V >>> 60).toNat (Y, P)).1 < c := by
    simp only [wWin]; exact Nat.mod_lt _ (by omega)
  have x23 : x.gpr .r23 = mask (wSq c true (wSq c true (wSq c true (wSq c true (Y, P))))).2 := by
    rw [kx.gpr .r23 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r23 (by decide), ku.gpr .r23 (by decide), p4]
  have x28 : x.gpr .r28 = BitVec.ofNat 64 (V >>> 60).toNat := by
    rw [kx.gpr .r28 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r28 (by decide), u28]
  refine WP.seq (WP.mono (update_ok fx.ctx.toEnv fx.consts hc3 hodd xy xl x23 x28 hdl)
    fun y ⟨⟨y23, ym⟩, ky⟩ => ?_)
  have fy := fx.stepW (by rw [ym]; exact Outs.refl _ _ _) ky (by decide) (by rw [ym])
  have y24 : y.gpr .r24 = V := by
    rw [ky.gpr .r24 (by decide), kx.gpr .r24 (by simp [Pub.montRegs, tailRegs]), kv.gpr .r24 (by decide),
      ku.gpr .r24 (by decide), h4]
  have hsh : WP isa (.block [.lsl .r24 .r24 4]) y fun z =>
      (z.gpr .r24 = V <<< 4 ∧ z.mem = y.mem) ∧ Keep [.r24] y z := by
    refine WP.keep _ ?_ (by decide)
    prun [y24]
  refine WP.mono hsh fun z ⟨⟨z24, zm⟩, kz⟩ => ⟨fy.stepW (by rw [zm]; exact Outs.refl _ _ _) kz (by decide)
    (by rw [zm]), by rw [zm, ym, xy], xl, ?_, z24⟩
  rw [kz.gpr .r23 (by decide), y23]
  rfl

end VG.Proof.MillerRabin.PPC64LE
