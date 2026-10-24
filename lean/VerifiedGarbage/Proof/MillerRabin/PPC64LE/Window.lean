module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Table
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math

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
    WP isa (.seq (.block (isDigit ++ entry ++ PublicChecked.base .r9 t ++ PublicChecked.base .r5 o)) selectAcc) s
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

end VG.Proof.MillerRabin.PPC64LE
