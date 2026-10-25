module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.WinBase
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Four-bit windows on PPC64LE: selecting `T_d`

`select_ok`: array 5 := table entry `d` (array `8 + d`), for the digit `d`
in `r18`, by a scan of the whole table: each entry is copied or not under a
mask of `j = d`, so that no address depends on `d`.
-/

@[expose] public section

namespace VG.Proof.Bignum.PPC64LE.Win

open VG VG.PPC64LE VG.Proof.Mont VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.Bignum.PPC64LE.ModExp
open VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base montOp)

theorem sub1_sign {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (x - BitVec.ofNat 64 1) >>> 63 = BitVec.ofNat 64 (if x = 0 then 1 else 0) := by
  apply BitVec.eq_of_toNat_eq
  have : x = 0 ↔ x.toNat = 0 := ⟨fun h => by rw [h]; rfl, fun h => BitVec.eq_of_toNat_eq h⟩
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    this]
  split <;> omega_arith

theorem isDigit_ok {s : State} {j d : Nat} (h19 : s.gpr .r19 = BitVec.ofNat 64 j)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16) :
    WP isa (.block isDigit) s fun t => (t.gpr .r20 = mask (decide (j = d)) ∧ t.mem = s.mem) ∧
      Keep [.r0, .r3, .r20] s t := by
  have hx : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_xor, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith),
      Nat.mod_eq_of_lt (by omega_arith)]
    exact Nat.xor_lt_two_pow (by omega_arith) (by omega_arith)
  have he : (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0) ↔ j = d := by
    rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.xor_eq_zero_iff]
    constructor
    · intro e
      have := congrArg BitVec.toNat e
      rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_arith), Nat.mod_eq_of_lt (by omega_arith)]
        at this
    · rintro rfl; rfl
  refine WP.keep _ ?_ (by decide)
  unfold isDigit
  prun [h19, h18, sub1_sign hx]
  by_cases e : j = d
  · simp [e]
  · simp [e, show ¬ (BitVec.ofNat 64 j ^^^ BitVec.ofNat 64 d = 0#64) from fun h => e (he.mp h)]

/-- The registers a choice of an entry writes. -/
def pickRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- Array `o := j = d ? T_j : [t]`, for `j` in `r19` and `d` in `r18`. -/
theorem pick_ok {s : State} {B : Addr} {Z w N j d : Nat} (h : WCtx s B Z w N)
    (h19 : s.gpr .r19 = BitVec.ofNat 64 j) (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hj : j < 16) (hd : d < 16)
    {o t : Nat} (hot : o = 3 ∧ t = 5 ∨ o = 5 ∧ t = 3) :
    WP isa (.seq (.block (isDigit ++ entry ++ base .r9 t ++ base .r5 o)) selectAcc64) s
      fun s' => (A s'.mem B w o = (if j = d then A s.mem B w (8 + j) else A s.mem B w t) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem s'.mem) ∧ Keep pickRegs s s' := by
  have ho : o < 24 := by omega_arith
  have ht : t < 24 := by omega_arith
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (isDigit_ok h19 h18 hj hd) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  have e1 := h.regs k1 (by decide) m1
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) e1 (by rw [k1.gpr .r19 (by decide), h19])) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.regs k2 (by decide) m2
  rw [WP.block_append_iff]
  refine WP.mono (Pub.base_ok (rd := .r9) (by decide) (by decide) e2.r10 e2.r29 t) fun t₃ ⟨⟨a9, m3⟩, k3⟩ => ?_
  have e3 := e2.regs k3 (by decide) m3
  refine WP.mono (Pub.base_ok (rd := .r5) (by decide) (by decide) e3.r10 e3.r29 o) fun t₄ ⟨⟨a5, m4⟩, k4⟩ => ?_
  have e4 := e3.regs k4 (by decide) m4
  have hm : t₄.mem = s.mem := by rw [m4, m3, m2, m1]
  refine WP.mono (selectAt_ok e4 (b := decide (j = d)) (o := o) (a := 8 + j) (t := t) ho (by omega_arith) ht
      (by omega_arith) (by omega_arith) a5
      (by rw [k4.gpr .r8 (by decide), k3.gpr .r8 (by decide), a8])
      (by rw [k4.gpr .r9 (by decide), a9])
      (by rw [k4.gpr .r20 (by decide), k3.gpr .r20 (by decide), k2.gpr .r20 (by decide), h20]))
    fun s' ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  refine ⟨⟨by rw [hv]; by_cases e : j = d <;> simp [e], hout⟩, ?_⟩
  exact ((((k1.trans k2).trans k3).trans k4).trans k).mono

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

/-- The registers the selection writes. -/
def selectRegs : List Reg := pickRegs ++ [.r19, .r4]

/-- `select`: array 5 := `T_d`, for `d` in `r18`; only arrays 3 and 5 change. -/
theorem select_ok {s : State} {B : Addr} {Z w N d : Nat} (h : WCtx s B Z w N)
    (h18 : s.gpr .r18 = BitVec.ofNat 64 d) (hd : d < 16) :
    WP isa select s fun t =>
      (A t.mem B w 5 = A s.mem B w (8 + d) ∧ (∀ j < 24, j ≠ 3 → j ≠ 5 → A t.mem B w j = A s.mem B w j) ∧ WCtx t B Z w N ∧
        Outs B (win w) s.mem t.mem) ∧ Keep selectRegs s t := by
  have hn := h.nw
  -- What changes: arrays 3 and 5.
  let Ch : Mem → Mem → Prop := fun m m' => ∀ x, (Mont.ofs B x < slot w 3 ∨ slot w 3 + 8 * (w + 2) ≤ Mont.ofs B x) →
    (Mont.ofs B x < slot w 5 ∨ slot w 5 + 8 * (w + 2) ≤ Mont.ofs B x) → m' x = m x
  have ch_trans : ∀ {m₁ m₂ m₃ : Mem}, Ch m₁ m₂ → Ch m₂ m₃ → Ch m₁ m₃ := fun a b x h3 h5 =>
    (b x h3 h5).trans (a x h3 h5)
  have ch3 : ∀ {m m' : Mem}, Outside B (slot w 3) (8 * (w + 2)) m m' → Ch m m' := fun o x h3 _ => o x h3
  have ch5 : ∀ {m m' : Mem}, Outside B (slot w 5) (8 * (w + 2)) m m' → Ch m m' := fun o x _ h5 => o x h5
  have ch_arr : ∀ {m m' : Mem}, Ch m m' → ∀ j < 24, j ≠ 3 → j ≠ 5 → A m' B w j = A m B w j := by
    intro m m' hc j hj h3 h5
    have := slot_lt (w := w) hj
    have s3 := slot_sep (w := w) h3
    have s5 := slot_sep (w := w) h5
    refine val32_congr fun i hi => congrArg BitVec.toNat (Mem.readW_congr fun l hl => hc _ ?_ ?_)
    · rw [Mont.ofs_off B (by omega_arith)]; omega_arith
    · rw [Mont.ofs_off B (by omega_arith)]; omega_arith
  have ch_win : ∀ {m m' : Mem}, Ch m m' → Outs B (win w) m m' := fun hc x hx => hc x (by
    have := hx _ (List.mem_singleton_self _)
    have := slot_win (w := w) (o := 3) (by decide) (by decide)
    simp only [Mont.ofs] at *; omega_arith) (by
    have := hx _ (List.mem_singleton_self _)
    have := slot_win (w := w) (o := 5) (by decide) (by decide)
    simp only [Mont.ofs] at *; omega_arith)
  unfold select
  have hpre : WP isa (.block [.li .r19 0]) s fun t => (t.gpr .r19 = BitVec.ofNat 64 0 ∧ t.mem = s.mem) ∧
      Keep [.r19] s t := by
    refine WP.keep _ ?_ (by decide)
    prun
  refine WP.seq (WP.mono hpre fun t₀ ⟨⟨a19, m0⟩, k0⟩ => ?_)
  let I : Nat → State → Prop := fun k t => WCtx t B Z w N ∧ t.gpr .r18 = BitVec.ofNat 64 d ∧
    t.gpr .r19 = BitVec.ofNat 64 (2 * k) ∧
    A t.mem B w 5 = (if d < 2 * k then A s.mem B w (8 + d) else A s.mem B w 5) ∧
    Ch s.mem t.mem ∧ Keep selectRegs s t
  refine WP.mono (count_loop (n := 8) (cr := .r4) (by decide) I (fun k hk t ⟨et, t18, t19, t5, tout, kt⟩ => ?_)
    ⟨h.regs k0 (by decide) m0, by rw [k0.gpr .r18 (by decide), h18], a19, (by rw [m0]; simp),
      (by rw [m0]; exact fun _ _ _ => rfl), k0.mono⟩)
    fun t ⟨ct, _, _, t5, tout, kt⟩ => ⟨⟨by rw [t5, ite_eq_left_of_eq_true _ _ (eq_true (by omega_arith))],
        ch_arr tout, ct, ch_win tout⟩, kt⟩
  -- The first entry of the pair, into array 3.
  refine wp_seq_assoc (WP.mono (pick_ok et t19 t18 (by omega_arith) hd (o := 3) (t := 5) (by simp))
    fun u ⟨⟨u3, uo⟩, ku⟩ => ?_)
  have eu := et.of ku (by decide) (win_of_out uo (by decide) (by decide))
  -- The second, into array 5.
  rw [show ([.addi .r19 .r19 1] ++ isDigit ++ entry ++ base .r9 3 ++ base .r5 5) =
      [.addi .r19 .r19 1] ++ (isDigit ++ entry ++ base .r9 3 ++ base .r5 5) by simp only [List.append_assoc]]
  refine wp_seq_assoc (wp_block_prefix_seq ?_)
  have hinc : WP isa (.block [.addi .r19 .r19 1]) u fun v =>
      (v.gpr .r19 = BitVec.ofNat 64 (2 * k + 1) ∧ v.mem = u.mem) ∧ Keep [.r19] u v := by
    refine WP.keep _ ?_ (by decide)
    prun [(ku.gpr .r19 (by decide)).trans t19, ← BitVec.ofNat_add]
  refine WP.mono hinc fun v ⟨⟨v19, vm⟩, kv⟩ => ?_
  have ev := eu.regs kv (by decide) vm
  refine (WP.mono (pick_ok ev v19 (by rw [kv.gpr .r18 (by decide), ku.gpr .r18 (by decide), t18])
    (by omega_arith) hd (o := 5) (t := 3) (by simp)) fun x ⟨⟨x5, xo⟩, kx⟩ => ?_)
  have ex := ev.of kx (by decide) (win_of_out xo (by decide) (by decide))
  have hend : WP isa (.block [.addi .r19 .r19 1, .subi .r4 .r19 16]) x fun y =>
      (y.gpr .r19 = BitVec.ofNat 64 (2 * (k + 1)) ∧
        y.gpr .r4 = BitVec.ofNat 64 (2 * (k + 1)) - BitVec.ofNat 64 16 ∧ y.mem = x.mem) ∧ Keep [.r19, .r4] x y := by
    refine WP.keep _ ?_ (by decide)
    prun [(kx.gpr .r19 (by decide)).trans v19, ← BitVec.ofNat_add,
      show 2 * k + 1 + 1 = 2 * (k + 1) by omega_arith]
  have Cx : Ch s.mem x.mem := ch_trans (ch_trans tout (ch3 uo)) (by rw [← vm]; exact ch5 xo)
  refine WP.mono hend fun y ⟨⟨y19, y4, ym⟩, ky⟩ => ⟨⟨ex.regs ky (by decide) ym, by
    rw [ky.gpr .r18 (by decide), kx.gpr .r18 (by decide), kv.gpr .r18 (by decide), ku.gpr .r18 (by decide), t18],
    y19, ?_, by rw [ym]; exact Cx, ?_⟩, ?_⟩
  · rw [ym, x5, vm, u3, t5, ch_arr (ch_trans tout (ch3 uo)) (8 + (2 * k + 1)) (by omega_arith) (by omega_arith) (by omega_arith),
      ch_arr tout (8 + 2 * k) (by omega_arith) (by omega_arith) (by omega_arith)]
    split_ifs <;> (try subst_vars) <;> first | rfl | (exfalso; omega_arith)
  · exact (kt.trans ((((ku.trans kv).trans kx).trans ky))).mono
  · rw [y4, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega_arith

end VG.Proof.Bignum.PPC64LE.Win
