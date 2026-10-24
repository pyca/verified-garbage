module

public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Ctx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.RsaKeyGen.MrMont
import VerifiedGarbage.Proof.Bignum.Math
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Eq

/-!
# The Miller–Rabin round on PPC64LE: the table

`table_ok`: from the witness `b R mod c` in array 5 and `R mod c` in array
9, table entry `j` (array `11 + j`) holds `b^j R mod c` for every `j < 16`,
and `y` (array 6) holds `R mod c`.
-/

@[expose] public section

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)

/-- `selectAcc` with the bases already in `r5`, `r8` and `r9`. -/
theorem selectAt_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {b : Bool} {o a t : Nat}
    (ho : o < 28) (ha : a < 28) (ht : t < 28) (hoa : o ≠ a) (hot : o ≠ t)
    (h5 : s.gpr .r5 = off B (slot w o)) (h8 : s.gpr .r8 = off B (slot w a)) (h9 : s.gpr .r9 = off B (slot w t))
    (h20 : s.gpr .r20 = mask b) :
    WP isa selectAcc s fun s' =>
      (arr s'.mem B w o = (if b then arr s.mem B w a else arr s.mem B w t) ∧
        Outside B (slot w o) (8 * (w + 2)) s.mem s'.mem) ∧ Keep [.r0, .r3, .r14, .r15, .r16, .r17] s s' := by
  have sep := fun {j k : Nat} (hjk : j ≠ k) => slot_sep (w := w) hjk
  have hO := h.arr ho
  have hA := h.arr ha
  have hT := h.arr ht
  refine WP.mono (selectAcc_ok h.hs (dA := slot w a) (dT := slot w t) (dO := slot w o) (n := 2 * w) (b := b)
      h8 h9 h5 h.h11 h20 (by have := h.hw; omega) (by have := h.hw'; omega)
      (by omega) (by omega) (by omega)
      (by have := sep hoa; omega) (by have := sep hot; omega)) fun s' ⟨hv, hout, k⟩ =>
    ⟨⟨hv, hout.mono (Nat.le_refl _) (by omega)⟩, k⟩

theorem ones_ok (s : State) :
    WP isa (.block ones) s fun t => (t.gpr .r20 = mask true ∧ t.mem = s.mem) ∧ Keep [.r20] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold ones
  prun
  rfl

/-- The registers `copy` and `toEntry` write. -/
def copyRegs : List Reg := [.r0, .r3, .r5, .r8, .r9, .r14, .r15, .r16, .r17, .r20]

/-- `copy o a`: array `o` := array `a`. -/
theorem copy_ok {s : State} {B : Addr} {Z w : Nat} (h : Env s B Z w) {o a : Nat} (ho : o < 28) (ha : a < 28)
    (hoa : o ≠ a) :
    WP isa (copy o a) s fun t =>
      (arr t.mem B w o = arr s.mem B w a ∧ Outside B (slot w o) (8 * (w + 2)) s.mem t.mem) ∧
        Keep copyRegs s t := by
  unfold copy
  refine WP.seq (WP.mono (ones_ok s) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_)
  refine WP.mono (sel_ok (h.keep k1 (by decide)) ho ha ha hoa hoa h20) fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [m1] at hv hout
  exact ⟨⟨by simpa only [arr, ite_true] using hv, hout⟩, (k1.trans k).mono (by simp [selRegs, copyRegs])⟩

theorem entry_addr (B : Addr) (w j : Nat) :
    (BitVec.ofNat 64 j + BitVec.ofNat 64 11) * BitVec.ofNat 64 (8 * (w + 2)) + off B (slot w 0) =
      off B (slot w (11 + j)) := by
  simp only [off, slot, Impl.Bignum.hdrBytes, Nat.zero_mul, Nat.add_zero]
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_mul, Nat.add_comm 11 j, BitVec.ofNat_add 256]
  ac_rfl

/-- `entry`: the base of table entry `j` (in `r30`) into `r8`. -/
theorem entry_ok {s : State} {B : Addr} {Z w j : Nat} (h : Env s B Z w) (h30 : s.gpr .r30 = BitVec.ofNat 64 j) :
    WP isa (.block entry) s fun t => (t.gpr .r8 = off B (slot w (11 + j)) ∧ t.mem = s.mem) ∧ Keep [.r8] s t := by
  refine WP.keep _ ?_ (by decide)
  unfold entry
  prun [h30, h.h29, h.h10, aTab, entry_addr]

/-- `toEntry a`: table entry `j` (in `r30`) := array `a`. -/
theorem toEntry_ok {s : State} {B : Addr} {Z w j : Nat} (h : Env s B Z w) (h30 : s.gpr .r30 = BitVec.ofNat 64 j)
    (hj : j < 16) {a : Nat} (ha : a < 11) :
    WP isa (toEntry a) s fun t =>
      (arr t.mem B w (11 + j) = arr s.mem B w a ∧ Outside B (slot w (11 + j)) (8 * (w + 2)) s.mem t.mem) ∧
        Keep copyRegs s t := by
  unfold toEntry
  refine WP.seq ?_
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (ones_ok s) fun t₁ ⟨⟨h20, m1⟩, k1⟩ => ?_
  have e1 := h.keep k1 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (entry_ok (j := j) e1 (by rw [k1.gpr .r30 (by decide), h30])) fun t₂ ⟨⟨a8, m2⟩, k2⟩ => ?_
  have e2 := e1.keep k2 (by decide)
  rw [WP.block_append_iff]
  have hmv : WP isa (.block [.addi .r5 .r8 0]) t₂ fun t₃ =>
      (t₃.gpr .r5 = off B (slot w (11 + j)) ∧ t₃.mem = t₂.mem) ∧ Keep [.r5] t₂ t₃ := by
    refine WP.keep _ ?_ (by decide)
    prun [a8, BitVec.add_zero]
  refine WP.mono hmv fun t₃ ⟨⟨a5, m3⟩, k3⟩ => ?_
  have e3 := e2.keep k3 (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (e3.base (rd := .r8) (by decide) (by decide) a) fun t₄ ⟨⟨b8, m4⟩, k4⟩ => ?_
  have e4 := e3.keep k4 (by decide)
  refine WP.mono (e4.base (rd := .r9) (by decide) (by decide) a) fun t₅ ⟨⟨b9, m5⟩, k5⟩ => ?_
  have e5 := e4.keep k5 (by decide)
  have k15 := (((k1.trans k2).trans k3).trans k4).trans k5
  have hm : t₅.mem = s.mem := by rw [m5, m4, m3, m2, m1]
  refine WP.mono (selectAt_ok e5 (b := true) (o := 11 + j) (a := a) (t := a) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by rw [k5.gpr .r5 (by decide), k4.gpr .r5 (by decide), a5])
      (by rw [k5.gpr .r8 (by decide), b8]) b9
      ((((k2.trans k3).trans k4).trans k5).gpr .r20 (by decide) |>.trans h20)) fun t ⟨⟨hv, hout⟩, k⟩ => ?_
  rw [hm] at hv hout
  exact ⟨⟨by simpa only [ite_true] using hv, hout⟩, (k15.trans k).mono (by simp [copyRegs])⟩

end VG.Proof.MillerRabin.PPC64LE

namespace VG.Proof.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Proof.Mont VG.Proof.Bignum.PPC64LE
open VG.Impl.Bignum VG.Impl.Bignum.PPC64LE VG.Impl.MillerRabin.PPC64LE
open VG.Proof.Bignum (slot slot_sep)
open VG.Proof.RsaKeyGen (mont_val)

/-! ## Frames -/

/-- The registers the round's pieces write, but the flag's and the
exponent's. -/
def tabRegs : List Reg :=
  [.r0, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r14, .r15, .r16, .r17, .r18, .r19, .r20, .r22, .r30]

/-- What every step keeps, from `s₀`: the context, the constants, only the
round's arrays written, only `rs` among the registers. -/
structure Fr (rs : List Reg) (s₀ s : State) (B : Addr) (Z w c : Nat) : Prop where
  ctx : MCtx s B Z w
  consts : Consts s.mem B w c
  muts : Mut B w s₀.mem s.mem
  keep : Keep rs s₀ s

theorem Fr.trans {rs rs' : List Reg} {s₀ s t : State} {B : Addr} {Z w c : Nat} (h : Fr rs s₀ s B Z w c)
    (hm : Mut B w s.mem t.mem) (k : Keep rs' s t) (hrs : ∀ r ∈ rs', r ∈ rs) (hmr : ∀ r ∈ mctxRegs, r ∉ rs)
    (h0 : w32 t.mem B (slot w 0) = w32 s.mem B (slot w 0)) : Fr rs s₀ t B Z w c := by
  have hn : slot w 28 ≤ 2 ^ 64 := by have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega
  exact ⟨h.ctx.keep k (fun r hr hr' => hmr r hr (hrs r hr')) h0, h.consts.of_mut hm hn,
    Outs.trans h.muts hm, (h.keep.trans k).mono (fun r hr => by
      rcases List.mem_append.mp hr with hr | hr
      · exact hr
      · exact hrs r hr)⟩

theorem Fr.slot28 {rs : List Reg} {s₀ s : State} {B : Addr} {Z w c : Nat} (h : Fr rs s₀ s B Z w c) :
    slot w 28 ≤ 2 ^ 64 := by
  have := h.ctx.hs.nowrap; have := h.ctx.hZ; omega

/-- A block that writes only registers among `rs`. -/
theorem Fr.regs {rs rs' : List Reg} {s₀ s t : State} {B : Addr} {Z w c : Nat} (h : Fr rs s₀ s B Z w c)
    (hm : t.mem = s.mem) (k : Keep rs' s t) (hrs : ∀ r ∈ rs', r ∈ rs := by decide)
    (hmr : ∀ r ∈ mctxRegs, r ∉ rs := by decide) : Fr rs s₀ t B Z w c :=
  h.trans (by rw [hm]; exact Outs.refl _ _ _) k hrs hmr (by rw [hm])

/-- The table's entries below `j`. -/
def TabUpTo (m : Mem) (B : Addr) (w c b j : Nat) : Prop :=
  ∀ i < j, arr m B w (11 + i) = b ^ i % c * 2 ^ (64 * w) % c

/-- The whole table. -/
abbrev TabOK (m : Mem) (B : Addr) (w c b : Nat) : Prop := TabUpTo m B w c b 16

theorem pow_mul_mod (b i c : Nat) : b ^ i % c * (b % c) % c = b ^ (i + 1) % c := by
  rw [← Nat.mul_mod, Nat.pow_succ]

/-- The table, from `b R mod c` in array 5 and `R mod c` in array 9. -/
theorem table_ok {s : State} {B : Addr} {Z w c b : Nat} (h : MCtx s B Z w) (hc : Consts s.mem B w c)
    (hc3 : 3 ≤ c) (hodd : c % 2 = 1) (h5 : arr s.mem B w 5 = b % c * 2 ^ (64 * w) % c) :
    WP isa table s fun t => Fr tabRegs s t B Z w c ∧ arr t.mem B w 5 = arr s.mem B w 5 ∧
      TabOK t.mem B w c b ∧ arr t.mem B w aY = 2 ^ (64 * w) % c := by
  have hR := VG.Proof.Bignum.coprime_pow2 hodd (64 * w)
  have f0 : Fr tabRegs s s B Z w c := ⟨h, hc, Outs.refl _ _ _, Keep.refl _ _⟩
  have hn := f0.slot28
  have hc0 := hc.cand
  -- `r30 := j`
  have li30 : ∀ (j : Nat) (u : State), j < 2 ^ 15 →
      WP isa (.block [.li .r30 j]) u fun t => (t.gpr .r30 = BitVec.ofNat 64 j ∧ t.mem = u.mem) ∧ Keep [.r30] u t :=
    fun j u hj => by
      refine WP.keep _ ?_ (by simp [writesOnly, instrs, dstOf, Instr.writesLr])
      prun [hj]
  unfold table
  refine WP.seq (WP.mono (li30 0 s (by decide)) fun s₁ ⟨⟨a30, m1⟩, k1⟩ => ?_)
  have f1 := f0.regs m1 k1
  refine WP.seq (WP.mono (toEntry_ok f1.ctx.toEnv a30 (by decide) (a := aOne) (by decide))
    fun s₂ ⟨⟨v0, o2⟩, k2⟩ => ?_)
  have f2 := f1.trans (Mut.of_entry o2 (by decide)) k2 (by decide) (by decide) (Outside.w32_0 o2 (by decide) hn)
  refine WP.seq (WP.mono (li30 1 s₂ (by decide)) fun s₃ ⟨⟨b30, m3⟩, k3⟩ => ?_)
  have f3 := f2.regs m3 k3
  refine WP.seq (WP.mono (toEntry_ok f3.ctx.toEnv b30 (by decide) (a := aW) (by decide))
    fun s₄ ⟨⟨v1, o4⟩, k4⟩ => ?_)
  have f4 := f3.trans (Mut.of_entry o4 (by decide)) k4 (by decide) (by decide) (Outside.w32_0 o4 (by decide) hn)
  refine WP.seq (WP.mono (copy_ok f4.ctx.toEnv (o := aY) (a := aW) (by decide) (by decide) (by decide))
    fun s₅ ⟨⟨vy, o5⟩, k5⟩ => ?_)
  have f5 := f4.trans (Mut.of_outside o5 (by simp [aY])) k5 (by decide) (by decide) (Outside.w32_0 o5 (by decide) hn)
  refine WP.seq (WP.mono (li30 2 s₅ (by decide)) fun s₆ ⟨⟨c30, m6⟩, k6⟩ => ?_)
  have f6 := f5.regs m6 k6
  -- array 5 throughout
  have w5_1 : arr s₁.mem B w 5 = arr s.mem B w 5 := by rw [m1]
  have w5_2 : arr s₂.mem B w 5 = arr s.mem B w 5 := by rw [Outside.arrEq o2 (by decide) (by decide) hn, w5_1]
  have w5_4 : arr s₄.mem B w 5 = arr s.mem B w 5 := by
    rw [Outside.arrEq o4 (by decide) (by decide) hn, m3, w5_2]
  have w5_5 : arr s₅.mem B w 5 = arr s.mem B w 5 := by rw [Outside.arrEq o5 (by decide) (by decide) hn, w5_4]
  have w5_6 : arr s₆.mem B w 5 = arr s.mem B w 5 := by rw [m6, w5_5]
  -- the first two entries
  have t0 : arr s₂.mem B w 11 = b ^ 0 % c * 2 ^ (64 * w) % c := by
    rw [v0, m1, hc.one, Nat.pow_zero, Nat.mod_eq_of_lt (show 1 < c by omega), Nat.one_mul]
  have tab2 : TabUpTo s₆.mem B w c b 2 := by
    intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · rw [m6, Outside.arrEq o5 (by decide) (by decide) hn, Outside.arrEq o4 (by decide) (by decide) hn, m3]
      exact t0
    · rw [m6, Outside.arrEq o5 (by decide) (by decide) hn]
      show arr s₄.mem B w (11 + 1) = _
      rw [v1, m3, show aW = 5 from rfl, w5_2, h5, Nat.pow_one]
  have y6 : arr s₆.mem B w aY = b ^ 1 % c * 2 ^ (64 * w) % c := by
    rw [m6, vy, show aW = 5 from rfl, w5_4, h5, Nat.pow_one]
  refine WP.seq (WP.mono (count_loop (n := 14) (cr := .r4) (by decide)
      (fun k t => Fr tabRegs s t B Z w c ∧ t.gpr .r30 = BitVec.ofNat 64 (2 + k) ∧
        arr t.mem B w 5 = arr s.mem B w 5 ∧ TabUpTo t.mem B w c b (2 + k) ∧
        arr t.mem B w aY = b ^ (1 + k) % c * 2 ^ (64 * w) % c)
      (fun k hk t ⟨ft, t30, t5, ttab, ty⟩ => ?_) ⟨f6, c30, w5_6, tab2, y6⟩) fun t ⟨ft, _, t5, ttab, ty⟩ => ?_)
  · have tc := ft.consts.cand
    have hb5 : arr t.mem B w 5 < arr t.mem B w 0 := by
      rw [t5, h5, tc]; exact Nat.mod_lt _ (by omega)
    refine WP.seq (WP.mono (mont_ok ft.ctx (o := 6) (a := 6) (b := 5) (by simp) (by simp) (by simp) hb5)
      fun u ⟨⟨hlt, heq, hout, h0⟩, ku⟩ => ?_)
    have fu := ft.trans (Mut.of_mont hout (by simp)) ku (by decide) (by decide) h0
    have uy : arr u.mem B w aY = b ^ (2 + k) % c * 2 ^ (64 * w) % c := by
      rw [tc] at hlt heq
      rw [show 2 + k = (1 + k) + 1 by omega, ← pow_mul_mod]
      exact mont_val hR hlt heq ty (by rw [t5, h5])
    have u30 : u.gpr .r30 = BitVec.ofNat 64 (2 + k) := (ku.gpr .r30 (by decide)).trans t30
    refine WP.seq (WP.mono (toEntry_ok fu.ctx.toEnv u30 (by omega) (a := aY) (by decide))
      fun v ⟨⟨ve, vo⟩, kv⟩ => ?_)
    have fv := fu.trans (Mut.of_entry vo (by omega)) kv (by decide) (by decide) (Outside.w32_0 vo (by omega) hn)
    have hblk : WP isa (.block [.addi .r30 .r30 1, .subi .r4 .r30 16]) v fun x =>
        (x.gpr .r30 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 ∧
          x.gpr .r4 = BitVec.ofNat 64 (2 + k) + BitVec.ofNat 64 1 - BitVec.ofNat 64 16 ∧ x.mem = v.mem) ∧
          Keep [.r30, .r4] v x := by
      refine WP.keep _ ?_ (by decide)
      prun [(kv.gpr .r30 (by decide)).trans u30]
    refine WP.mono hblk fun x ⟨⟨x30, x4, xm⟩, kx⟩ => ⟨⟨fv.regs xm kx, ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [x30, ← BitVec.ofNat_add, Nat.add_assoc]
    · rw [xm, Outside.arrEq vo (by decide) (by omega) hn, Outs.arrEq_mont hout (by decide) (by decide)
        (by decide) (by decide) hn, t5]
    · intro i hi
      rw [xm]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < 2 + k + 1 by omega) with hi | rfl
      · rw [Outside.arrEq vo (by omega) (by omega) hn, Outs.arrEq_mont hout (by omega) (by omega) (by omega)
          (by omega) hn]
        exact ttab i hi
      · rw [ve, uy]
    · rw [xm, Outside.arrEq vo (by decide) (by simp only [aY]; omega) hn, uy, show 1 + (k + 1) = 2 + k by omega]
    · rw [x4, ← BitVec.ofNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
  · refine WP.mono (copy_ok ft.ctx.toEnv (o := aY) (a := aOne) (by decide) (by decide) (by decide))
      fun u ⟨⟨uy, uo⟩, ku⟩ => ?_
    have fu := ft.trans (Mut.of_outside uo (by simp [aY])) ku (by decide) (by decide)
      (Outside.w32_0 uo (by decide) hn)
    refine ⟨fu, ?_, fun i hi => ?_, ?_⟩
    · rw [Outside.arrEq uo (by decide) (by decide) hn, t5]
    · rw [Outside.arrEq uo (by omega) (by simp [aY]; omega) hn]
      exact ttab i (by omega)
    · rw [uy, ft.consts.one]

end VG.Proof.MillerRabin.PPC64LE
