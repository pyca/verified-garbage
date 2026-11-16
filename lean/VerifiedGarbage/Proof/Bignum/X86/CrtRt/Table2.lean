module

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.Ctx
public import VerifiedGarbage.Proof.Mont.X86.WindowWords
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Mont.X86.ExponentInitMath

/-! ### `Bignum.X86.CrtRt.Table`, which only this module used -/

section

/-! ### `Bignum.X86.CrtRt.Shift`, which only this module used -/

section

/-! # The next window of a run-time-width exponentiation

`shiftLoop` shifts a number up by four bits (`shiftLoop_ok`); `nextWindow`
stores the exponent's top four bits in the window word and shifts the
exponent past them (`nextWindow_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Mont.X86.Dynamic (times16_toNat shr28_toNat shift_top val32_top_bits)
open VG.Proof.Bignum.X86.PublicRt (countLoop ptr4)

theorem shiftLoop_ok {t₀ : State} {W : Addr} {L : Nat} (hw : Ws t₀ W L) {x N : Nat} (hN : 0 < N)
    (hx : x + 4 * N ≤ L) (hebp : PtrAt t₀ W .ebp x) (hedx : (t₀.gpr .edx).toNat = 4 * N)
    (hecx : t₀.gpr .ecx = 0) :
    WP isa shiftLoop t₀ fun u => Outside W x (4 * N) t₀.mem u.mem ∧
      val32 u.mem W x N = val32 t₀.mem W x N * 16 % 2 ^ (32 * N) ∧ Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ u := by
  have hn := hw.nowrap
  refine WP.mono (countLoop hN (fun j t => Keeps [.eax, .ebx, .ecx, .edx, .ebp] t₀ t ∧ PtrAt t W .ebp (x + 4 * j) ∧
      (t.gpr .edx).toNat = 4 * (N - j) ∧ Outside W x (4 * j) t₀.mem t.mem ∧
      val32 t.mem W x j = val32 t₀.mem W x j * 16 % 2 ^ (32 * j) ∧
      (t.gpr .ecx).toNat = val32 t₀.mem W x j * 16 / 2 ^ (32 * j)) ?_
    ⟨Keeps.refl _ _, by simpa using hebp, by simpa using hedx, Outside.refl _ _ _ _,
      by simp only [val32, Nat.zero_mul, Nat.zero_mod],
      by rw [hecx]; simp only [val32, Nat.zero_mul, Nat.zero_div]; rfl⟩)
    fun u ⟨K, _, _, O, V, _⟩ => ⟨O, V, K⟩
  rintro j t hj ⟨Kt, ebp, edx, O, V, C⟩
  obtain ht := hw.of_keeps Kt
  refine wp_movS (readSrc_ptr ht ebp (d := 0) (by omega_using [hx, hj])) fun s₂ u₂ _ => ?_
  refine wp_movS rfl fun s₃ u₃ _ => VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun s₄ u₄ => ?_
  refine wp_addS rfl fun s₅ u₅ _ => wp_addS rfl fun s₆ u₆ _ => wp_addS rfl fun s₇ u₇ _ => ?_
  refine wp_addS rfl fun s₈ u₈ _ => wp_addS rfl fun s₉ u₉ _ => ?_
  obtain k₉ : Keeps [.eax, .ebx] t s₉ := (((((((u₂.keeps.mono (by decide)).widen u₃.keeps).widen
    u₄.keeps).widen u₅.keeps).widen u₆.keeps).widen u₇.keeps).widen u₈.keeps).widen u₉.keeps
  obtain ht₉ := ht.of_keeps k₉
  obtain ebp₉ : PtrAt s₉ W .ebp (x + 4 * j) := by rw [PtrAt, k₉.1 _ (by decide)]; exact ebp
  refine wp_storeS (ea_ptr ht₉ ebp₉ (d := 0) (by omega_using [hx, hj]))
    (ws_write ht₉ (y := x + 4 * j + 0) (n := 4) (by omega_using [hx, hj])) fun s₁₀ m₁₀ => ?_
  refine wp_movS rfl fun s₁₁ u₁₁ _ => wp_addS rfl fun s₁₂ u₁₂ _ => wp_subZ rfl fun s₁₃ u₁₃ z₁₃ => WP.block_nil ?_
  obtain ⟨c₁, c₂⟩ := count_zf edx hj
  obtain mem₉ : s₉.mem = t.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  obtain word : w32 t.mem W (x + 4 * j) = w32 t₀.mem W (x + 4 * j) :=
    O.w32 (by omega_using []) (by omega_using [hx, hj, hn])
  obtain ecx₈ : s₈.gpr .ecx = t.gpr .ecx := by
    rw [u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide),
      u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide)]
  obtain value : (s₉.gpr .eax).toNat =
      w32 t₀.mem W (x + 4 * j) * 16 % 2 ^ 32 + val32 t₀.mem W x j * 16 / 2 ^ (32 * j) := by
    rw [u₉.gpr, BitVec.toNat_add, ecx₈, C, u₈.gpr, u₇.gpr, u₆.gpr, u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, times16_toNat]
    change (w32 t.mem W (x + 4 * j + 0) * 16 % 2 ^ 32 + _) % 2 ^ 32 = _
    rw [Nat.add_zero, word]
    have : val32 t₀.mem W x j * 16 / 2 ^ (32 * j) < 16 :=
      (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by have := val32_lt t₀.mem W x j; omega_arith)
    omega_arith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact Kt.trans ((((k₉.mono (by decide)).trans (m₁₀.keeps _)).trans (u₁₁.keeps.mono (by decide))).trans
      ((u₁₂.keeps.mono (by decide)).trans (u₁₃.keeps.mono (by decide))))
  · rw [PtrAt, u₁₃.other _ (by decide), u₁₂.gpr, u₁₁.other _ (by decide), m₁₀.gpr]; exact ptr4 ebp₉
  · rw [u₁₃.gpr, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide)]; exact c₁
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, mem₉, Nat.add_zero]
    exact (O.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [hx, hj, hn])).mono (by omega_using []) (by omega_using []))
  · rw [u₁₃.mem, u₁₂.mem, u₁₁.mem, m₁₀.mem, mem₉, Nat.add_zero, val32_store hn (by omega_using [hx, hj]), V, value,
      val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), shift_top (Nat.two_pow_pos _) (val32_lt _ _ _ _)]
  · rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr, m₁₀.gpr, u₉.other _ (by decide),
      u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.gpr, u₂.gpr, shr28_toNat, val32_top_bits, Nat.add_zero]
    exact congrArg (· / 2 ^ 28) word
  · rw [z₁₃, u₁₂.other _ (by decide), u₁₁.other _ (by decide), m₁₀.gpr, k₉.1 _ (by decide), c₂]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

theorem nextWindow_ok (h : In Ex base bytes len args s) (c : Ctx) :
    WP isa (nextWindow c) s fun u =>
      Frame (frameR base (s.gpr .esp) [(winOff, 4), (lo len (.slot c 8), bc len c)]) s.mem u.mem ∧
      w32 u.mem base winOff = sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c) ∧
      sv u.mem base len c 8 = sv s.mem base len c 8 * 16 % 2 ^ (32 * cwc len c) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u := by
  have nw' := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain g := bc_ge h.lower' c
  obtain hb := bc_le h.upper' c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain lo8 : numBase ≤ lo len (.slot c 8) := by simp [lo]
  have nb : numBase = 3336 := rfl
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain ⟨k, ek⟩ : ∃ k, cwc len c = k + 1 := ⟨cwc len c - 1, by omega_arith⟩
  unfold nextWindow
  simp only [List.append_assoc]
  -- The window word.
  refine WP.seq (ptrTo_ok (r := .eax) (t := .edx) (x := .slot c 8) (by decide) (by decide) h.edi h.width
    h.upper' (by omega_arith) fun u₁ K₁ m₁ p₁ => ?_)
  obtain h₁ := h.regs K₁ m₁
  refine widthC_ok (k := 0) (c := c) (r := .edx) h₁.width h.upper' fun u₂ K₂ m₂ e₂ => ?_
  refine wp_addS rfl fun u₃ a₃ _ => wp_subS rfl fun u₄ a₄ _ => ?_
  obtain K₄ : Keeps [.eax, .edx] s u₄ :=
    (((K₁.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (a₄.keeps.mono (by decide))
  obtain ws₄ := h.ws.of_keeps K₄
  obtain p₄ : PtrAt u₄ base .eax (lo len (.slot c 8) + 4 * k) := by
    rw [PtrAt, a₄.gpr, a₃.gpr, K₂.1 _ (by decide), e₂]
    rw [show (4 : BitVec 32) = BitVec.ofNat 32 4 from rfl, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      ← BitVec.sub_eq_add_neg, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega_arith) (by omega_arith), ptr_add p₁,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := bc len c - 4) (by omega_arith)]
    congr 2; omega_arith
  refine wp_movS (readSrc_ptr ws₄ p₄ (d := 0) (by omega_arith)) fun u₅ a₅ _ => ?_
  refine VG.Proof.Bignum.X86.PublicRt.wp_shr (by decide) fun u₆ a₆ => ?_
  obtain K₆ : Keeps [.eax, .edx] s u₆ := (K₄.trans (a₅.keeps.mono (by decide))).trans (a₆.keeps.mono (by decide))
  obtain h₆ := h.regs K₆ (by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, m₂, m₁])
  refine wp_storeS (h₆.scratch.ea (d := winOff) (by simp only [winOff]; omega_arith))
    (h₆.scratch.write (d := winOff) (by simp only [winOff]; omega_arith)) fun u₇ m₇ => WP.block_nil ?_
  obtain mem₆ : u₆.mem = s.mem := by rw [a₆.mem, a₅.mem, a₄.mem, a₃.mem, m₂, m₁]
  obtain W₇ : Outside base winOff 4 s.mem u₇.mem := by
    rw [m₇.mem, ← mem₆]; exact writeW32_outside _ _ _ (by simp only [winOff]; omega_arith)
  obtain win₇ : w32 u₇.mem base winOff = sv s.mem base len c 8 * 16 / 2 ^ (32 * cwc len c) := by
    rw [m₇.mem, w32_write_self, a₆.gpr, a₅.gpr, shr28_toNat, a₄.mem, a₃.mem, m₂, m₁, Nat.add_zero]
    simp only [sv]
    rw [ek, val32_top_bits]
  obtain K₇ : Keeps [.eax, .edx] s u₇ := K₆.trans (m₇.keeps _)
  obtain h₇ := h.keep K₇ (by decide) (by decide) (W₇.mono (Nat.zero_le _) (by simp only [winOff]; omega_arith))
  -- The exponent shifted.
  refine WP.seq (ptrTo_ok (r := .ebp) (t := .edx) (x := .slot c 8) (by decide) (by decide) h₇.edi h₇.width
    h.upper' (by omega_arith) fun u₈ K₈ m₈ p₈ => ?_)
  obtain h₈ := h₇.regs K₈ m₈
  refine cntTo_ok (r := .edx) (n := one c) h₈.width h.upper' (one_ok c).extra fun u₉ K₉ m₉ c₉ => ?_
  refine wp_movS rfl fun u₁₀ a₁₀ _ => WP.block_nil ?_
  obtain K₁₀ : Keeps [.ecx, .edx, .ebp] u₇ u₁₀ :=
    ((K₈.mono (by decide)).trans (K₉.mono (by decide))).trans (a₁₀.keeps.mono (by decide))
  refine WP.mono (shiftLoop_ok (h₇.ws.of_keeps K₁₀) (x := lo len (.slot c 8)) (N := cwc len c) (by omega_arith)
    (by omega_arith) (by rw [PtrAt, a₁₀.other _ (by decide), K₉.1 _ (by decide)]; exact p₈)
    (by rw [a₁₀.other _ (by decide), cnt_toNat h.upper' (one_ok c) c₉, cw1])
    a₁₀.gpr) fun u ⟨O, V, K⟩ => ?_
  obtain m₁₀ : u₁₀.mem = u₇.mem := by rw [a₁₀.mem, m₉, m₈]
  refine ⟨?_, ?_, ?_, ((K₇.mono (by decide)).trans (K₁₀.mono (by decide))).trans K⟩
  · rw [← m₁₀] at W₇
    obtain O' : Outside base (lo len (.slot c 8)) (bc len c) u₁₀.mem u.mem := by rw [bw]; exact O
    exact (frameR_of_outside W₇ (by simp only [winOff]; omega_arith) (by simp)).trans
      (frameR_of_outside O' (by omega_arith) (by simp))
  · rw [O.w32 (d := winOff) (by simp only [winOff]; omega_arith) (by simp only [winOff]; omega_arith), m₁₀, win₇]
  · simp only [sv]
    rw [V, m₁₀, W₇.val32 (by simp only [winOff]; omega_arith) (by omega_arith)]

end

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # The table of a run-time-width windowed exponentiation

Entry `j` of the table lies at `te len c j`, in the wide slots from 20
(`entryPtr_ok`). A selection by pointers set up in registers ends by
reloading `edi` (`selectTail_ok`). The table holds `b^j R mod M` for
`j < 16` (`buildTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Bignum.X86.PublicRt (adds_ok selectLoop_ok)
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- Entry `j` of the table. -/
abbrev te (len : Nat) (c : Ctx) (j : Nat) : Nat := lo len (.slot .wide 20) + j * bc len c

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32}

/-- The table, and slots 0 to 8 of the context, within the working space and apart. -/
theorem In.table_fit (h : In Ex base bytes len args s) (c : Ctx) :
    lo len (.slot c 8) + st len c ≤ lo len (.slot .wide 20) ∧ te len c 16 < bytes := by
  obtain f27 := h.slot_fit .wide (j := 27) (by decide)
  obtain hb := bc_half_le' len
  obtain g := bc_ge h.lower' .wide
  obtain hst : st len c ≤ st len .wide := by cases c <;> simp only [st] <;> omega_arith
  obtain hbc : bc len c ≤ bc len .wide := by cases c <;> simp only [st] at hst <;> omega_arith
  obtain m1 : 9 * st len c ≤ 9 * st len .wide := Nat.mul_le_mul_left 9 hst
  obtain m2 : 16 * bc len c ≤ 16 * bc len .wide := Nat.mul_le_mul_left 16 hbc
  have e8 : lo len (.slot c 8) = numBase + 8 * st len c := rfl
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have e27 : lo len (.slot .wide 27) = numBase + 27 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have et : te len c 16 = lo len (.slot .wide 20) + 16 * bc len c := rfl
  rw [e27] at f27
  rw [e8, e20, et, e20]
  omega_using [f27, hst, hbc, est]

theorem entryPtr_ok {is : List Instr} {Q : State → Prop} {c : Ctx} {j : Nat} {r t : Reg} (hrt : r ≠ t)
    (hte : t ≠ .edi) (hre : r ≠ .esp) (hts : t ≠ .esp) (hedi : (s.gpr .edi).toNat = base.toNat)
    (hr : readSrc s (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len)) (hl : len ≤ 1024) (hj : j ≤ 16)
    (kk : ∀ u, Keeps [r, t] s u → u.mem = s.mem → PtrAt u base r (te len c j) → WP isa (.block is) u Q) :
    WP isa (.block (entryPtr c r j t ++ is)) s Q := by
  obtain hb := bc_le hl c
  obtain hw := bc_le hl .wide
  have e20 : lo len (.slot .wide 20) = numBase + 20 * st len .wide := rfl
  have est : st len .wide = 2 * bc len .wide + 32 := rfl
  have nb : numBase = 3336 := rfl
  obtain hlo : lo len (.slot .wide 20) < 2 ^ 32 := by rw [e20, est, nb]; omega_using [hw]
  simp only [entryPtr, List.append_assoc]
  refine ptrTo_ok (x := .slot .wide 20) hrt hte hedi hr hl hlo
    fun u K m p => ?_
  obtain hr' : readSrc u (.mem (argAt 0 1)) = some (BitVec.ofNat 32 len) := by
    rw [← hr]; simp only [readSrc, State.load32, State.ea, argAt, at_, K.1 .esp (by simp [hre.symm, hts.symm]), m,
      K.2.1, K.2.2]; rfl
  refine widthC_ok (k := 0) (c := c) (r := t) hr' hl fun v Kv mv ev => adds_ok hrt j fun w Kw mw ew => ?_
  refine kk w ((K.trans (Kv.mono (by simp))).trans (Kw.mono (by simp))) (by rw [mw, mv, m]) ?_
  rw [PtrAt, ew, Kv.1 _ (by simp [hrt]), BitVec.toNat_add, p, ev, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := bc len c) (by omega_using [hb])]
  have : j * bc len c ≤ 16 * 1024 := Nat.mul_le_mul hj hb
  rw [Nat.mod_eq_of_lt (a := j * bc len c) (by omega_using [this]), Nat.mod_add_mod, Nat.add_assoc]

/-- A selection under the mask `ecx` through `ebp` (source) and `ebx` (destination), `edi` counting
the bytes, then `edi` reloaded: from `s₀`, whose inputs hold, by register changes. -/
theorem selectTail_ok {s₀ : State} (h : In Ex base bytes len args s₀)
    (K₀ : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ s) (m₀ : s.mem = s₀.mem)
    {x d N : Nat} {k : Bool} (hN : 0 < N) (hx : x + 4 * N ≤ bytes) (hd : d + 4 * N ≤ bytes)
    (hxd : d + 4 * N ≤ x ∨ x + 4 * N ≤ d) (pe : PtrAt s base .ebp x) (pb : PtrAt s base .ebx d)
    (ce : (s.gpr .edi).toNat = 4 * N) (hk : s.gpr .ecx = cmask k) :
    WP isa (.seq selectLoop (.block restoreEdi)) s fun u =>
      Outside base d (4 * N) s.mem u.mem ∧
      val32 u.mem base d N = (if k then val32 s.mem base x N else val32 s.mem base d N) ∧
      PtrAt u base .ebx (d + 4 * N) ∧
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s₀ u := by
  obtain ws : Ws s base bytes := h.ws.of_keeps K₀
  have hn := h.scratch.nowrap
  refine WP.seq (WP.mono (selectLoop_ok ws (x := x) (d := d) (N := N) k hN hx hd hxd pe pb ce hk)
    fun t ⟨O, V, pbt, Kt⟩ => ?_)
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .edi] s₀ t := K₀.trans (Kt.mono (by decide))
  obtain Oall : Outside base 0 bytes s₀.mem t.mem := by rw [← m₀]; exact O.mono (Nat.zero_le _) (by omega_using [hd])
  refine wp_movS ((h.stack 16 (by decide)).keep Kall (by decide) Oall).readSrc fun t₁ u₁ _ => WP.block_nil ?_
  obtain ed : t₁.gpr .edi = s₀.gpr .edi := by rw [u₁.gpr]; exact h.edi_eq
  refine ⟨by rw [u₁.mem]; exact O, by rw [u₁.mem]; exact V, by rw [PtrAt, u₁.other _ (by decide)]; exact pbt,
    PublicRt.Keeps.drop_edi (rs := [.eax, .ebx, .ecx, .edx, .ebp]) ?_ ed⟩
  exact (Kall.trans (u₁.keeps.mono (by decide))).mono (by decide)

end

end VG.Proof.Bignum.X86.CrtRt

end

end


/-! # Building the table of a run-time-width windowed exponentiation

Entries 0 and 1 copied from one and the base in Montgomery form, and each
next entry the product of the one below and the base (`buildTable_ok`).
-/

@[expose] public section

namespace VG.Proof.Bignum.X86.CrtRt

variable {Ex : List Region → List Region → Prop}

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Bignum.X86 VG.Impl.Bignum.X86.CrtRt VG.Proof.Mont
open VG.Proof.Mont.X86 VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Impl.Bignum.X86.PublicRt (argAt)

/-- The ranges `buildTable` changes. -/
abbrev tabR (len : Nat) (c : Ctx) : List (Nat × Nat) :=
  [(te len c 0, 16 * bc len c), (lo len (.slot c 7), bc len c), (lo len (.slot c 1), 3 * bc len c + 56)]

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- The pointers of a copy of slot `x` into entry `j`. -/
theorem copySetup_ok (h : In Ex base bytes len args s) {x j : Nat} (hx : x ≤ 8) (hj : j ≤ 15) {Q : State → Prop}
    (k : ∀ w, Keeps [.ebx, .ecx, .edx, .ebp, .edi] s w → w.mem = s.mem →
      PtrAt w base .ebp (lo len (.slot c x)) → PtrAt w base .ebx (te len c j) →
      (w.gpr .edi).toNat = 4 * cwc len c → w.gpr .ecx = cmask true → Q w) :
    WP isa (.block (([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++ ptrTo (.slot c x) .ebp .edx ++
      entryPtr c .ebx j .edx ++ cntTo (one c) .edi)) s Q := by
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  have bl := h.bytes_lt
  obtain hx8 : lo len (.slot c x) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hx; simp only [lo]; omega_arith
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_movS rfl fun w₁ u₁ _ => ?_
  obtain h₁ := h.regs u₁.keeps u₁.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (by decide) (by decide) h₁.edi h₁.width h.upper' (by omega_arith)
    fun w₂ K₂ m₂ p₂ => ?_
  obtain h₂ := h₁.regs K₂ m₂
  refine entryPtr_ok (c := c) (j := j) (r := .ebx) (t := .edx) (by decide) (by decide) (by decide) (by decide)
    h₂.edi h₂.width h.upper' (by omega_arith) fun w₃ K₃ m₃ p₃ => ?_
  obtain h₃ := h₂.regs K₃ m₃
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) h₃.width h.upper' (one_ok c).extra fun w₄ K₄ m₄ c₄ => WP.block_nil ?_
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  refine k w₄ ((((u₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (K₃.mono (by decide))).trans
    (K₄.mono (by decide))) (by rw [m₄, m₃, m₂, u₁.mem]) ?_ ?_ ?_ ?_
  · rw [PtrAt, K₄.1 _ (by decide), K₃.1 _ (by decide)]; exact p₂
  · rw [PtrAt, K₄.1 _ (by decide)]; exact p₃
  · rw [cnt_toNat h.upper' (one_ok c) c₄, cw1]
  · rw [K₄.1 _ (by decide), K₃.1 _ (by decide), K₂.1 _ (by decide), u₁.gpr]; rfl

/-- A copy of slot `x` into entry `j`, then `P`. -/
theorem copyEntry_ok (h : In Ex base bytes len args s) {x j : Nat} (hx : x ≤ 8) (hj : j ≤ 15) {P : Prog isa}
    {Q : State → Prop}
    (k : ∀ u, Outside base (te len c j) (bc len c) s.mem u.mem →
      val32 u.mem base (te len c j) (cwc len c) = sv s.mem base len c x →
      Keeps [.eax, .ebx, .ecx, .edx, .ebp] s u → WP isa P u Q) :
    WP isa (.seq (.block (([.mov .ecx (.imm (BitVec.allOnes 32))] : List Instr) ++ ptrTo (.slot c x) .ebp .edx ++
      entryPtr c .ebx j .edx ++ cntTo (one c) .edi)) (.seq (.seq selectLoop (.block restoreEdi)) P)) s Q := by
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  obtain hx8 : lo len (.slot c x) ≤ lo len (.slot c 8) := by
    have := Nat.mul_le_mul_right (st len c) hx; simp only [lo]; omega_arith
  obtain hj16 : te len c j + bc len c ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega_arith)
    rw [Nat.succ_mul] at this
    show lo len (.slot .wide 20) + j * bc len c + bc len c ≤ lo len (.slot .wide 20) + 16 * bc len c
    omega_arith
  obtain t0 : te len c 0 ≤ te len c j := by simp [te]
  obtain t0' : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  have est : st len c = 2 * bc len c + 32 := rfl
  refine WP.seq (copySetup_ok (c := c) h hx hj fun w K m pe pb ce ck => ?_)
  refine WP.seq (WP.mono (selectTail_ok h (K.mono (by decide)) m (x := lo len (.slot c x)) (d := te len c j)
    (N := cwc len c) (k := true) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    pe pb ce ck) fun u ⟨O, V, _, Ku⟩ => k u ?_ ?_ Ku)
  · rw [← m, bw]; exact O
  · rw [V, m]; simp

end

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

/-- The table at entry `i` of its loop: entries below `i` filled, slot 7 the last, `esi` at entry `i`. -/
structure TabInv (Ex : List Region → List Region → Prop) (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) (c : Ctx) (M b : Nat) (s₀ : State)
    (i : Nat) (t : State) : Prop where
  ctx : CtxOk Ex base bytes len args c M t
  keeps : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s₀ t
  frame : Frame (frameR base (s₀.gpr .esp) (tabR len c)) s₀.mem t.mem
  table : ∀ j < i, val32 t.mem base (te len c j) (cwc len c) = b ^ j * 2 ^ (8 * bc len c) % M
  last : sv t.mem base len c 7 = b ^ (i - 1) * 2 ^ (8 * bc len c) % M
  ptr : PtrAt t base .esi (te len c i)

theorem tabR_fit (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ tabR len c, p.1 + p.2 ≤ bytes := by
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e7 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain e14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  obtain e48 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain t16 : te len c 0 + 16 * bc len c = te len c 16 := by simp [te]
  intro p hp
  simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- The table's ranges lie past slot 0 and the header. -/
theorem tabR_past (h : In Ex base bytes len args s) (c : Ctx) : ∀ p ∈ tabR len c, numBase + bc len c ≤ p.1 := by
  obtain T := h.table_fit c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 1) := sl_le c (by decide)
  obtain e17 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  intro p hp
  simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith

/-- A multiplication into slot 7 keeps the table. -/
theorem mulR7_te (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (mulR len c 7)) m m') (R : CallRoom sp base bytes) {j : Nat} (hj : j < 16) :
    val32 m' base (te len c j) (cwc len c) = val32 m base (te len c j) (cwc len c) := by
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e17 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain tj : te len c j + bc len c ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ 16 by omega_arith)
    simp only [te]; rw [Nat.succ_mul] at this; omega_arith
  obtain tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega_arith
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  refine frameR_val32 F R h.scratch.nowrap (by omega_arith) ?_ ?_ <;>
    intro p hp <;> simp only [mulR, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
    rcases hp with rfl | rfl <;> dsimp only <;> omega_arith

/-- The table's ranges keep slot 5. -/
theorem tabR_slot5 (h : In Ex base bytes len args s) {sp : BitVec 32} {m m' : Mem}
    (F : Frame (frameR base sp (tabR len c)) m m') (R : CallRoom sp base bytes) :
    val32 m' base (lo len (.slot c 5)) (cwc len c) = val32 m base (lo len (.slot c 5)) (cwc len c) := by
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e1 : lo len (.slot c 1) = numBase + st len c := by simp [lo]
  have e5 : lo len (.slot c 5) = numBase + 5 * st len c := rfl
  obtain e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega_arith
  refine frameR_val32 F R h.scratch.nowrap (by omega_arith) ?_ (tabR_fit h c)
  intro p hp; simp only [tabR, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> dsimp only <;> omega_arith

end

/-- Two pointers into the working space are equal exactly when their offsets are. -/
theorem ptr_beq {s : State} {W : Addr} {r q : Reg} {a b : Nat} (ha : PtrAt s W r a) (hb : PtrAt s W q b)
    (hn : W.toNat + a < 2 ^ 32) (hn' : W.toNat + b < 2 ^ 32) : (s.gpr r - s.gpr q == 0) = decide (a = b) := by
  by_cases e : a = b
  · subst e
    have : s.gpr r = s.gpr q := BitVec.eq_of_toNat_eq (ha.trans hb.symm)
    simp [this]
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro hz
    have : s.gpr r = s.gpr q := by
      have := congrArg (· + s.gpr q) hz; simp only [BitVec.sub_add_cancel] at this; exact this.trans (BitVec.zero_add _)
    have := congrArg BitVec.toNat this
    rw [ha, hb, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hn'] at this
    omega_arith

section
variable {s : State} {base : Addr} {bytes len : Nat} {args : Nat → BitVec 32} {c : Ctx} {M : Nat}

theorem tableStep_ok {s₀ : State} {b i : Nat} (hb₀ : sv s₀.mem base len c 5 = b * 2 ^ (8 * bc len c) % M)
    (hi2 : 2 ≤ i) (hi : i < 16) {t : State} (I : TabInv Ex base bytes len args c M b s₀ i t) :
    WP isa (tableStep c) t fun u => TabInv Ex base bytes len args c M b s₀ (i + 1) u ∧
      u.zf = some (decide (i + 1 = 16)) := by
  have C := I.ctx
  have h := C.inp
  have nw' := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  have bl := h.bytes_lt
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain e14 : lo len (.slot c 1) + st len c ≤ lo len (.slot c 4) := sl_le c (by decide)
  obtain e45 : lo len (.slot c 4) + st len c ≤ lo len (.slot c 5) := sl_le c (by decide)
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain tsucc : ∀ j, te len c (j + 1) = te len c j + bc len c := fun j => by simp only [te]; rw [Nat.succ_mul]; omega_arith
  obtain ti16 : te len c (i + 1) ≤ te len c 16 := by
    have := Nat.mul_le_mul_right (bc len c) (show i + 1 ≤ 16 by omega_arith); simp only [te]; omega_arith
  obtain ti0 : te len c 0 ≤ te len c i := by simp only [te]; omega_arith
  obtain ti1 := tsucc i
  obtain t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega_arith
  have hM := C.gt
  obtain sp₀ : t.gpr .esp = s₀.gpr .esp := I.keeps.1 _ (by decide)
  obtain fit := tabR_fit h c
  obtain room₀ : CallRoom (s₀.gpr .esp) base bytes := sp₀ ▸ h.room
  -- The base keeps its value.
  obtain B : sv t.mem base len c 5 = b * 2 ^ (8 * bc len c) % M := by
    simp only [sv]
    rw [tabR_slot5 h I.frame room₀]
    exact hb₀
  unfold tableStep
  -- Slot 7 times the base.
  refine WP.seq (WP.mono (cmul_ok C (o := 7) (a := 7) (b := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [B]; exact Nat.mod_lt _ (by omega_arith))) fun u₁ ⟨C₁, cs₁, F₁, L₁, V₁⟩ => ?_)
  obtain P₁ : sv u₁.mem base len c 7 = b ^ i * 2 ^ (8 * bc len c) % M := by
    obtain v := VG.Proof.Dsa.mont_product C.coprime (a := b ^ (i - 1)) (b := b)
      (by rw [I.last, Nat.mod_mod]) (by rw [B, Nat.mod_mod]) V₁
    rw [Nat.mod_eq_of_lt L₁] at v
    rw [v, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega_arith : 1 ≤ i)]
  have h₁ := C₁.inp
  obtain esi₁ : u₁.gpr .esi = t.gpr .esi := cs₁.1 _ (by decide)
  -- The pointers of the copy into entry `i`.
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine WP.seq (wp_movS rfl fun w₁ a₁ _ => ?_)
  obtain hw₁ := h₁.regs a₁.keeps a₁.mem
  refine ptrTo_ok (r := .ebp) (t := .edx) (x := .slot c 7) (by decide) (by decide) hw₁.edi hw₁.width h.upper'
    (by omega_arith) fun w₂ K₂ m₂ p₂ => wp_movS rfl fun w₃ a₃ _ => ?_
  obtain hw₃ := hw₁.regs ((K₂.mono (by decide)).trans (a₃.keeps.mono (by decide)) : Keeps [.ebx, .edx, .ebp] w₁ w₃)
    (by rw [a₃.mem, m₂])
  rw [← List.append_nil (cntTo (one c) .edi)]
  refine cntTo_ok (r := .edi) (n := one c) hw₃.width h.upper' (one_ok c).extra fun w₄ K₄ m₄ c₄ => WP.block_nil ?_
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain Kw : Keeps [.ebx, .ecx, .edx, .ebp, .edi] u₁ w₄ :=
    (((a₁.keeps.mono (by decide)).trans (K₂.mono (by decide))).trans (a₃.keeps.mono (by decide))).trans
      (K₄.mono (by decide))
  obtain mw : w₄.mem = u₁.mem := by rw [m₄, a₃.mem, m₂, a₁.mem]
  obtain pe : PtrAt w₄ base .ebp (lo len (.slot c 7)) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.other _ (by decide)]; exact p₂
  obtain pb : PtrAt w₄ base .ebx (te len c i) := by
    rw [PtrAt, K₄.1 _ (by decide), a₃.gpr, K₂.1 _ (by decide), a₁.other _ (by decide), esi₁]; exact I.ptr
  obtain ce : (w₄.gpr .edi).toNat = 4 * cwc len c := by rw [cnt_toNat h.upper' (one_ok c) c₄, cw1]
  obtain ck : w₄.gpr .ecx = cmask true := by
    rw [K₄.1 _ (by decide), a₃.other _ (by decide), K₂.1 _ (by decide), a₁.gpr]; rfl
  -- The copy.
  refine WP.seq (WP.mono (selectTail_ok h₁ (Kw.mono (by decide)) mw (x := lo len (.slot c 7)) (d := te len c i)
    (N := cwc len c) (k := true) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) pe pb ce ck)
    fun u₂ ⟨O₂, V₂, pb₂, K₂'⟩ => ?_)
  obtain h₂ := h₁.keep (K₂'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₁ u₂) (by decide) (by decide)
    (by rw [← mw]; exact O₂.mono (Nat.zero_le _) (by omega_arith))
  -- `esi` past entry `i`, and the comparison with the table's end.
  refine wp_movS rfl fun v₁ b₁ _ => ?_
  obtain hv₁ := h₂.regs b₁.keeps b₁.mem
  refine entryPtr_ok (c := c) (j := 16) (r := .edx) (t := .eax) (by decide) (by decide) (by decide) (by decide)
    hv₁.edi hv₁.width h.upper' (by decide) fun v₂ K₅ m₅ p₅ => wp_cmpS rfl fun v₃ f₃ z₃ => WP.block_nil ?_
  obtain esi₂ : PtrAt v₂ base .esi (te len c (i + 1)) := by
    rw [PtrAt, K₅.1 _ (by decide), b₁.gpr, tsucc, bw]; exact pb₂
  obtain esi₃ : PtrAt v₃ base .esi (te len c (i + 1)) := by rw [PtrAt, f₃.gpr]; exact esi₂
  obtain Kall : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] t v₃ :=
    ((((cs₁.mono (by decide)).trans (K₂'.mono (by decide))).trans (b₁.keeps.mono (by decide))).trans
      (K₅.mono (by decide))).trans (f₃.keeps _)
  obtain m₃ : v₃.mem = u₂.mem := by rw [f₃.mem, m₅, b₁.mem]
  obtain O₂' : Outside base (te len c 0) (16 * bc len c) u₁.mem u₂.mem := by
    rw [← mw]; exact O₂.mono (by omega_arith) (by omega_arith)
  obtain F₂ : Frame (frameR base (s₀.gpr .esp) (tabR len c)) u₁.mem v₃.mem := by
    rw [m₃]; exact frameR_of_outside O₂' (by omega_arith) (by simp)
  obtain F₁' : Frame (frameR base (s₀.gpr .esp) (tabR len c)) t.mem u₁.mem := by
    rw [← sp₀]; exact frameR_mono F₁ (by simp)
  obtain C₃ : CtxOk Ex base bytes len args c M v₃ := by
    obtain C₂ := C₁.keepF (K₂'.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₁ u₂) (by decide)
      (by decide) (ws := [(te len c 0, 16 * bc len c)]) (frameR_of_outside O₂' (by omega_arith) (by simp))
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only; omega_arith)
      (by intro p hp; simp only [List.mem_singleton] at hp; subst hp; dsimp only
          obtain z0 : lo len (.slot c 0) = numBase := sl_zero len c
          obtain e01 : lo len (.slot c 0) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
          omega_arith)
    exact C₂.regs ((b₁.keeps.mono (by decide) : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] u₂ v₁).trans
      ((K₅.mono (by decide)).trans (f₃.keeps _))) (by rw [f₃.mem, m₅, b₁.mem])
  -- Values.
  obtain keepU : ∀ d, d + 4 * cwc len c ≤ bytes → (d + 4 * cwc len c ≤ te len c i ∨ te len c i + bc len c ≤ d) →
      val32 v₃.mem base d (cwc len c) = val32 u₁.mem base d (cwc len c) := fun d hd hdi => by
    rw [m₃, ← mw]; exact O₂.val32 (by omega_arith) (by omega_arith)
  refine ⟨⟨C₃, I.keeps.trans Kall, I.frame.trans (F₁'.trans F₂), fun j hj => ?_, ?_, esi₃⟩, ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [m₃, V₂]; simp only [↓reduceIte, mw]; exact P₁
    · have hj' : j < i := by omega_arith
      obtain tj : te len c j + bc len c ≤ te len c i := by
        have := Nat.mul_le_mul_right (bc len c) (show j + 1 ≤ i by omega_arith); simp only [te]; rw [Nat.succ_mul] at this; omega_arith
      obtain tj0 : te len c 0 ≤ te len c j := by simp only [te]; omega_arith
      rw [keepU (te len c j) (by omega_arith) (.inl (by omega_arith))]
      rw [mulR7_te h F₁ h.room (by omega_arith)]
      exact I.table j hj'
  · simp only [sv]
    rw [keepU (lo len (.slot c 7)) (by omega_arith) (.inl (by omega_arith)), Nat.add_sub_cancel]
    exact P₁
  · rw [z₃, ptr_beq esi₂ p₅ (by omega_arith) (by omega_arith)]
    congr 1
    apply decide_eq_decide.mpr
    constructor
    · intro e
      obtain e' : (i + 1) * bc len c = 16 * bc len c := by simp only [te] at e; omega_arith
      exact Nat.eq_of_mul_eq_mul_right (by omega_arith) e'
    · intro e; rw [e]

/-- The table: entry `j` holds `b^j R mod M`, from one and the base in Montgomery form. -/
theorem buildTable_ok {b : Nat} (C : CtxOk Ex base bytes len args c M s)
    (h6 : sv s.mem base len c 6 = 2 ^ (8 * bc len c) % M) (h5 : sv s.mem base len c 5 = b * 2 ^ (8 * bc len c) % M) :
    WP isa (buildTable c) s fun u => TabInv Ex base bytes len args c M b s 16 u := by
  have h := C.inp
  have nw := h.scratch.nowrap
  obtain f8 := h.slot_fit c (j := 8) (by decide)
  obtain T := h.table_fit c
  obtain bw := bc_eq_cwc len c
  obtain g := bc_ge h.lower' c
  have est : st len c = 2 * bc len c + 32 := rfl
  obtain e57 : lo len (.slot c 5) + st len c ≤ lo len (.slot c 7) := sl_le c (by decide)
  obtain e78 : lo len (.slot c 7) + st len c ≤ lo len (.slot c 8) := sl_le c (by decide)
  obtain t0 : te len c 0 = lo len (.slot .wide 20) := by simp [te]
  obtain t1 : te len c 1 = te len c 0 + bc len c := by simp [te]
  obtain t16 : te len c 16 = te len c 0 + 16 * bc len c := by simp only [te]; omega_arith
  obtain cb1 : cb len (one c) = bc len c := by simp [cb, one]
  obtain cw1 : cw len (one c) = cwc len c := by simp [cw, cwc, cb, one]
  obtain fit := tabR_fit h c
  unfold buildTable
  refine copyEntry_ok (c := c) h (x := 6) (j := 0) (by decide) (by decide) fun u₁ O₁ V₁ K₁ => ?_
  obtain h₁ := h.keep K₁ (by decide) (by decide) (O₁.mono (Nat.zero_le _) (by omega_arith))
  refine copyEntry_ok (c := c) h₁ (x := 5) (j := 1) (by decide) (by decide) fun u₂ O₂ V₂ K₂ => ?_
  obtain h₂ := h₁.keep K₂ (by decide) (by decide) (O₂.mono (Nat.zero_le _) (by omega_arith))
  refine WP.seq (WP.mono (copy_ok h₂ (x := .slot c 5) (d := .slot c 7) (one_ok c) (by rw [cb1]; omega_arith)
    (by rw [cb1]; omega_arith) (by rw [cb1]; exact .inr (by omega_arith))) fun u₃ ⟨O₃, V₃, K₃⟩ => ?_)
  obtain h₃ := h₂.keep K₃ (by decide) (by decide) (O₃.mono (Nat.zero_le _) (by rw [cb1]; omega_arith))
  rw [← List.append_nil (entryPtr c .esi 2 .edx)]
  refine WP.seq (entryPtr_ok (c := c) (j := 2) (r := .esi) (t := .edx) (by decide) (by decide) (by decide)
    (by decide) h₃.edi h₃.width h.upper' (by decide) fun w K₄ m₄ p₄ => WP.block_nil ?_)
  rw [cb1] at O₃
  rw [cw1] at V₃
  -- The state after the setup.
  obtain F₁ : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem u₁.mem :=
    frameR_of_outside (O₁.mono (o' := te len c 0) (n' := 16 * bc len c) (Nat.le_refl _) (by omega_arith)) (by omega_arith) (by simp)
  obtain F₂ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₁.mem u₂.mem :=
    frameR_of_outside (O₂.mono (o' := te len c 0) (n' := 16 * bc len c) (by omega_arith) (by omega_arith)) (by omega_arith) (by simp)
  obtain F₃ : Frame (frameR base (s.gpr .esp) (tabR len c)) u₂.mem w.mem := by
    rw [m₄]; exact frameR_of_outside O₃ (by omega_arith) (by simp)
  obtain F : Frame (frameR base (s.gpr .esp) (tabR len c)) s.mem w.mem := F₁.trans (F₂.trans F₃)
  obtain K : Keeps [.eax, .ebx, .ecx, .edx, .ebp, .esi] s w :=
    (((K₁.trans K₂).trans K₃).mono (by decide)).trans (K₄.mono (by decide))
  obtain S5 : sv u₂.mem base len c 5 = sv s.mem base len c 5 := tabR_slot5 h (F₁.trans F₂) h.room
  obtain I₂ : TabInv Ex base bytes len args c M b s 2 w := by
    refine ⟨C.keepF K (by decide) (by decide) F fit (tabR_past h c), K, F, fun j hj => ?_, ?_, p₄⟩
    · rw [m₄]
      rcases (show j = 0 ∨ j = 1 by omega_arith) with rfl | rfl
      · rw [O₃.val32 (.inr (by omega_arith)) (by omega_arith), O₂.val32 (.inl (by omega_arith)) (by omega_arith), V₁, h6]; simp
      · rw [O₃.val32 (.inr (by omega_arith)) (by omega_arith), V₂]
        simp only [sv] at h5 ⊢; rw [O₁.val32 (.inl (by omega_arith)) (by omega_arith), h5]; simp
    · simp only [sv]; rw [m₄, V₃]; simp only [sv] at S5 h5; rw [S5, h5]; simp
  -- The loop.
  refine PublicRt.countLoop (N := 14) (by decide) (fun j t => TabInv Ex base bytes len args c M b s (j + 2) t)
    (fun j t hj I => WP.mono (tableStep_ok h5 (by omega_arith) (by omega_arith) I) fun u ⟨I', z⟩ => ⟨I', ?_⟩) I₂
  rw [z]; congr 1

end

end VG.Proof.Bignum.X86.CrtRt
