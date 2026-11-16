module
public import VerifiedGarbage.Impl.Dsa.Arm.Stream
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
public import VerifiedGarbage.Spec.Dsa
public import VerifiedGarbage.Spec.Rsa.Contract
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Csub
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Dsa.Arm.Checks
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.StreamBytes
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Weierstrass.Words
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.AddrArith

/-! ### `Dsa.Arm.Doubling`, which only this module used -/

section

/-! # Counted modular doubling on ARMv7

The public counter stays in registers: `r1` across digit addition, then `r0`
across conditional subtraction. The arithmetic and memory bounds are those
of the existing addition and subtraction kernels.
-/

@[expose] public section
namespace VG.Proof.Dsa.Arm
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw wp_subs op2_reg op2_imm)

theorem countedDouble_parts_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Ws t base size ∧
      val32 t.mem base (resS n) (2 * n) =
        (val32 s.mem base (resS n) (2 * n) + val32 s.mem base (resS n) (2 * n)) % m ∧
      Outs base [(resS n, 8 * n), (tmpS n, 8 * n), (accS n, 4 * (8 * n + 2))] s.mem t.mem ∧
      Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 := by
  let M := contextMod n
  let acc := accS n
  let o := resS n
  let a := resS n
  let b := resS n
  have hs := h.ws
  have hn : 0 < M.n := h.n0
  obtain hL : MulLayD M size invO acc o a b :=
    context_lay h.size_le h.small (by decide) (by decide) (by decide)
  have hm : val32 s.mem base M.mo (words M) = m := h.modulus
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  have hA : val32 s.mem base a (words M) < m := hv
  have hB : val32 s.mem base b (words M) < m := hv
  suffices H : WP isa (countedDouble n) s fun t => Ws t base size ∧
    val32 t.mem base o (words M) = (val32 s.mem base a (words M) + val32 s.mem base b (words M)) % m ∧
    Outs base [(o, 4 * words M), (M.tmp, 4 * words M), (acc, 4 * (4 * words M + 2))] s.mem t.mem ∧
    Rest dclob s t ∧ t.gpr .r0 = s.gpr .r1 by
    simpa only [M, o, a, b, acc, contextMod, Impl.Mont.Arm.words,
      show 4 * (2 * n) = 8 * n by omega_arith,
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega_arith] using H
  have hnw := hs.nowrap
  obtain ⟨W, hW⟩ : ∃ W, words M = W := ⟨_, rfl⟩
  obtain hD : digits M = 2 * W := by rw [← hW]; simp only [digits, Impl.Mont.Arm.words]; omega_arith
  obtain ⟨acc_le, a_le, b_le, mo_le, tmp_le, o_le, inv_le, acc16, a16, b16, mo16, tmp16, o16, inv16, sa, sb, smo,
    sinv, stmp, so, tmo, ot⟩ := hL
  simp only [accLen, hD, hW] at acc_le a_le b_le mo_le tmp_le o_le acc16 a16 b16 mo16 tmp16 sa sb smo sinv stmp so tmo ot
  rw [hW] at hm hA hB ⊢
  unfold countedDouble
  refine WP.seq (WP.mono (VG.Arm.WP.gpr (addDigits_ok hs (M := M) (acc := acc) (a := a) (b := b) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact a_le) (by rw [hW]; exact b_le)
    (by rw [hD]; omega_using [acc16]) (by rw [hW]; exact a16) (by omega_using [b16])
    (by rw [hD, hW]; omega_using [sa]) (by rw [hD, hW]; omega_using [sb])) (r := .r1) (by
      simp [instrs, addDigits, ptrLoop, ptr, addDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t₀ ⟨⟨w₀, V₀, D₀, O₀, R₀⟩, C₀⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun t₁ U => WP.block_nil ?_)
  obtain w₁ := w₀.of_upd U (by decide)
  have V₁ := V₀
  have D₁ := D₀
  have O₁ := O₀
  rw [← U.mem] at V₁ D₁ O₁
  obtain R₁ := R₀.trans (U.rest (by decide : .r0 ∈ dclob))
  obtain C₁ : t₁.gpr .r0 = s.gpr .r1 := by rw [U.gpr, C₀]
  simp only [hD, hW] at V₁ D₁ O₁
  obtain hm₁ : val32 t₁.mem base M.mo W = m := by
    rw [O₁.val32 (by omega_using [smo]) (by omega_using [mo_le, hnw])]; exact hm
  refine WP.mono (VG.Arm.WP.gpr (csubD_ok w₁ (M := M) (src := acc) (o := o) (m := m) hn
    (by rw [hD]; omega_using [acc_le]) (by rw [hW]; exact o_le) (by rw [hW]; exact tmp_le) (by rw [hW]; exact mo_le)
    (by rw [hD]; omega_using [acc16]) o16 (by rw [hW]; exact tmp16) (by rw [hW]; exact mo16)
    (by rw [hD, hW]; omega_using [stmp]) (by rw [hW]; exact tmo) (by rw [hD, hW]; omega_using [so])
    (by rw [hW]; exact ot) (by rw [hW]; exact hm₁) hm0 (by rw [hD]; exact D₁) (by rw [hD, V₁]; omega_using [hA, hB])) (r := .r0) (by
      simp [instrs, csubD, ptrLoop, ptr, diffDigitD, half, bump, mask16] <;> (repeat' apply And.intro) <;> exact of_decide_eq_true rfl))
    fun t ⟨⟨wt, V, O, R⟩, C⟩ => ⟨wt, ?_, ?_, R₁.trans R, C.trans C₁⟩
  · rw [hW] at V; rw [V, hD, V₁]
  · rw [hW] at O
    exact (Outs.of_outside (O₁.mono (o' := acc) (n' := 4 * (4 * W + 2)) (Nat.le_refl _) (by omega_using [])) (by simp)).trans (O.mono (by simp))

/-- One doubling keeps the context and carries the counter into `r0`. -/
theorem countedDouble_ok {n size m : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m) :
    WP isa (countedDouble n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 * val32 s.mem base (slot n 9) (2 * n) % m ∧
      t.gpr .r0 = s.gpr .r1 := by
  refine WP.mono (countedDouble_parts_ok h hv) fun t ⟨w, V, O, R, C⟩ => ?_
  obtain K : OpKeep n base 9 s t := ⟨R, O⟩
  exact ⟨h.keep (by decide) w K, K, by simpa only [resS, Nat.two_mul] using V, C⟩

structure DoubleInv (n m size k : Nat) (base : Addr) (s : State) (j : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 9) (2 * n) = 2 ^ j * val32 s.mem base (slot n 9) (2 * n) % m
  keep : OpKeep n base 9 s u
  count : u.gpr .r0 = BitVec.ofNat 32 (k - j)

theorem doubles_ok {n size m : Nat} {base : Addr} (k : Nat) {s : State}
    (h : Context n m base size s) (hv : val32 s.mem base (slot n 9) (2 * n) < m)
    (hk : k < 2 ^ 16) :
    WP isa (doubles n k) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) = 2 ^ k * val32 s.mem base (slot n 9) (2 * n) % m := by
  unfold doubles
  split
  · rename_i hz
    subst k
    exact WP.block_nil ⟨h, ⟨Rest.refl _ _, Outs.refl _ _ _⟩,
      by rw [Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv]⟩
  · rename_i hk0
    refine WP.seq (wp_movw fun t U => WP.block_nil ?_)
    obtain c : Context n m base size t := ⟨h.ws.of_upd U (by decide), h.size_le, h.small, h.n0,
      by rw [U.mem]; exact h.modulus, h.gt_one, by rw [U.mem]; exact h.inverse⟩
    obtain I0 : DoubleInv n m size k base s 0 t := ⟨c,
      by rw [U.mem, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hv],
      ⟨U.rest (by decide), by rw [U.mem]; exact Outs.refl _ _ _⟩,
      by rw [U.gpr, Nat.sub_zero, movw_ofNat hk]⟩
    refine WP.loop (M := isa) (fun r u => ∃ j, r = k - j ∧ j < k ∧ DoubleInv n m size k base s j u)
      ?_ k t ⟨0, rfl, by omega_arith, I0⟩
    rintro r u ⟨j, rfl, hj, I⟩
    refine WP.seq (wp_mov (op2_reg _ _) fun u₀ U₀ => WP.block_nil ?_)
    obtain c₀ : Context n m base size u₀ := ⟨I.ctx.ws.of_upd U₀ (by decide), I.ctx.size_le,
      I.ctx.small, I.ctx.n0, by rw [U₀.mem]; exact I.ctx.modulus, I.ctx.gt_one,
      by rw [U₀.mem]; exact I.ctx.inverse⟩
    obtain hm : 0 < m := by have := I.ctx.gt_one; omega_arith
    refine WP.seq (WP.mono (countedDouble_ok c₀ (by rw [U₀.mem, I.val]; exact Nat.mod_lt _ hm))
      fun u₁ ⟨c₁, K₁, V₁, C₁⟩ => ?_)
    refine wp_subs (op2_imm (by decide)) fun u₂ U₂ Z₂ => WP.block_nil ?_
    obtain I' : DoubleInv n m size k base s (j + 1) u₂ := by
      refine ⟨⟨c₁.ws.of_upd U₂ (by decide), c₁.size_le, c₁.small, c₁.n0,
        by rw [U₂.mem]; exact c₁.modulus, c₁.gt_one, by rw [U₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_⟩
      · rw [U₂.mem, V₁, U₀.mem, I.val, Nat.mul_mod_mod, Nat.pow_succ]
        congr 1
        ac_rfl
      · refine ⟨((I.keep.rest.trans (U₀.rest (by decide))).trans K₁.rest).trans (U₂.rest (by decide)), ?_⟩
        rw [U₂.mem]
        exact I.keep.mem.trans (by rw [← U₀.mem]; exact K₁.mem)
      · rw [U₂.gpr, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega_arith) (by omega_arith)]
        congr 1
    obtain hz : u₂.z = decide (j + 1 = k) := by
      rw [Z₂, C₁, U₀.gpr, I.count, ofNat_sub_one (by omega_arith) (by omega_arith),
        VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
      simp only [decide_eq_decide]
      omega_arith
    by_cases hj1 : j + 1 = k
    · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj1]; rfl,
        I'.ctx, I'.keep, by rw [I'.val, hj1]⟩
    · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj1]; rfl,
        k - (j + 1), by omega_arith, j + 1, rfl, by omega_arith, I'⟩

end VG.Proof.Dsa.Arm

end

end


/-!
# DSA on 32-bit ARM: the arithmetic on slots

`reduceStream n` reduces the bytes from `r11` to `lr` modulo the context's
modulus into the result slot (`reduceStream_ok`), a byte at a time
(`streamStep_ok`: eight doublings and the byte's addition); `modulusMinus`
writes `m - amount` (`modulusMinus_ok`), `ordinaryMul` and `ordinaryAdd`
multiply and add ordinary residues (`ordinaryMul_ok`, `ordinaryAdd_ok`).
All of them change only the result and product slots, the temporary slot and
the accumulator (`streamRanges`).
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_ldrb wp_dp wp_cmp op2_imm op2_reg dpVal eval_ne
  eval_eq)

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.trans {n o : Nat} {base : Addr} {s t u : State}
    (h₁ : OpKeep n base o s t) (h₂ : OpKeep n base o t u) : OpKeep n base o s u :=
  ⟨h₁.rest.trans h₂.rest, h₁.mem.trans h₂.mem⟩

/-- The memory the slot arithmetic changes: the result and product slots, the
temporary slot and the accumulator. -/
abbrev streamRanges (n : Nat) : List (Nat × Nat) :=
  [(slot n 9, 8 * n), (slot n 10, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem _root_.VG.Proof.Mont.Arm.Dyn.OpKeep.streamRanges {n o : Nat} {base : Addr} {s t : State}
    (K : OpKeep n base o s t) (ho : o = 9 ∨ o = 10 := by decide) : Outs base (streamRanges n) s.mem t.mem :=
  K.mem.mono fun r hr => by
    simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp

/-- Memory past the context is kept. -/
theorem Outs.outside {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (h : Outs base rs m m') {o n : Nat}
    (hr : ∀ r ∈ rs, o ≤ r.1 ∧ r.1 + r.2 ≤ o + n) : Outside base o n m m' :=
  fun x hx => h x fun r hr' => by have := hr r hr'; omega_arith

theorem streamRanges_inside (n : Nat) : ∀ r ∈ streamRanges n, 0 ≤ r.1 ∧ r.1 + r.2 ≤ 0 + contextBytes n := by
  obtain b9 := slot_bound (n := n) (i := 9) (by decide)
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain b1 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  obtain b6 := slot_bound (n := n) (i := 6) (by decide)
  obtain a := slot_acc n
  simp only [stride] at *
  simp only [streamRanges, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl | rfl) <;> constructor <;> omega_arith

/-! ## Doublings and a byte -/

theorem reduceStep_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hb : val32 s.mem base (slot n 10) (2 * n) < m) :
    WP isa (reduceStep n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + val32 s.mem base (slot n 10) (2 * n)) % m := by
  have m1 := h.gt_one
  obtain nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold reduceStep
  refine WP.seq (WP.mono (doubles_ok 8 h hv (by decide)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  obtain Bu := Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_add_ok cu (o := 9) (a := 9) (b := 10) (by decide) (by decide) (by decide)
    (by rw [Vu]; exact Nat.mod_lt _ (by omega_arith)) (by rw [Bu]; exact hb)) fun t ⟨ct, Kt, Vt⟩ =>
    ⟨ct, Ku.trans Kt, ?_⟩
  rw [Vt, Vu, Bu, Nat.mod_add_mod]

/-- A number below `2³²` with its low word replaced. -/
theorem val32_low_write {m : Mem} {base : Addr} {d k : Nat} (hk : 0 < k) (hn : base.toNat + d + 4 * k ≤ 2 ^ 32)
    (hv : val32 m base d k < 2 ^ 32) (v : BitVec 32) : val32 (m.writeW (off base d) v) base d k = v.toNat := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_arith⟩
  obtain hu : val32 (m.writeW (off base d) v) base (d + 4) j = val32 m base (d + 4) j :=
    val32_congr fun i hi => w32_write_ne (size := d + 4 * (j + 1)) (by omega_arith) (by omega_arith) (by omega_arith) (.inr (by omega_arith)) v
  rw [val32] at hv ⊢
  rw [w32_write_self, hu]
  omega_arith

theorem streamStep_ok {n size m i len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hi : i < len) (hlen : p.toNat + len ≤ 2 ^ 32)
    (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p + BitVec.ofNat 32 i) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hv : val32 s.mem base (slot n 9) (2 * n) < m) (hpad : val32 s.mem base (slot n 10) (2 * n) < 2 ^ 32) :
    WP isa (streamStep n) s fun t =>
      Context n m base size t ∧ t.gpr .r11 = p + BitVec.ofNat 32 (i + 1) ∧ t.gpr .lr = s.gpr .lr ∧
      t.z = decide (i + 1 = len) ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (256 * val32 s.mem base (slot n 9) (2 * n) + (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat) % m ∧
      val32 t.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  simp only [stride] at b10 s9
  unfold streamStep
  obtain ea : State.addr (s.gpr .r11 + BitVec.ofNat 32 0) = State.addr p + BitVec.ofNat 64 i := by
    rw [hc, Offset.add_add, Nat.add_zero, VG.Arm.addr_add (by omega_arith)]
  refine WP.seq (wp_ldrb (by decide) ea hr fun s₁ u₁ => wp_ptr (d := .r10) (by decide) (by simp only [prodS]; omega_arith)
    fun s₂ u₂ => ?_)
  obtain w₂ : Ws s₂ base size := (h.ws.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea (K := prodS n) (d := 0) (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte])
    (by simp only [prodS]; omega_arith)) (w₂.write (d := prodS n + 0) (n := 4) (by simp only [prodS]; omega_arith))
    fun s₃ m₃ => WP.block_nil ?_
  obtain mem₃ : s₃.mem = s.mem.writeW (off base (slot n 10)) (BitVec.setWidth 32 (s.mem (State.addr p + BitVec.ofNat 64 i))) := by
    rw [m₃.mem, u₂.mem, u₁.mem, u₂.other .r4 (by decide), u₁.gpr]; rfl
  obtain O₃ : Outside base (slot n 10) (8 * n) s.mem s₃.mem := by
    rw [mem₃]; exact (writeW32_outside _ _ _ (by omega_arith)).mono (Nat.le_refl _) (by omega_arith)
  obtain w₃ : Ws s₃ base size := w₂.of_mupd m₃
  obtain c₃ : Context n m base size s₃ := h.of_slot w₃ O₃ (by decide)
  obtain byte := (s.mem (State.addr p + BitVec.ofNat 64 i)).isLt
  obtain B₃ : val32 s₃.mem base (slot n 10) (2 * n) = (s.mem (State.addr p + BitVec.ofNat 64 i)).toNat := by
    rw [mem₃, val32_low_write (by omega_arith) (by omega_arith) hpad, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]
  obtain Y₃ : val32 s₃.mem base (slot n 9) (2 * n) = val32 s.mem base (slot n 9) (2 * n) :=
    O₃.val32 (by omega_arith) (by omega_arith)
  obtain R₃ : Rest (.r11 :: dclob) s s₃ :=
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (m₃.rest _)
  refine WP.seq (WP.mono (reduceStep_ok c₃ (by rw [Y₃]; exact hv) (by rw [B₃]; omega_arith)) fun u ⟨cu, Ku, Vu⟩ => ?_)
  refine wp_dp (op2_imm (by decide)) fun t₁ v₁ => wp_cmp (op2_reg _ _) fun t f z => WP.block_nil ?_
  obtain Ru : Rest (.r11 :: dclob) s u := R₃.trans (Ku.rest.mono (by decide))
  obtain r11 : t₁.gpr .r11 = p + BitVec.ofNat 32 (i + 1) := by
    rw [v₁.gpr, dpVal, Ku.rest.gpr .r11 (by decide), m₃.gpr, u₂.other .r11 (by decide),
      u₁.other .r11 (by decide), hc]
    show p + BitVec.ofNat 32 i + BitVec.ofNat 32 1 = _
    rw [Offset.add_add]
  obtain lr : t₁.gpr .lr = s.gpr .lr := by rw [v₁.other .lr (by decide)]; exact Ru.gpr .lr (by decide)
  obtain mt : t.mem = u.mem := by rw [f.mem, v₁.mem]
  refine ⟨⟨?_, c₃.size_le, c₃.small, c₃.n0, ?_, c₃.gt_one, ?_⟩, by rw [f.gpr]; exact r11, by rw [f.gpr]; exact lr,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact (cu.ws.of_upd v₁ (by decide)).of_fupd f
  · rw [mt]; exact cu.modulus
  · rw [mt]; exact cu.inverse
  · rw [z, r11, lr, he, sub_add_add, cmp_ofNat (by omega_arith) (by omega_arith)]
  · rw [mt, Vu, Y₃, B₃]
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
    rw [mt, Ku.val32 (i := 10) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', B₃]
    omega_arith
  · rw [mt]
    exact (Outs.of_outside O₃ (by simp)).trans Ku.streamRanges
  · exact (Ru.trans (v₁.rest (by decide))).trans (f.rest _)

/-! ## The stream -/

/-- The bytes from `r11 = p` to `lr = p + len`, reduced modulo `m` into the
result slot. -/
theorem reduceStream_ok {n size m len : Nat} {base : Addr} {s : State} {p : BitVec 32}
    (h : Context n m base size s) (hm : 255 < m) (hlen : p.toNat + len ≤ 2 ^ 32) (hl : len < 2 ^ 32)
    (hc : s.gpr .r11 = p) (he : s.gpr .lr = p + BitVec.ofNat 32 len)
    (hr : ∀ i < len, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hd : Region.Disjoint ⟨State.addr p, len⟩ ⟨off base 0, contextBytes n⟩) :
    WP isa (reduceStream n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) len) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  obtain b9 := slot_bound (n := n) (i := 9) (by decide)
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  obtain m0 : 0 < m := by omega_arith
  simp only [stride] at b9 b10 s9
  obtain e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold reduceStream
  refine WP.seq (WP.mono (zeros_ok h.ws (k := 2 * n) (o := resS n) (by omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS]; omega_arith)) fun u₁ ⟨w₁, Z₁, O₁, R₁⟩ => ?_)
  rw [e8] at O₁
  obtain c₁ := h.of_slot w₁ O₁ (by decide)
  refine WP.seq (WP.mono (zeros_ok w₁ (k := 2 * n) (o := prodS n) (by omega_arith) (by simp only [prodS]; omega_arith)
    (by simp only [prodS]; omega_arith)) fun u₂ ⟨w₂, Z₂, O₂, R₂⟩ => ?_)
  rw [e8] at O₂
  obtain c₂ := c₁.of_slot w₂ O₂ (by decide)
  obtain Y₂ : val32 u₂.mem base (slot n 9) (2 * n) = 0 := by
    rw [O₂.val32 (by simp only [prodS]; omega_arith) (by omega_arith)]; exact val32_zeros Z₁
  obtain P₂ : val32 u₂.mem base (slot n 10) (2 * n) = 0 := val32_zeros Z₂
  obtain K₂ : Outs base (streamRanges n) s.mem u₂.mem :=
    (Outs.of_outside O₁ (by simp [resS])).trans (Outs.of_outside O₂ (by simp [prodS]))
  obtain R₂' : Rest (.r11 :: dclob) s u₂ := (R₁.mono (by decide)).trans (R₂.mono (by decide))
  obtain r11 : u₂.gpr .r11 = p := by rw [R₂.gpr .r11 (by decide), R₁.gpr .r11 (by decide), hc]
  obtain lr : u₂.gpr .lr = p + BitVec.ofNat 32 len := by rw [R₂.gpr .lr (by decide), R₁.gpr .lr (by decide), he]
  refine WP.seq (wp_cmp (op2_reg _ _) fun u₃ f₃ z₃ => WP.block_nil ?_)
  obtain c₃ : Context n m base size u₃ := ⟨c₂.ws.of_fupd f₃, c₂.size_le, c₂.small, c₂.n0, by rw [f₃.mem]; exact c₂.modulus,
    c₂.gt_one, by rw [f₃.mem]; exact c₂.inverse⟩
  obtain R₃ : Rest (.r11 :: dclob) s u₃ := R₂'.trans (f₃.rest _)
  obtain K₃ : Outs base (streamRanges n) s.mem u₃.mem := by rw [f₃.mem]; exact K₂
  obtain p0 : p = p + BitVec.ofNat 32 0 := (BitVec.add_zero p).symm
  obtain d0 := sub_add_add p 0 len
  rw [BitVec.add_zero] at d0
  rw [r11, lr, d0, cmp_ofNat (by omega_arith) (by omega_arith)] at z₃
  obtain dec0 : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) 0) % m = 0 := by
    simp only [Spec.Rsa.bytesAt, List.range_zero, List.map_nil, Spec.Dsa.decodeBE, List.foldl_nil, Nat.zero_mod]
  refine WP.ite (decide (0 = len)) (by rw [eval_eq, z₃]) (fun hz => WP.block_nil ⟨c₃, ?_, K₃, R₃⟩) fun hz => ?_
  · have hz : len = 0 := (of_decide_eq_true hz).symm
    rw [f₃.mem, Y₂, hz, dec0]
  obtain hpos : 0 < len := by have := of_decide_eq_false hz; omega_arith
  obtain inside := streamRanges_inside n
  refine WP.loop (M := isa) (fun k (u : State) => ∃ i, k = len - i ∧ i < len ∧ Context n m base size u ∧
      u.gpr .r11 = p + BitVec.ofNat 32 i ∧ u.gpr .lr = p + BitVec.ofNat 32 len ∧
      val32 u.mem base (slot n 9) (2 * n) = Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) i) % m ∧
      val32 u.mem base (slot n 10) (2 * n) < 2 ^ 32 ∧ Outs base (streamRanges n) s.mem u.mem ∧
      Rest (.r11 :: dclob) s u) ?_ len u₃
    ⟨0, by omega_arith, hpos, c₃, by rw [f₃.gpr, r11]; exact p0, by rw [f₃.gpr, lr], by rw [f₃.mem, Y₂, dec0],
      by rw [f₃.mem, P₂]; decide, K₃, R₃⟩
  rintro k u ⟨i, rfl, hi, cu, r11u, lru, Vu, Pu, Ou, Ru⟩
  refine WP.mono (streamStep_ok cu hm hi hlen hl r11u lru (by rw [Ru.rd, Ru.wr]; exact hr i hi)
    (by rw [Vu]; exact Nat.mod_lt _ m0) Pu) fun t ⟨ct, r11t, lrt, zt, Vt, Pt, Ot, Rt⟩ => ?_
  obtain byte : u.mem (State.addr p + BitVec.ofNat 64 i) = s.mem (State.addr p + BitVec.ofNat 64 i) :=
    VG.Proof.Weierstrass.keep_of_disjoint (Outs.outside Ou inside) hd (by omega_arith) hi (by omega_arith)
  obtain Vt' : val32 t.mem base (slot n 9) (2 * n) =
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (State.addr p) (i + 1)) % m := by
    rw [Vt, Vu, byte, VG.Proof.Dsa.reduce_prefix_succ]
  by_cases hl : i + 1 = len
  · exact .inl ⟨by rw [eval_ne, zt]; simp [hl], ct, by rw [Vt', hl], Ou.trans Ot, Ru.trans Rt⟩
  · exact .inr ⟨by rw [eval_ne, zt]; simp [hl], len - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, ct, r11t,
      by rw [lrt, lru], Vt', Pt, Ou.trans Ot, Ru.trans Rt⟩

/-! ## Slot arithmetic -/

/-- `[resS] = m - amount`. -/
theorem modulusMinus_ok {n size m amount : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : amount ≤ m) (hn4 : 8 * n ≤ 4096) :
    WP isa (modulusMinus n amount) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = m - amount ∧ Outs base (streamRanges n) s.mem t.mem ∧
      Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain s09 := slot_le (n := n) (i := 0) (j := 9) (by decide)
  obtain s9 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have n0 := h.n0
  obtain hm : m < 2 ^ (32 * (2 * n)) := by rw [← h.modulus]; exact val32_lt _ _ _ _
  simp only [stride] at b10 s09 s9
  obtain e8 : 4 * (2 * n) = 8 * n := by omega_arith
  unfold modulusMinus
  refine WP.seq (WP.mono (setConst_ok h.ws (k := 2 * n) (o := prodS n) (x := amount) (by omega_arith)
    (by simp only [prodS]; omega_arith) (by simp only [prodS]; omega_arith) (by omega_arith)) fun u ⟨Vu, Ru, Ou⟩ => ?_)
  rw [e8] at Ou
  obtain cu := h.of_slot (h.ws.of_rest Ru (by decide)) Ou (by decide)
  refine WP.mono (subWords_ok cu.ws (k := 2 * n) (o := resS n) (a := modS n) (b := prodS n) (by omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [modS]; omega_arith) (by simp only [prodS]; omega_arith) (by simp only [resS]; omega_arith)
    (by simp only [resS, modS]; omega_arith) (by simp only [resS, prodS]; omega_arith)) fun t ⟨Vt, Rt, Ot⟩ => ⟨?_, ?_, ?_, Ru.trans Rt⟩
  · rw [e8] at Ot; exact cu.of_slot (cu.ws.of_rest Rt (by decide)) Ot (by decide)
  · show val32 t.mem base (resS n) (2 * n) = _
    obtain Vu' : val32 u.mem base (slot n 10) (2 * n) = amount := by rw [Nat.mod_eq_of_lt (by omega_arith)] at Vu; exact Vu
    rw [Vt, show modS n = slot n 0 from rfl, cu.modulus, show prodS n = slot n 10 from rfl, Vu', show m + 2 ^ (32 * (2 * n)) - amount = (m - amount) + 2 ^ (32 * (2 * n)) by omega_arith,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_arith)]
  · rw [e8] at Ot; exact (Outs.of_outside Ou (by simp [prodS])).trans (Outs.of_outside Ot (by simp [resS]))

/-- `[resS] = [expS] [baseS] mod m`, from `R² mod m` in slot 7. -/
theorem ordinaryMul_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (ordinaryMul n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 11) (2 * n) * val32 s.mem base (slot n 8) (2 * n) % m ∧
      Outs base (streamRanges n) s.mem t.mem ∧ Rest dclob s t := by
  obtain nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold ordinaryMul
  refine WP.seq (WP.mono (context_mul_ok h (o := 10) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [hr2]; exact Nat.mod_lt _ (by have := h.gt_one; omega_arith))) fun u ⟨cu, Ku, ltu, Vu⟩ => ?_)
  obtain Pu : val32 u.mem base (slot n 10) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime ltu (by rw [Vu, hr2])
  obtain Eu := Ku.val32 (i := 11) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw
  refine WP.mono (context_mul_ok cu (o := 9) (a := 11) (b := 10) (by decide) (by decide) (by decide) ltu)
    fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, Ku.streamRanges.trans Kt.streamRanges, Ku.rest.trans Kt.rest⟩
  rw [Pu, Eu] at Vt
  rw [← Nat.mod_eq_of_lt ltt, ← Eu]
  rw [Eu]
  exact VG.Proof.Dsa.mont_scale h.coprime Vt

/-- `[resS] = [baseS] + [expS] mod m`. -/
theorem ordinaryAdd_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ha : val32 s.mem base (slot n 8) (2 * n) < m) (hb : val32 s.mem base (slot n 11) (2 * n) < m) :
    WP isa (ordinaryAdd n) s fun t => Context n m base size t ∧ OpKeep n base 9 s t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (val32 s.mem base (slot n 8) (2 * n) + val32 s.mem base (slot n 11) (2 * n)) % m :=
  context_add_ok h (o := 9) (a := 8) (b := 11) (by decide) (by decide) (by decide) ha hb

end VG.Proof.Dsa.Arm
