module

public import VerifiedGarbage.Proof.Dsa.Arm.RegisterSave
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Dsa.SameTrace
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Dsa.Arm.ContextBody
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ContextInit
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Zeros
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo

/-! ### `Mont.Arm.Dyn.Exponent`, which this module and modules that import it used -/

section

/-! ### `Mont.Arm.Dyn.ExponentProduct`, which only this module used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the conditional product

`exponentProduct n` multiplies the result by the base where the exponent's
low bit is set (`exponentProduct_ok`): the product is always computed, and
selected under the bit's mask.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_ldr)

variable {umaal : Bool}

/-- A context, after code that changed only header bytes past `m'` and
registers outside `dclob`'s complement. -/
theorem Context.of_outside {n size m d len : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (w : Ws t base size) (O : Outside base d len s.mem t.mem) (hd : 4 ≤ d) (hl : d + len ≤ 256) :
    Context n m base size t := by
  obtain h0 := slot_header n 0
  have nw := h.ws.nowrap
  obtain b0 := slot_bound (n := n) (i := 0) (by decide)
  have sz := h.size_le
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [O.val32 (by omega_using [hl, h0]) (by simp only [stride] at b0; omega_using [nw, b0, sz])]; exact h.modulus
  · rw [O.w32 (by simp only [invO]; omega_using [hd]) (by decide)]; exact h.inverse

/-- The memory the conditional product changes. -/
def productRanges (n : Nat) : List (Nat × Nat) :=
  [(maskO, 4), (slot n 10, 8 * n), (slot n 9, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

theorem exponentProduct_ok {n size m y b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentProduct umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if w32 s.mem base (slot n 11) % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      Outs base (productRanges n) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have hn := h.n0
  obtain hm0 : 0 < m := by have := h.gt_one; omega_using [this]
  obtain b11 := slot_bound (n := n) (i := 11) (by decide)
  obtain h0 := slot_header n 0
  obtain h11 := slot_header n 11
  obtain h8 : 8 ≤ size := by omega_using [sz, b11, h11]
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_using [sz, nw]
  unfold exponentProduct
  refine WP.seq (WP.mono (exponentMask_ok h.ws (n := n) (by simp only [expS, stride] at *; omega_using [sz, b11])
    (by simp only [expS, stride] at *; omega_using [sm, b11]) (by omega_using [h8])) fun s₁ ⟨w₁, M₁, O₁, R₁⟩ => ?_)
  obtain c₁ := h.of_outside w₁ O₁ (by decide) (by decide)
  have keep₁ (i : Nat) (hi : i < 12) : val32 s₁.mem base (slot n i) (2 * n) = val32 s.mem base (slot n i) (2 * n) := by
    obtain hd := slot_header n i
    obtain bd := slot_bound (n := n) hi
    exact O₁.val32 (by simp only [maskO]; omega_using [hd]) (by simp only [stride] at bd; omega_using [sm, bd])
  obtain hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by
    rw [keep₁ 8 (by decide), hb]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 10) (a := 9) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain mask₂ : w32 s₂.mem base maskO = w32 s₁.mem base maskO := by
    obtain h1 := slot_header n 1
    obtain h2 := slot_header n 2
    obtain h10 := slot_header n 10
    have := K₂.mem.val32 (d := maskO) (k := 1) (fun r hr => by
      simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp only [maskO] <;> omega_arith) (by decide)
    simpa only [val32, Nat.mul_zero, Nat.add_zero] using this
  refine WP.seq (wp_ldr (by decide) (c₂.ws.ea12 (by simp only [maskO]; omega_using [h8])) (c₂.ws.read (d := maskO) (n := 4)
    (by simp only [maskO]; omega_using [h8])) fun s₃ u₃ => WP.block_nil ?_)
  obtain w₃ := c₂.ws.of_upd u₃ (by decide)
  obtain b9 := slot_bound (n := n) (i := 9) (by decide)
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  obtain r3 : s₃.gpr .r3 = if decide (w32 s.mem base (slot n 11) % 2 = 1) = true then BitVec.allOnes 32 else 0 := by
    rw [u₃.gpr]
    apply BitVec.eq_of_toNat_eq
    show w32 s₂.mem base maskO = _
    rw [mask₂, M₁]
    simp only [decide_eq_true_eq, expS]
    rfl
  refine WP.mono (selectW_ok w₃ (k := 2 * n) (src := slot n 9) (tmp := slot n 10) (o := slot n 9) _ r3 (by omega_using [hn])
    (by simp only [stride] at *; omega_using [sz, b9]) (by simp only [stride] at *; omega_using [sz, b10]) (by simp only [stride] at *; omega_using [sz, b9])
    (by simp only [stride] at *; omega_using [sm, b9]) (by simp only [stride] at *; omega_using [sm, b10]) (by simp only [stride] at *; omega_using [sm, b9])
    (.inl rfl) (.inl (by simp only [stride] at *; omega_using [l910]))) fun t ⟨wt, W, O, R⟩ => ?_
  have m₃ : s₃.mem = s₂.mem := u₃.mem
  rw [m₃] at W O
  rw [show 4 * (2 * n) = 8 * n by omega_using []] at O
  refine ⟨c₂.of_slot wt O (by decide), ?_, ?_, ?_⟩
  · have vp : val32 s₂.mem base (slot n 10) (2 * n) = y * b * 2 ^ (64 * n) % m := by
      obtain v := VG.Proof.Dsa.mont_product h.coprime (a := y) (b := b)
        (by rw [keep₁ 9 (by decide), hy, Nat.mod_mod]) (by rw [keep₁ 8 (by decide), hb, Nat.mod_mod]) V₂
      rwa [Nat.mod_eq_of_lt lt₂] at v
    obtain vy : val32 s₂.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m := by
      rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', keep₁ 9 (by decide), hy]
    by_cases hbit : w32 s.mem base (slot n 11) % 2 = 1
    · rw [val32_move (m := s₂.mem) (d := slot n 10) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_true, ↓reduceIte], vp, ite_eq_left hbit]
    · rw [val32_congr (m := s₂.mem) fun i hi => by
        rw [W i hi]; simp only [hbit, decide_false, Bool.false_eq_true, ↓reduceIte], vy, ite_eq_right hbit]
  · have l1 := slot_le (n := n) (i := 1) (j := 9) (by decide)
    obtain l2 := slot_le (n := n) (i := 2) (j := 9) (by decide)
    obtain e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_using []
    obtain l6 := slot_le (n := n) (i := 6) (j := 9) (by decide)
    obtain h1 := slot_header n 1
    refine ((Outs.of_outside O₁ (by simp [productRanges])).trans (K₂.mem.mono (by simp [productRanges]))).trans
      (Outs.of_outside O (by simp [productRanges]))
  · exact ((R₁.mono (by decide)).trans K₂.rest).trans ((u₃.rest (by decide)).trans (R.mono (by decide)))

end VG.Proof.Mont.Arm.Dyn

end

end


/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: exponentiation

`exponentiate n expWords` writes `[slot 9] = [slot 8]^[slot 11] mod m`
(`exponentiate_ok`), from one in slot 6 and `R² mod m` in slot 7: the base
and one are encoded, `32 expWords` steps (`exponentStep_ok`, counted in `lr`)
each square the base and multiply the result by it under the exponent's
low bit, which they shift out, and the result is decoded.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_movw wp_subs)

variable {umaal : Bool}

/-- The memory an exponentiation's steps change. -/
def exponentRanges (n expWords : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 8, 8 * n), (slot n 11, 4 * expWords)]

theorem exponentRanges_slot {n expWords i k : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n expWords) s.mem t.mem) (hi : i = 0 ∨ i = 6 ∨ i = 7) (hk : k ≤ 2 * n)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  obtain e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_arith
  obtain e7 : slot n 7 = slot n 6 + stride n := by simp only [slot]; omega_arith
  obtain e8 : slot n 8 = slot n 7 + stride n := by simp only [slot]; omega_arith
  obtain l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
  obtain l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  obtain l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  obtain l01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  obtain l12 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  obtain b11 := slot_bound (n := n) (i := 11) (by decide)
  obtain h0 := slot_header n 0
  simp only [stride] at *
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, maskO, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hi with rfl | rfl | rfl <;> rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> omega_arith
  · rcases hi with rfl | rfl | rfl <;> omega_arith

theorem exponentBody_ok {n size m y b expWords : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentBody umaal n expWords) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
  obtain b11 := slot_bound (n := n) (i := 11) (by decide)
  obtain h0 := slot_header n 0
  obtain l811 := slot_le (n := n) (i := 8) (j := 11) (by decide)
  obtain l911 := slot_le (n := n) (i := 9) (j := 11) (by decide)
  obtain l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  obtain l111 := slot_le (n := n) (i := 1) (j := 11) (by decide)
  obtain e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega_arith
  obtain l611 := slot_le (n := n) (i := 6) (j := 11) (by decide)
  unfold exponentBody
  refine WP.seq (WP.mono (exponentProduct_ok h hy hb) fun s₁ ⟨c₁, Y₁, O₁, R₁⟩ => ?_)
  obtain B₁ : val32 s₁.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m := by
    rw [← hb]
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega_arith)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
    obtain l810 := slot_le (n := n) (i := 8) (j := 10) (by decide)
    obtain l68 := slot_le (n := n) (i := 6) (j := 8) (by decide)
    obtain l18 := slot_le (n := n) (i := 1) (j := 8) (by decide)
    obtain h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega_arith
  obtain E₁ : val32 s₁.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega_arith)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    obtain h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega_arith
  obtain hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by rw [B₁]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) =
      (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
    obtain ⟨k, rfl⟩ : ∃ k, expWords = k + 1 := ⟨expWords - 1, by omega_arith⟩
    rw [val32_parity]
  -- The shift.
  obtain l011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  obtain hE : slot n 11 + 4 * expWords ≤ size := by simp only [stride] at b11; omega_using [b11, sz, hen]
  obtain hE16 : slot n 11 < 2 ^ 16 := by simp only [stride] at b11; omega_using [b11, sm]
  obtain s0 : slot n 0 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l011; omega_using [l011]
  obtain s8 : slot n 8 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l811; omega_using [l811]
  obtain s9 : slot n 9 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l911; omega_using [l911]
  obtain hE64 : slot n 11 + 4 * expWords ≤ 2 ^ 64 := by omega_using [hE, nw]
  unfold shiftExponent
  refine wp_ptr (d := .r1) (by decide) (by simp only [expS]; exact hE16) fun s₃ u₃ => ?_
  obtain w₃ := c₂.ws.of_upd u₃ (by decide)
  refine WP.mono (shiftWords_ok (E := expS n) expWords 0 s₃ w₃ (by rw [u₃.gpr, u₃.other .r12 (by decide)])
    (by simp only [expS]; omega_using [hE]) (by omega_using [hew])) fun t ⟨wt, O, V, R⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, expS] at O V
  rw [u₃.mem] at O V
  obtain ct : Context n m base size t := by
    refine ⟨wt, c₂.size_le, c₂.small, c₂.n0, ?_, c₂.gt_one, ?_⟩
    · rw [O.val32 (.inl s0) (by omega_using [s0, hE64])]; exact c₂.modulus
    · rw [O.w32 (by simp only [invO]; omega_using [h0, l011]) (by decide)]; exact c₂.inverse
  refine ⟨ct, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O.val32 (.inl s9) (by omega_using [s9, hE64])]; exact Y₂
  · rw [O.val32 (.inl s8) (by omega_using [s8, hE64])]
    obtain v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
      (by rw [B₁, Nat.mod_mod]) (by rw [B₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  · rw [V, E₂]
  · have h1 := slot_header n 1
    exact ((O₁.mono fun r hr => List.mem_append_left _ hr).trans (K₂.mem.mono (by simp [productRanges]))).trans
      (Outs.of_outside O (by simp))
  · exact (R₁.trans K₂.rest).trans ((u₃.rest (by decide)).trans (R.mono (by decide)))

theorem exponentStep_ok {n size m y b expWords k : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .lr = BitVec.ofNat 32 k) :
    WP isa (exponentStep umaal n expWords) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (k - 1) ∧ t.z = decide (k = 1) ∧ Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  unfold exponentStep
  refine WP.seq (WP.mono (exponentBody_ok h he hen hew hy hb) fun s₁ ⟨c₁, Y, B, E, O, R⟩ => ?_)
  refine wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide))) fun t u z => WP.block_nil ?_
  obtain l₁ : s₁.gpr .lr = BitVec.ofNat 32 k := by rw [R.gpr .lr (by decide)]; exact hc
  refine ⟨by rw [u.gpr, l₁, ofNat_sub_one hk hk32], ?_, ⟨c₁.ws.of_upd u (by decide), c₁.size_le, c₁.small, c₁.n0,
    by rw [u.mem]; exact c₁.modulus, c₁.gt_one, by rw [u.mem]; exact c₁.inverse⟩, by rw [u.mem]; exact Y,
    by rw [u.mem]; exact B, by rw [u.mem]; exact E, by rw [u.mem]; exact O,
    (R.mono (by decide)).trans (u.rest (by decide))⟩
  rw [z, l₁, ofNat_sub_one hk hk32, VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
  simp only [decide_eq_decide]
  omega_arith

/-- The invariant of the exponentiation's loop after `i` of its `steps` steps. -/
structure ExponentInv (n size m expWords target steps i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .lr = BitVec.ofNat 32 (steps - i)
  bound : val32 t.mem base (slot n 11) expWords < 2 ^ (steps - i)
  value : ∃ y b,
    val32 t.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m ∧
    val32 t.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m ∧
    (y * b ^ val32 t.mem base (slot n 11) expWords) % m = target
  mem : Outs base (exponentRanges n expWords) s.mem t.mem
  rest : Rest (.lr :: dclob) s t

theorem exponentLoop_ok {n size m expWords a : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = a * 2 ^ (64 * n) % m)
    (hc : s.gpr .lr = BitVec.ofNat 32 (32 * expWords)) :
    WP isa (.loop (exponentStep umaal n expWords) .ne) s
      (ExponentInv n size m expWords (a ^ val32 s.mem base (slot n 11) expWords % m)
        (32 * expWords) (32 * expWords) base s) := by
  let steps := 32 * expWords
  let target := a ^ val32 s.mem base (slot n 11) expWords % m
  obtain hspos : 0 < steps := by dsimp [steps]; omega_arith
  obtain init : ExponentInv n size m expWords target steps 0 base s s := by
    refine ⟨h, ?_, ?_, ⟨1, a, ?_, hb, ?_⟩, Outs.refl _ _ _, Rest.refl _ _⟩
    · simpa only [Nat.sub_zero] using hc
    · simpa only [Nat.sub_zero] using val32_lt s.mem base (slot n 11) expWords
    · simpa only [Nat.one_mul] using hy
    · simp only [Nat.one_mul]; rfl
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = steps - i ∧ i < steps ∧ ExponentInv n size m expWords target steps i base s t)
    ?_ steps s ⟨0, rfl, hspos, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain ⟨y, b, Y, B, V⟩ := I.value
  refine WP.mono (exponentStep_ok I.context he hen hew Y B (by omega_arith) (by dsimp [steps] at *; omega_arith) I.counter)
    fun u ⟨count, zf, C, Y', B', E', O, K⟩ => ?_
  obtain next : ExponentInv n size m expWords target steps (i + 1) base s u := by
    refine ⟨C, ?_, ?_, ⟨_, _, Y', B', ?_⟩, I.mem.trans O, I.rest.trans K⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega_arith]
    · rw [E']
      obtain hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega_arith, Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega_arith
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_true (by omega_arith)]; rfl
    · change ExponentInv n size m expWords target steps steps base s u
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, next⟩
    rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_false (by omega_arith)]; rfl

theorem ExponentInv.finished {n size m expWords target steps : Nat} {base : Addr} {s t : State}
    (I : ExponentInv n size m expWords target steps steps base s t) :
    val32 t.mem base (slot n 9) (2 * n) = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  obtain ez : val32 t.mem base (slot n 11) expWords = 0 := by omega_arith
  obtain ⟨y, b, Y, _, V⟩ := I.value
  rw [ez, Nat.pow_zero, Nat.mul_one] at V
  rw [Y, Nat.mul_mod y, V, Nat.mul_mod_mod]

theorem exponentRanges_op {n expWords o : Nat} {base : Addr} {s t : State}
    (K : OpKeep n base o s t) (ho : o = 8 ∨ o = 9) : Outs base (exponentRanges n expWords) s.mem t.mem := by
  refine K.mem.mono ?_
  intro r hr
  simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases ho with rfl | rfl <;> rcases hr with rfl | rfl | rfl <;> simp [exponentRanges, productRanges]

/-- `[slot 9] = [slot 8]^[slot 11] mod m`, the exponent `expWords` words, from
one in slot 6 and `R² mod m` in slot 7. -/
theorem exponentiate_ok {n size m expWords : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hone : val32 s.mem base (slot n 6) (2 * n) = 1)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (exponentiate umaal n expWords) s fun t =>
      Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) expWords % m ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold exponentiate
  refine WP.seq (WP.mono (context_mul_ok h (o := 9) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  obtain Y₁ : val32 s₁.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  obtain R₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hr2]
  obtain B₁ := K₁.val32 (i := 8) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw'
  obtain E₁ := K₁.val32 (i := 11) (by decide) hen (by decide) (by decide) (.inl (by decide)) nw'
  obtain O₁ : val32 s₁.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hone]
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [R₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain B₂ : val32 s₂.mem base (slot n 8) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁])
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
  obtain E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  obtain O₂ : val32 s₂.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', O₁]
  refine WP.seq (wp_movw fun s₃ u₃ => WP.block_nil ?_)
  obtain c₃ : Context n m base size s₃ := ⟨c₂.ws.of_upd u₃ (by decide), c₂.size_le, c₂.small, c₂.n0,
    u₃.mem ▸ c₂.modulus, c₂.gt_one, u₃.mem ▸ c₂.inverse⟩
  refine WP.seq (WP.mono (exponentLoop_ok c₃ he hen hew (u₃.mem ▸ Y₂) (u₃.mem ▸ B₂)
    (by rw [u₃.gpr, movw_ofNat (by have := c₂.small; simp only [contextBytes, slot, stride] at this; omega_arith)]))
    fun s₄ I => ?_)
  obtain O₄ : val32 s₄.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges_slot I.mem (.inr (.inl rfl)) (Nat.le_refl _) nw', u₃.mem, O₂]
  refine WP.mono (context_mul_ok I.context (o := 9) (a := 9) (b := 6) (by decide) (by decide) (by decide)
    (by rw [O₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := val32 s₄.mem base (slot n 9) (2 * n))
      (out := val32 t.mem base (slot n 9) (2 * n)) h.coprime (by rw [I.finished, Nat.mod_mod]) (by rw [Vt, O₄])
    rw [Nat.mod_eq_of_lt ltt, Nat.mod_mod, u₃.mem, E₂] at v
    exact v
  · have o₁ := exponentRanges_op (expWords := expWords) K₁ (.inr rfl)
    obtain o₂ := exponentRanges_op (expWords := expWords) K₂ (.inl rfl)
    obtain o₃ : Outs base (exponentRanges n expWords) s₂.mem s₃.mem := u₃.mem ▸ Outs.refl _ _ _
    exact (((o₁.trans o₂).trans o₃).trans I.mem).trans (exponentRanges_op Kt (.inr rfl))
  · exact ((((K₁.rest.trans K₂.rest).mono (by decide)).trans (u₃.rest (by decide))).trans I.rest).trans
      (Kt.rest.mono (by decide))

end VG.Proof.Mont.Arm.Dyn

end

end

/-! ### `Dsa.Arm.ContextCall`, which this module and modules that import it used -/

section

/-! # Calls of shared ARMv7 Montgomery setup -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.X25519.Arm (Rest wp_mov wp_movw op2_reg)

abbrev callRanges (n : Nat) := Impl.Dsa.Arm.Context.scratch n

/-- The lightweight setup establishes exactly the invariant needed by sums,
subtractions and streaming reduction, without computing unused powers of two. -/
theorem light_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (modS n) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (light n) s fun t => Context n m base size t ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  have h16 : contextBytes n < 2 ^ 16 := by simp only [contextBytes, slot, stride]; omega_using [hn48]
  have low : w32 s.mem base (slot n 0) % 2 ^ 16 = m % 2 ^ 16 := by
    rw [← hv, val32_mod16 _ _ _ _ (by omega_using [hn])]
    rfl
  refine WP.mono (setupInverse_ok hs (mo := modS n)
    (by simp only [modS, stride] at *; omega_using [hz, b0])
    (by simp only [modS, stride] at *; omega_using [b0, h16]) (by omega_using [hz, b0, h0])
    (by simp only [modS] at *; omega_using [hodd, low])) fun t ⟨wt, I, O, R, _⟩ => ?_
  refine ⟨⟨wt, hz, h16, hn, ?_, hm1, ?_⟩, ?_, R.mono (by decide)⟩
  · rw [O.val32 (by simp only [invO, modS] at *; omega_using [h0])
      (by have := hs.nowrap; simp only [modS, stride] at *; omega_using [b0, h16])]; exact hv
  · rw [Nat.add_mod, Nat.mul_mod, ← low, ← Nat.mul_mod, ← Nat.add_mod]; exact I
  · exact Outs.of_outside O (by simp [scratch, invO])

theorem light_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT true false)) (light n)
      (VG.Arm.Taint.Agree (wsT true false)) :=
  erased_relCT (c₀ := .block (setupInverse 0))
    (VG.Taint.hintOf taintU (wsT true false) (.block (setupInverse 0)))
    (by kernel_rfl) (wsT_noBase _ _) (by decide)

theorem light_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat}
    (W₁ : Ws s₁ base size₁) (W₂ : Ws s₂ base size₂) (h11 : s₁.gpr .r11 = s₂.gpr .r11) :
    SameTrace isa (light n) s₁ s₂ :=
  SameTrace.of_relCT (light_relCT n) (VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact BitVec.eq_of_toNat_eq (W₁.wb_toNat.trans W₂.wb_toNat.symm)
    · exact h11)

theorem body_noCalls (n : Nat) : (body n).noCalls = true := by
  simp only [body, contextSetup, one, powerTwo, addD, addDigits, csubD, Dynamic.zeros, ptrLoop,
    Code.noCalls, Bool.and_self]

theorem head_ok {s : State} (n : Nat) : WP isa (.block (head n)) s fun u =>
    u.gpr .r4 = s.gpr .r12 ∧ u.gpr .r0 = s.gpr .r12 ∧
      u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32 ∧
      Rest [.r0, .r1, .r4] s u ∧ u.mem = s.mem :=
  wp_mov (op2_reg s .r12) fun u₁ U₁ => wp_mov (op2_reg u₁ .r12) fun u₂ U₂ => wp_movw fun u U₃ =>
    WP.block_nil ⟨by rw [U₃.other _ (by decide), U₂.other _ (by decide), U₁.gpr],
      by rw [U₃.other _ (by decide), U₂.gpr, U₁.other _ (by decide)], U₃.gpr,
      ((U₁.rest (by decide)).trans (U₂.rest (by decide))).trans (U₃.rest (by decide)),
      by rw [U₃.mem, U₂.mem, U₁.mem]⟩

theorem entry_pre {s u : State} {base : Addr} {size n : Nat} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn48 : n ≤ 48)
    (h0 : u.gpr .r0 = s.gpr .r12) (h1 : u.gpr .r1 = (BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32)
    (hm : u.mem = s.mem) (ho : val32 s.mem base (modS n) (2 * n) % 2 = 1)
    (hM : 1 < val32 s.mem base (modS n) (2 * n)) :
    (setupK n).pre (u.callEntry.withRegions [] [⟨base, contextBytes n⟩]) := by
  have b0 : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  have l1 : (u.callEntry.gpr .r1).toNat * 8 = contextBytes n := by
    rw [State.callEntry_gpr _ (by decide), h1]; exact Pow.words_eq hn48
  simp only [setupK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_mem, State.callEntry_mem, b0, l1, hm]
  refine ⟨trivial, trivial, ?_, Nat.le_refl _, ho, hM⟩
  rw [State.callEntry_gpr _ (by decide), h0, hs.wb_toNat]
  have := hs.nowrap
  omega_using [hz, this]

theorem call_ok {s : State} {base : Addr} {size n m : Nat} (hs : Ws s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (modS n) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (Impl.Dsa.Arm.Context.call n) s fun t => Context n m base size t ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  unfold Impl.Dsa.Arm.Context.call
  refine WP.seq (WP.mono (head_ok n) fun u ⟨h4, h0, h1, R₁, M₁⟩ => ?_)
  have W₁ := hs.of_rest R₁ (by decide)
  refine WP.seq (WP.call (k := setupK n) (setupK_correct hn hn48)
    (entry_pre hs hz hn48 h0 h1 M₁ (by rw [hv]; exact hodd) (by rw [hv]; exact hm1))
    (Covers.right (Pow.covers_ctx W₁ hz)) (Pow.covers_ctx W₁ hz)
    (fun v RD WR SP _ P _ post => ?_) (body_noCalls n))
  have B : State.addr (u.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0, hs.wb]
  simp only [setupK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, B, M₁, hv] at post
  obtain ⟨Inv, One, RR, O⟩ := post
  have V4 : v.gpr .r4 = s.gpr .r12 := by rw [P _ (by decide) (by decide), h4]
  refine wp_mov (op2_reg v .r4) fun t U => WP.block_nil ?_
  have W : Ws t base size := ⟨by rw [U.gpr, V4, hs.wb], by rw [U.wr, WR]; exact W₁.wr, hs.nowrap⟩
  have Mod : val32 t.mem base (modS n) (2 * n) = m := by
    rw [U.mem, O.val32 (fun r hr => by
      simp only [scratch, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [modS, oneS, rrS, tmpS, accS, resS, slot, stride] <;> omega_using [])
      (by have := hs.nowrap; simp only [modS, contextBytes, slot, stride] at *; omega_using [hn48])]
    exact hv
  refine ⟨⟨W, hz, by simp only [contextBytes, slot, stride]; omega_using [hn48], hn, Mod, hm1,
    by rw [U.mem]; exact Inv⟩, by rw [U.mem]; exact One, by rw [U.mem]; exact RR,
    by rw [U.mem]; exact O, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r hr
    have H : r = .r11 ∨ r = .r12 := by revert hr; cases r <;> decide
    rcases H with rfl | rfl
    · rw [U.other _ (by decide), P _ (by decide) (by decide), R₁.gpr _ (by decide)]
    · rw [U.gpr, V4]
  · rw [U.rd, RD, R₁.rd]
  · rw [U.wr, WR, R₁.wr]
  · rw [U.sp, SP, R₁.sp]

theorem call_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n : Nat}
    (W₁ : Ws s₁ base size₁) (W₂ : Ws s₂ base size₂) (Z₁ : contextBytes n ≤ size₁)
    (Z₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (O₁ : val32 s₁.mem base (modS n) (2 * n) % 2 = 1) (M₁ : 1 < val32 s₁.mem base (modS n) (2 * n))
    (O₂ : val32 s₂.mem base (modS n) (2 * n) % 2 = 1) (M₂ : 1 < val32 s₂.mem base (modS n) (2 * n)) :
    SameTrace isa (Impl.Dsa.Arm.Context.call n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (Taint.ofRegs []) a b :=
    fun _ _ => Taint.agree_ofRegs fun _ h => nomatch h
  unfold Impl.Dsa.Arm.Context.call
  refine SameTrace.seq (SameTrace.of_relCT
    (erased_relCT (τ := Taint.ofRegs []) (σ := Taint.ofRegs [])
      (c₀ := .block [.mov .r4 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _))
    (head_ok n) (head_ok n) fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, H₁⟩ ⟨_, h0₂, h1₂, R₂, H₂⟩ => ?_
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (setupK_correct hn hn48) (setupK_ct n) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := Taint.ofRegs []) (σ := Taint.ofRegs []) (h := .block []) (by decide)).mono
      (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  refine ⟨entry_pre W₁ Z₁ hn48 h0₁ h1₁ H₁ O₁ M₁, entry_pre W₂ Z₂ hn48 h0₂ h1₂ H₂ O₂ M₂, ?_,
    Covers.right (Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁), Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁,
    Covers.right (Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂), Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂⟩
  simp only [setupK, State.withRegions_gpr]
  rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
  exact BitVec.eq_of_toNat_eq (by rw [W₁.wb_toNat, W₂.wb_toNat])

end VG.Proof.Dsa.Arm.Context

end

end

/-!
# DSA's exponentiation as a function on 32-bit ARM: its code

`vg_dsa_pow_{n}_{e}` (`Impl/Dsa/Arm/Pow.lean`) saves the registers it uses
in the header (`stores_ok`), sets up the context and exponentiates, and
loads them back (`loads_ok`): `body_ok`.
-/

@[expose] public section

namespace VG.Proof.Dsa.Arm.Pow

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr op2_reg)

variable {umaal : Bool}

theorem exponent_scratch {n e : Nat} (he : e ≤ 2 * n) :
    ∀ r ∈ exponentRanges n e, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
      List.not_mem_nil, false_imp_iff, implies_true, and_true, contextBytes, slot, stride, maskO]
    omega_arith)

/-- `b ^ x mod m` into slot 9, for the modulus in slot 0, the base in slot 8
and the exponent of `e` words in slot 11; the registers the calling
convention keeps are restored. -/
theorem body_ok {s : State} {base : Addr} {size n e m : Nat} (E : Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body umaal n e) s fun t =>
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  obtain ⟨c44, c4960⟩ := contextBytes_bounds hn48
  have nw := E.nowrap
  have s0 := slot_bound (n := n) (i := 0) (by decide)
  have s8 := slot_bound (n := n) (i := 8) (by decide)
  have s11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have h8 := slot_header n 8
  have h11 := slot_header n 11
  unfold body save
  refine WP.seq (wp_mov (op2_reg s .r0) fun s₁ u₁ => ?_)
  have w₁ : Ws s₁ base size := ⟨by rw [u₁.gpr]; exact E.wb, u₁.wr ▸ E.wr, nw⟩
  refine WP.mono (stores_ok slots w₁ (slots_fit (by omega_arith)) slots_apart) fun s₂ ⟨S₂, O₂, R₂⟩ => ?_
  have w₂ := w₁.of_rest R₂ (by decide)
  have away : ∀ {d k : Nat}, 44 ≤ d → d + 4 * k ≤ 2 ^ 64 →
      val32 s₂.mem base d k = val32 s.mem base d k := fun hd hd' => by
    rw [O₂.val32 (fun r hr => .inr (by have := slots_words r hr; omega_arith)) hd', u₁.mem]
  have hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := by
    rw [away (by omega_arith) (by simp only [contextBytes, slot, stride] at *; omega_arith)]; exact hv
  refine WP.seq (WP.mono (Context.call_ok w₂ (by omega_arith) hn hn48 hv₂ hm1 hodd)
    fun s₃ ⟨c₃, one₃, rr₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (exponentiate_ok c₃ he hen (by omega_arith) one₃ rr₃) fun s₄ ⟨c₄, V₄, O₄, R₄⟩ => ?_)
  refine WP.mono (loads_ok slots c₄.ws (slots_fit (by omega_arith)) slots_r12 slots_nodup) fun t ⟨L, R₅, M₅⟩ =>
    ⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_⟩
  · have k₃ : ∀ {d k : Nat}, (∀ r ∈ Context.callRanges n, d + 4 * k ≤ r.1 ∨ r.1 + r.2 ≤ d) → d + 4 * k ≤ 2 ^ 64 →
        val32 s₃.mem base d k = val32 s₂.mem base d k := fun h h' => O₃.val32 h h'
    rw [show val32 t.mem base (slot n 9) (2 * n) = val32 s₄.mem base (slot n 9) (2 * n) by rw [M₅], V₄,
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      k₃ (by simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff,
        implies_true, and_true, slot, stride]; omega_arith) (by omega_arith),
      away (by omega_arith) (by omega_arith), away (by omega_arith) (by omega_arith)]
  · have O₂' : Outs base (scratch n) s.mem s₂.mem := by rw [← u₁.mem]; exact outs_within O₂ (words_scratch n)
    rw [M₅]
    exact (O₂'.trans (outs_within O₃ (setup_scratch hn))).trans (outs_within O₄ (exponent_scratch hen))
  · rw [← slots_regs] at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx12 := slots_r12 x hx
    have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [L x hx,
      outs_readW O₄ (by
        simp only [exponentRanges, productRanges, List.cons_append, List.nil_append, List.forall_mem_cons,
          List.not_mem_nil, false_imp_iff, implies_true, and_true, slot, stride, maskO]
        omega_arith) (by omega_arith),
      outs_readW O₃ (by
        simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
          slot, stride]
        omega_arith) (by omega_arith),
      S₂ x hx, u₁.other _ hx12]
  · rw [R₅.sp, R₄.sp, R₃.sp, R₂.sp, u₁.sp]
  · rw [R₅.rd, R₄.rd, R₃.rd, R₂.rd, u₁.rd]
  · rw [R₅.wr, R₄.wr, R₃.wr, R₂.wr, u₁.wr]

/-! ## The function -/

/-- The function's contract in this file's terms: the working space at `r0`,
of `r1` words, and the numbers as `val32` reads them. -/
def powK (n e : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (slot n 0) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧ (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) e % val32 s.mem base (slot n 0) (2 * n) ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0

theorem powK_correct {n e : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (he : 0 < e) (hen : e ≤ 2 * n) (s : State)
    (h : (powK n e).pre s) :
    ∃ tr t, Exec isa (body umaal n e) s tr t ∧ abiPreserved s t ∧ (powK n e).post s t := by
  obtain ⟨-, hwr, hnw, hz, hodd, hm1⟩ := h
  have E : Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, ex, V, O, P, hsp, -, -⟩ := body_ok E hz hn hn48 he hen rfl hm1 hodd
  exact ⟨tr, t, ex, ⟨P, hsp⟩, V, O⟩

/-- Saving the outer helper's registers leaves its arguments in memory. -/
theorem saveHead_ok {s : State} {base : Addr} {size : Nat} (E : Entry s base size) (hz : 44 ≤ size) :
    WP isa (.block save) s fun u => Ws u base size ∧
      Outs base (words slots) s.mem u.mem ∧ Rest [.r12] s u := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun u₁ U => ?_
  have W : Ws u₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (stores_ok slots W (slots_fit hz) slots_apart) fun u ⟨_, O, R⟩ =>
    ⟨W.of_rest R (by decide), by rw [← U.mem]; exact O,
      (U.rest (by decide)).trans (R.mono (by decide))⟩

/-- Context setup may call a helper; its outputs recover the public workspace
before the remainder's taint proof resumes. -/
theorem savedSetup_trace {n : Nat} {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} {rest : Prog isa}
    (E₁ : Entry s₁ base size₁) (E₂ : Entry s₂ base size₂)
    (Z₁ : contextBytes n ≤ size₁) (Z₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (O₁ : val32 s₁.mem base (modS n) (2 * n) % 2 = 1) (M₁ : 1 < val32 s₁.mem base (modS n) (2 * n))
    (O₂ : val32 s₂.mem base (modS n) (2 * n) % 2 = 1) (M₂ : 1 < val32 s₂.mem base (modS n) (2 * n))
    (H : RelCT isa (VG.Arm.Taint.Agree (wsT false false)) rest (fun _ _ => True)) :
    SameTrace isa (.seq (.block save) (.seq (Impl.Dsa.Arm.Context.call n) rest)) s₁ s₂ := by
  have c44 := (contextBytes_bounds hn48).1
  have Eq : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := congrArg BitVec.toNat (E₁.wb.trans E₂.wb.symm)
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H
  refine SameTrace.seq (SameTrace.of_relCT
    (relCT_of_check (τ := VG.Arm.Taint.ofRegs [.r0]) (σ := wsT false false) (h := .block []) (by decide))
    (VG.Arm.Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact Eq))
    (saveHead_ok E₁ (by omega_arith)) (saveHead_ok E₂ (by omega_arith)) fun u₁ u₂ ⟨W₁, Q₁, _⟩ ⟨W₂, Q₂, _⟩ => ?_
  have mod : ∀ {s u : State}, Outs base (words slots) s.mem u.mem →
      val32 u.mem base (modS n) (2 * n) = val32 s.mem base (modS n) (2 * n) := fun O =>
    O.val32 (fun r hr => .inr (by
      have := slots_words r hr; simp only [modS, slot, stride]; omega_arith)) (by
      have := E₁.nowrap; simp only [modS, contextBytes, slot, stride] at *; omega_arith)
  refine SameTrace.seq (Context.call_trace W₁ W₂ Z₁ Z₂ hn hn48
    (by rw [mod Q₁]; exact O₁) (by rw [mod Q₁]; exact M₁)
    (by rw [mod Q₂]; exact O₂) (by rw [mod Q₂]; exact M₂))
    (Context.call_ok W₁ Z₁ hn hn48 rfl (by rw [mod Q₁]; exact M₁) (by rw [mod Q₁]; exact O₁))
    (Context.call_ok W₂ Z₂ hn hn48 rfl (by rw [mod Q₂]; exact M₂) (by rw [mod Q₂]; exact O₂))
    fun v₁ v₂ ⟨C₁, _⟩ ⟨C₂, _⟩ => ?_
  exact SameTrace.of_relCT H (VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
    subst r
    exact BitVec.eq_of_toNat_eq (by rw [C₁.ws.wb_toNat, C₂.ws.wb_toNat]))

theorem powK_ct (n e : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (powK n e).pre (powK n e).pub (body umaal n e) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ Eq => ?_
  have E : ∀ {s : State}, (powK n e).pre s → Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) := by
    intro s H
    exact ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; simp⟩,
      by simpa only [VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩
  have E₂ : Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [Eq]; exact E h₂
  unfold body
  refine savedSetup_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48
    h₁.2.2.2.2.1 h₁.2.2.2.2.2 ?_ ?_ ?_
  · rw [Eq]; exact h₂.2.2.2.2.1
  · rw [Eq]; exact h₂.2.2.2.2.2
  · refine RelCT.seq (exponentiate_relCT false false n e) ?_
    exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial

end VG.Proof.Dsa.Arm.Pow
