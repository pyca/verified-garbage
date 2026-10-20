module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentProduct
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Mont.Arm.Dyn.ExponentParts
import VerifiedGarbage.Proof.Mont.Arm.Dyn.PowerTwo

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

/-- The memory an exponentiation's steps change. -/
def exponentRanges (n expWords : Nat) : List (Nat × Nat) :=
  productRanges n ++ [(slot n 8, 8 * n), (slot n 11, 4 * expWords)]

theorem exponentRanges_slot {n expWords i k : Nat} {base : Addr} {s t : State}
    (O : Outs base (exponentRanges n expWords) s.mem t.mem) (hi : i = 0 ∨ i = 6 ∨ i = 7) (hk : k ≤ 2 * n)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega
  have e7 : slot n 7 = slot n 6 + stride n := by simp only [slot]; omega
  have e8 : slot n 8 = slot n 7 + stride n := by simp only [slot]; omega
  have l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
  have l910 := slot_le (n := n) (i := 9) (j := 10) (by decide)
  have l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  have l01 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have l12 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  simp only [stride] at *
  apply O.val32
  · intro r hr
    simp only [exponentRanges, productRanges, maskO, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      at hr
    rcases hi with rfl | rfl | rfl <;> rcases hr with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl) <;> omega
  · rcases hi with rfl | rfl | rfl <;> omega

theorem exponentBody_ok {n size m y b expWords : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m)
    (hb : val32 s.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m) :
    WP isa (exponentBody n expWords) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest dclob s t := by
  have sz := h.size_le
  have sm := h.small
  have nw := h.ws.nowrap
  have hm0 : 0 < m := by have := h.gt_one; omega
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega
  have b11 := slot_bound (n := n) (i := 11) (by decide)
  have h0 := slot_header n 0
  have l811 := slot_le (n := n) (i := 8) (j := 11) (by decide)
  have l911 := slot_le (n := n) (i := 9) (j := 11) (by decide)
  have l1011 := slot_le (n := n) (i := 10) (j := 11) (by decide)
  have l111 := slot_le (n := n) (i := 1) (j := 11) (by decide)
  have e6 : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega
  have l611 := slot_le (n := n) (i := 6) (j := 11) (by decide)
  unfold exponentBody
  refine WP.seq (WP.mono (exponentProduct_ok h hy hb) fun s₁ ⟨c₁, Y₁, O₁, R₁⟩ => ?_)
  have B₁ : val32 s₁.mem base (slot n 8) (2 * n) = b * 2 ^ (64 * n) % m := by
    rw [← hb]
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    have l89 := slot_le (n := n) (i := 8) (j := 9) (by decide)
    have l810 := slot_le (n := n) (i := 8) (j := 10) (by decide)
    have l68 := slot_le (n := n) (i := 6) (j := 8) (by decide)
    have l18 := slot_le (n := n) (i := 1) (j := 8) (by decide)
    have h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega
  have E₁ : val32 s₁.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    refine O₁.val32 (fun r hr => ?_) (by simp only [stride] at *; omega)
    simp only [productRanges, maskO, List.mem_cons, List.not_mem_nil, or_false] at hr
    have h1 := slot_header n 1
    simp only [stride] at *
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> omega
  have hb₁ : val32 s₁.mem base (slot n 8) (2 * n) < m := by rw [B₁]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 8) (by decide) (by decide) (by decide) hb₁)
    fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  have Y₂ : val32 s₂.mem base (slot n 9) (2 * n) =
      (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
    obtain ⟨k, rfl⟩ : ∃ k, expWords = k + 1 := ⟨expWords - 1, by omega⟩
    rw [val32_parity]
  -- The shift.
  have l011 := slot_le (n := n) (i := 0) (j := 11) (by decide)
  have hE : slot n 11 + 4 * expWords ≤ size := by simp only [stride] at b11; omega_using [b11, sz, hen]
  have hE16 : slot n 11 < 2 ^ 16 := by simp only [stride] at b11; omega_using [b11, sm]
  have s0 : slot n 0 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l011; omega_using [l011]
  have s8 : slot n 8 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l811; omega_using [l811]
  have s9 : slot n 9 + 4 * (2 * n) ≤ slot n 11 := by simp only [stride] at l911; omega_using [l911]
  have hE64 : slot n 11 + 4 * expWords ≤ 2 ^ 64 := by omega_using [hE, nw]
  unfold shiftExponent
  refine wp_ptr (d := .r1) (by decide) (by simp only [expS]; exact hE16) fun s₃ u₃ => ?_
  have w₃ := c₂.ws.of_upd u₃ (by decide)
  refine WP.mono (shiftWords_ok (E := expS n) expWords 0 s₃ w₃ (by rw [u₃.gpr, u₃.other .r12 (by decide)])
    (by simp only [expS]; omega_using [hE]) (by omega_using [hew])) fun t ⟨wt, O, V, R⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero, expS] at O V
  rw [u₃.mem] at O V
  have ct : Context n m base size t := by
    refine ⟨wt, c₂.size_le, c₂.small, c₂.n0, ?_, c₂.gt_one, ?_⟩
    · rw [O.val32 (.inl s0) (by omega_using [s0, hE64])]; exact c₂.modulus
    · rw [O.w32 (by simp only [invO]; omega_using [h0, l011]) (by decide)]; exact c₂.inverse
  refine ⟨ct, ?_, ?_, ?_, ?_, ?_⟩
  · rw [O.val32 (.inl s9) (by omega_using [s9, hE64])]; exact Y₂
  · rw [O.val32 (.inl s8) (by omega_using [s8, hE64])]
    have v := VG.Proof.Dsa.mont_product h.coprime (a := b) (b := b)
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
    WP isa (exponentStep n expWords) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (k - 1) ∧ t.z = decide (k = 1) ∧ Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        (if val32 s.mem base (slot n 11) expWords % 2 = 1 then y * b else y) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 8) (2 * n) = (b * b) * 2 ^ (64 * n) % m ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords / 2 ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  unfold exponentStep
  refine WP.seq (WP.mono (exponentBody_ok h he hen hew hy hb) fun s₁ ⟨c₁, Y, B, E, O, R⟩ => ?_)
  refine wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide))) fun t u z => WP.block_nil ?_
  have l₁ : s₁.gpr .lr = BitVec.ofNat 32 k := by rw [R.gpr .lr (by decide)]; exact hc
  refine ⟨by rw [u.gpr, l₁, ofNat_sub_one hk hk32], ?_, ⟨c₁.ws.of_upd u (by decide), c₁.size_le, c₁.small, c₁.n0,
    by rw [u.mem]; exact c₁.modulus, c₁.gt_one, by rw [u.mem]; exact c₁.inverse⟩, by rw [u.mem]; exact Y,
    by rw [u.mem]; exact B, by rw [u.mem]; exact E, by rw [u.mem]; exact O,
    (R.mono (by decide)).trans (u.rest (by decide))⟩
  rw [z, l₁, ofNat_sub_one hk hk32, VG.Proof.X25519.Arm.ofNat_beq_zero (by omega)]
  simp only [decide_eq_decide]
  omega

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
    WP isa (.loop (exponentStep n expWords) .ne) s
      (ExponentInv n size m expWords (a ^ val32 s.mem base (slot n 11) expWords % m)
        (32 * expWords) (32 * expWords) base s) := by
  let steps := 32 * expWords
  let target := a ^ val32 s.mem base (slot n 11) expWords % m
  have hspos : 0 < steps := by dsimp [steps]; omega
  have init : ExponentInv n size m expWords target steps 0 base s s := by
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
  refine WP.mono (exponentStep_ok I.context he hen hew Y B (by omega) (by dsimp [steps] at *; omega) I.counter)
    fun u ⟨count, zf, C, Y', B', E', O, K⟩ => ?_
  have next : ExponentInv n size m expWords target steps (i + 1) base s u := by
    refine ⟨C, ?_, ?_, ⟨_, _, Y', B', ?_⟩, I.mem.trans O, I.rest.trans K⟩
    · rw [count, show steps - i - 1 = steps - (i + 1) by omega]
    · rw [E']
      have hp : 2 ^ (steps - i) = 2 ^ (steps - (i + 1)) * 2 := by
        rw [show steps - i = steps - (i + 1) + 1 by omega, Nat.pow_succ]
      have bound := I.bound
      rw [hp] at bound
      omega
    · rw [E', exponent_step_value]
      exact V
  by_cases hdone : i + 1 = steps
  · refine .inl ⟨?_, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_true (by omega)]; rfl
    · change ExponentInv n size m expWords target steps steps base s u
      rw [hdone] at next
      exact next
  · refine .inr ⟨?_, steps - (i + 1), by omega, i + 1, rfl, by omega, next⟩
    rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_false (by omega)]; rfl

theorem ExponentInv.finished {n size m expWords target steps : Nat} {base : Addr} {s t : State}
    (I : ExponentInv n size m expWords target steps steps base s t) :
    val32 t.mem base (slot n 9) (2 * n) = target * 2 ^ (64 * n) % m := by
  have bound := I.bound
  simp only [Nat.sub_self, Nat.pow_zero] at bound
  have ez : val32 t.mem base (slot n 11) expWords = 0 := by omega
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
    WP isa (exponentiate n expWords) s fun t =>
      Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) expWords % m ∧
      Outs base (exponentRanges n expWords) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  have hm0 : 0 < m := by have := h.gt_one; omega
  have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega
  unfold exponentiate
  refine WP.seq (WP.mono (context_mul_ok h (o := 9) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  have Y₁ : val32 s₁.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  have R₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hr2]
  have B₁ := K₁.val32 (i := 8) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw'
  have E₁ := K₁.val32 (i := 11) (by decide) hen (by decide) (by decide) (.inl (by decide)) nw'
  have O₁ : val32 s₁.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hone]
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [R₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  have B₂ : val32 s₂.mem base (slot n 8) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁])
  have Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
  have E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  have O₂ : val32 s₂.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', O₁]
  refine WP.seq (wp_movw fun s₃ u₃ => WP.block_nil ?_)
  have c₃ : Context n m base size s₃ := ⟨c₂.ws.of_upd u₃ (by decide), c₂.size_le, c₂.small, c₂.n0,
    u₃.mem ▸ c₂.modulus, c₂.gt_one, u₃.mem ▸ c₂.inverse⟩
  refine WP.seq (WP.mono (exponentLoop_ok c₃ he hen hew (u₃.mem ▸ Y₂) (u₃.mem ▸ B₂)
    (by rw [u₃.gpr, movw_ofNat (by have := c₂.small; simp only [contextBytes, slot, stride] at this; omega)]))
    fun s₄ I => ?_)
  have O₄ : val32 s₄.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges_slot I.mem (.inr (.inl rfl)) (Nat.le_refl _) nw', u₃.mem, O₂]
  refine WP.mono (context_mul_ok I.context (o := 9) (a := 9) (b := 6) (by decide) (by decide) (by decide)
    (by rw [O₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := val32 s₄.mem base (slot n 9) (2 * n))
      (out := val32 t.mem base (slot n 9) (2 * n)) h.coprime (by rw [I.finished, Nat.mod_mod]) (by rw [Vt, O₄])
    rw [Nat.mod_eq_of_lt ltt, Nat.mod_mod, u₃.mem, E₂] at v
    exact v
  · have o₁ := exponentRanges_op (expWords := expWords) K₁ (.inr rfl)
    have o₂ := exponentRanges_op (expWords := expWords) K₂ (.inl rfl)
    have o₃ : Outs base (exponentRanges n expWords) s₂.mem s₃.mem := u₃.mem ▸ Outs.refl _ _ _
    exact (((o₁.trans o₂).trans o₃).trans I.mem).trans (exponentRanges_op Kt (.inr rfl))
  · exact ((((K₁.rest.trans K₂.rest).mono (by decide)).trans (u₃.rest (by decide))).trans I.rest).trans
      (Kt.rest.mono (by decide))

end VG.Proof.Mont.Arm.Dyn
