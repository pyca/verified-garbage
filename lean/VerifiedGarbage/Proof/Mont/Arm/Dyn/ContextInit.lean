module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Mont.Arm.Dyn.ExponentParts`, which this module and modules that import it used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the exponent's windows

The facts about `m` a context gives (`Context.odd`, `Context.coprime`), the
Montgomery forms of one and of the base (`mont_one`, `mont_encode`), the
table's entry a register chooses (`pick_ok`, `scanFrom_ok`), the exponent's
top four bits and the exponent shifted up by them (`shiftUp_ok`, `window_ok`),
and a number copied to the table's next entry (`copyOut_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp op2_imm op2_reg op2_lsr op2_lsl dpVal
  toNat_shr toNat_shl)

variable {umaal : Bool}

theorem Context.odd {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s) : m % 2 = 1 := by
  have hi := h.inverse
  have hmod : (m * w32 s.mem base invO + 1) % 2 = 0 := by omega_using [hi]
  rcases (by omega_using [] : m % 2 = 0 ∨ m % 2 = 1) with hm | hm
  · rw [Nat.add_mod, Nat.mul_mod, hm] at hmod; simp at hmod
  · exact hm

theorem Context.coprime {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s) :
    Nat.Coprime (2 ^ (64 * n)) m :=
  VG.Proof.Bignum.coprime_pow2 h.odd _

theorem radix_squared (n : Nat) : 2 ^ (128 * n) = 2 ^ (64 * n) * 2 ^ (64 * n) := by
  rw [← Nat.pow_add]; congr 1; omega_using []

theorem mont_one {v n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = 2 ^ (128 * n) % m) : v = 2 ^ (64 * n) % m := by
  have he : v % m = 2 ^ (64 * n) % m := VG.Proof.Bignum.mont_cancel hc (by rw [h, radix_squared])
  rwa [Nat.mod_eq_of_lt hv] at he

theorem mont_encode {v a n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = a * (2 ^ (128 * n) % m) % m) : v = a * 2 ^ (64 * n) % m := by
  rw [radix_squared] at h
  have he := VG.Proof.Dsa.mont_scale hc h
  rwa [Nat.mod_eq_of_lt hv] at he

theorem val32_parity (m : Mem) (base : Addr) (out n : Nat) : val32 m base out (n + 1) % 2 = w32 m base out % 2 := by
  rw [val32]; omega_using []

/-! ## Slots -/

theorem slot_mono {n i j : Nat} (h : i ≤ j) : slot n i ≤ slot n j := by
  simp only [slot]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

theorem slot_succ (n i : Nat) : slot n (i + 1) = slot n i + stride n := by
  simp only [slot, Nat.succ_mul]; omega_using []

/-- A number in a slot, after code that changed only bytes of another slot. -/
theorem slot_outside {n o i k len : Nat} {base : Addr} {m m' : Mem} (O : Outside base (slot n o) len m m')
    (hl : len ≤ stride n) (hio : i ≠ o) (hk : 4 * k ≤ stride n) (hi : i < 30) (h16 : contextBytes n < 2 ^ 16) :
    val32 m' base (slot n i) k = val32 m base (slot n i) k := by
  have sep := slot_sep (n := n) hio
  have bi := slot_bound (n := n) hi
  exact O.val32 (by omega_using [sep, hl, hk]) (by omega_using [bi, hk, h16])

/-- The memory an exponentiation changes: the temporary slot and the
accumulator, and the slots from the base's on. -/
def exponentRanges (n : Nat) : List (Nat × Nat) := [(slot n 1, 5 * stride n), (slot n 8, 20 * stride n)]

theorem exponentRanges_of {n o len : Nat} {base : Addr} {m m' : Mem} (O : Outside base (slot n o) len m m')
    (ho : 8 ≤ o) (ho' : o < 28) (hl : len ≤ stride n) : Outs base (exponentRanges n) m m' := by
  have l8 := slot_mono (n := n) ho
  have bo := slot_le (n := n) ho'
  have e28 : slot n 28 = slot n 8 + 20 * stride n := by simp only [slot]; omega_using []
  intro x hx
  have h2 := hx (slot n 8, 20 * stride n) (by simp [exponentRanges])
  simp only at h2
  exact O x (by omega_using [l8, bo, e28, hl, h2])

theorem exponentRanges_op {n o : Nat} {base : Addr} {m m' : Mem} (O : Outs base (opRanges n o) m m')
    (ho : 8 ≤ o) (ho' : o < 28) : Outs base (exponentRanges n) m m' := by
  have l8 := slot_mono (n := n) ho
  have bo := slot_le (n := n) ho'
  have e28 : slot n 28 = slot n 8 + 20 * stride n := by simp only [slot]; omega_using []
  have e2 : slot n 2 = slot n 1 + stride n := slot_succ n 1
  have st : stride n = 8 * n + 8 := rfl
  intro x hx
  have h1 := hx (slot n 1, 5 * stride n) (by simp [exponentRanges])
  have h2 := hx (slot n 8, 20 * stride n) (by simp [exponentRanges])
  simp only at h1 h2
  refine O x fun r hr => ?_
  simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega_using [l8, bo, e28, e2, st, h1, h2]

/-- The modulus, one and `R²` are not among them. -/
theorem exponentRanges_slot {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (exponentRanges n) m m') (hi : i = 0 ∨ i = 6 ∨ i = 7) (hk : k ≤ 2 * n)
    (h16 : contextBytes n < 2 ^ 16) : val32 m' base (slot n i) k = val32 m base (slot n i) k := by
  apply O.val32
  · intro r hr
    simp only [exponentRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> simp only [slot, stride] <;> omega_using [hk]
  · simp only [contextBytes, slot, stride] at h16
    rcases hi with rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hk, h16]

/-- The memory a product of two powers changes: the second base's and
exponent's slots too. -/
def exponentRanges2 (n : Nat) : List (Nat × Nat) := [(slot n 1, 5 * stride n), (slot n 8, 22 * stride n)]

theorem exponentRanges2_of {n o len : Nat} {base : Addr} {m m' : Mem} (O : Outside base (slot n o) len m m')
    (ho : 8 ≤ o) (ho' : o < 30) (hl : len ≤ stride n) : Outs base (exponentRanges2 n) m m' := by
  have l8 := slot_mono (n := n) ho
  have bo := slot_le (n := n) ho'
  have e28 : slot n 30 = slot n 8 + 22 * stride n := by simp only [slot]; omega_using []
  intro x hx
  have h2 := hx (slot n 8, 22 * stride n) (by simp [exponentRanges2])
  simp only at h2
  exact O x (by omega_using [l8, bo, e28, hl, h2])

theorem exponentRanges2_op {n o : Nat} {base : Addr} {m m' : Mem} (O : Outs base (opRanges n o) m m')
    (ho : 8 ≤ o) (ho' : o < 30) : Outs base (exponentRanges2 n) m m' := by
  have l8 := slot_mono (n := n) ho
  have bo := slot_le (n := n) ho'
  have e28 : slot n 30 = slot n 8 + 22 * stride n := by simp only [slot]; omega_using []
  have e2 : slot n 2 = slot n 1 + stride n := slot_succ n 1
  have st : stride n = 8 * n + 8 := rfl
  intro x hx
  have h1 := hx (slot n 1, 5 * stride n) (by simp [exponentRanges2])
  have h2 := hx (slot n 8, 22 * stride n) (by simp [exponentRanges2])
  simp only at h1 h2
  refine O x fun r hr => ?_
  simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp only <;> omega_using [l8, bo, e28, e2, st, h1, h2]

/-- The modulus, one and `R²` are not among them either. -/
theorem exponentRanges2_slot {n i k : Nat} {base : Addr} {m m' : Mem}
    (O : Outs base (exponentRanges2 n) m m') (hi : i = 0 ∨ i = 6 ∨ i = 7) (hk : k ≤ 2 * n)
    (h16 : contextBytes n < 2 ^ 16) : val32 m' base (slot n i) k = val32 m base (slot n i) k := by
  apply O.val32
  · intro r hr
    simp only [exponentRanges2, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi with rfl | rfl | rfl <;> rcases hr with rfl | rfl <;> simp only [slot, stride] <;> omega_using [hk]
  · simp only [contextBytes, slot, stride] at h16
    rcases hi with rfl | rfl | rfl <;> simp only [slot, stride] <;> omega_using [hk, h16]

/-! ## The table's entry a register chooses -/

theorem maskEq_val : ∀ v < 16, ∀ j < 16,
    (0 : BitVec 32) - (((BitVec.ofNat 32 v ^^^ BitVec.ofNat 32 j) - 1) >>> 31) =
      if v = j then BitVec.allOnes 32 else 0 := by decide

/-- `r3` all ones if `r2 = j`, else zero. -/
theorem maskEq_ok {s : State} {v j : Nat} (hv : v < 16) (hj : j < 16) (h2 : s.gpr .r2 = BitVec.ofNat 32 v) :
    WP isa (.block (maskEq .r2 j)) s fun t =>
      t.gpr .r3 = (if v = j then BitVec.allOnes 32 else 0) ∧ Rest [.r3, .r4] s t ∧ t.mem = s.mem := by
  unfold maskEq
  refine wp_dp (op2_imm (encodable_lt (n := j) (by omega_using [hj]))) fun s₁ u₁ =>
    wp_dp (op2_imm (by decide)) fun s₂ u₂ => wp_mov (op2_lsr (by decide)) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => wp_dp (op2_reg _ _) fun t u₅ => WP.block_nil ⟨?_, ?_, ?_⟩
  · simp only [u₅.get, u₄.get, u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte, dpVal, h2]
    exact maskEq_val v hv j hj
  · exact ((((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
      (u₄.rest (by decide))).trans (u₅.rest (by decide))
  · rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]

/-- `[slot 10]` becomes the table's entry `j` if `r2 = j`. -/
theorem pick_ok {n size v j : Nat} {base : Addr} {s : State} (hs : Ws s base size) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16) (hv : v < 16) (hj : j < 16)
    (h2 : s.gpr .r2 = BitVec.ofNat 32 v) :
    WP isa (pick n j) s fun t => Ws t base size ∧
      val32 t.mem base (slot n 10) (2 * n) =
        (if v = j then val32 s.mem base (slot n (12 + j)) (2 * n) else val32 s.mem base (slot n 10) (2 * n)) ∧
      Outside base (slot n 10) (8 * n) s.mem t.mem ∧ Rest [.r1, .r3, .r4, .r5, .r7, .r8, .r9, .r10] s t := by
  have b10 := slot_bound (n := n) (i := 10) (by decide)
  have bj := slot_bound (n := n) (i := 12 + j) (by omega_using [hj])
  have lj := slot_le (n := n) (i := 10) (j := 12 + j) (by omega_using [])
  simp only [stride] at b10 bj lj
  unfold pick
  refine WP.seq (WP.mono (maskEq_ok hv hj h2) fun s₁ ⟨r3, R₁, m₁⟩ => ?_)
  refine WP.mono (selectW_ok (hs.of_rest R₁ (by decide)) (k := 2 * n) (src := slot n 10) (tmp := slot n (12 + j))
    (o := slot n 10) (decide (v = j)) (by rw [r3]; simp only [decide_eq_true_eq]) (by omega_using [hn])
    (by omega_using [hz, b10]) (by omega_using [hz, bj])
    (by omega_using [hz, b10]) (by omega_using [h16, b10])
    (by omega_using [h16, bj]) (by omega_using [h16, b10])
    (.inl rfl) (.inl (by omega_using [lj]))) fun t ⟨wt, W, O, R⟩ => ?_
  rw [m₁] at W O
  rw [show 4 * (2 * n) = 8 * n by omega_using []] at O
  refine ⟨wt, ?_, O, (R₁.mono (by decide)).trans (R.mono (by decide))⟩
  by_cases e : v = j
  · rw [ite_eq_left e]
    exact val32_move fun i hi => by simp only [W i hi, decide_eq_true e, ↓reduceIte]
  · rw [ite_eq_right e]
    exact val32_congr fun i hi => by simp only [W i hi, decide_eq_false e, Bool.false_eq_true, ↓reduceIte]

/-- `[slot 10]` becomes the table's entry `r2`: with the entries from `j` on
left to read, it is the entry already if that is below `j`. -/
theorem scanFrom_ok {n size v : Nat} {base : Addr} (T : Nat → Nat) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16) (hv : v < 16) :
    ∀ (k j : Nat) (s : State), j + k = 16 → Ws s base size → s.gpr .r2 = BitVec.ofNat 32 v →
      (v < j → val32 s.mem base (slot n 10) (2 * n) = T v) →
      (∀ i, j ≤ i → i < 16 → val32 s.mem base (slot n (12 + i)) (2 * n) = T i) →
      WP isa (scanFrom n k j) s fun t => Ws t base size ∧ val32 t.mem base (slot n 10) (2 * n) = T v ∧
        Outside base (slot n 10) (8 * n) s.mem t.mem ∧ Rest [.r1, .r3, .r4, .r5, .r7, .r8, .r9, .r10] s t
  | 0, j, s, hjk, hs, _, hsel, _ =>
    WP.block_nil ⟨hs, hsel (by omega_using [hjk, hv]), Outside.refl _ _ _ _, Rest.refl _ _⟩
  | k + 1, j, s, hjk, hs, h2, hsel, htab => by
    rw [scanFrom]
    refine WP.seq (WP.mono (pick_ok hs hn hz h16 hv (by omega_using [hjk]) h2) fun s₁ ⟨w₁, V₁, O₁, R₁⟩ => ?_)
    refine WP.mono (scanFrom_ok T hn hz h16 hv k (j + 1) s₁ (by omega_using [hjk]) w₁
      (by rw [R₁.gpr .r2 (by decide)]; exact h2) (fun hlt => ?_) (fun i hi hi16 => ?_))
      fun t ⟨wt, V, O, R⟩ => ⟨wt, V, O₁.trans O, R₁.trans R⟩
    · rw [V₁]
      by_cases e : v = j
      · rw [ite_eq_left e, e]; exact htab j (Nat.le_refl _) (by omega_using [hjk])
      · rw [ite_eq_right e]; exact hsel (by omega_using [hlt, e])
    · rw [← htab i (by omega_using [hi]) hi16]
      exact slot_outside O₁ (by simp only [stride]; omega_using []) (by omega_using []) (by simp only [stride]; omega_using [])
        (by omega_using [hi16]) h16

/-! ## The exponent shifted up four bits -/

theorem carry_word (c x : BitVec 32) (hc : c.toNat < 16) :
    (c ||| x <<< 4).toNat = x.toNat % 2 ^ 28 * 2 ^ 4 + c.toNat := by
  rw [BitVec.toNat_or, toNat_shl]
  have e : x.toNat * 2 ^ 4 % 2 ^ 32 = (x.toNat % 2 ^ 28) <<< 4 := by rw [Nat.shiftLeft_eq]; omega_using []
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega_using [hc] : c.toNat < 2 ^ 4), Nat.shiftLeft_eq]

/-- The `k` words at `[r1 + 4j]` (`r1 = r12 + E`) shifted up four bits: the
bits in `r2` come in, and those that go out are left there. -/
theorem shiftUp_ok {E size : Nat} {base : Addr} :
    ∀ (k j : Nat) (s : State), Ws s base size → s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 E →
    E + 4 * (j + k) ≤ size → 4 * (j + k) ≤ 4096 → (s.gpr .r2).toNat < 16 →
    WP isa (.block (shiftUp k j)) s fun t => Ws t base size ∧
      Outside base (E + 4 * j) (4 * k) s.mem t.mem ∧ (t.gpr .r2).toNat < 16 ∧
      val32 t.mem base (E + 4 * j) k + 2 ^ (32 * k) * (t.gpr .r2).toNat =
        16 * val32 s.mem base (E + 4 * j) k + (s.gpr .r2).toNat ∧ Rest [.r2, .r4, .r5] s t
  | 0, j, s, hs, _, _, _, h2 =>
    WP.block_nil ⟨hs, Outside.refl _ _ _ _, h2, by
      simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add], Rest.refl _ _⟩
  | k + 1, j, s, hs, h1, hk, h4, h2 => by
    have hnw := hs.nowrap
    rw [shiftUp]
    simp only [List.cons_append, List.nil_append]
    refine wp_ldr (by omega_arith) (hs.ea h1 (by omega_arith)) (hs.read (by omega_arith)) fun s₁ u₁ =>
      wp_dp (op2_lsl (by decide)) fun s₂ u₂ => wp_mov (op2_lsr (by decide)) fun s₃ u₃ => ?_
    have w₃ := ((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)
    have e3 : s₃.gpr .r1 = s₃.gpr .r12 + BitVec.ofNat 32 E := by
      simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h1
    refine wp_str (by omega_arith) (w₃.ea e3 (by omega_arith)) (w₃.write (by omega_arith)) fun s₄ m₄ => ?_
    have w₄ := w₃.of_mupd m₄
    have wlt : w32 s.mem base (E + 4 * j) < 2 ^ 32 := (s.mem.readW (off base (E + 4 * j)) 32).isLt
    have r5 : (s₃.gpr .r5).toNat = w32 s.mem base (E + 4 * j) % 2 ^ 28 * 2 ^ 4 + (s.gpr .r2).toNat := by
      simp only [u₃.get, u₂.get, reduceCtorEq, ↓reduceIte, dpVal]
      rw [u₁.other .r2 (by decide), u₁.gpr, carry_word _ _ h2]
    have r2 : (s₄.gpr .r2).toNat = w32 s.mem base (E + 4 * j) / 2 ^ 28 := by
      rw [m₄.gpr, u₃.gpr, toNat_shr, u₂.other .r4 (by decide), u₁.gpr]
    have m4 : s₄.mem = s.mem.writeW (off base (E + 4 * j)) (s₃.gpr .r5) := by
      rw [m₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine WP.mono (shiftUp_ok (E := E) k (j + 1) s₄ w₄ (by rw [m₄.gpr]; exact e3) (by omega_arith) (by omega_arith)
      (by rw [r2]; omega_using [wlt])) fun t ⟨wt, O, c2, V, R⟩ => ⟨wt, ?_, c2, ?_, ?_⟩
    · rw [m4] at O
      exact ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        (O.mono (by omega_arith) (by omega_arith))
    · rw [m4, show E + 4 * (j + 1) = E + 4 * j + 4 by omega_arith] at O V
      have head : w32 t.mem base (E + 4 * j) = (s₃.gpr .r5).toNat := by
        rw [O.w32 (by omega_arith) (by omega_arith), w32_write_self]
      have tail : val32 (s.mem.writeW (off base (E + 4 * j)) (s₃.gpr .r5)) base (E + 4 * j + 4) k =
          val32 s.mem base (E + 4 * j + 4) k :=
        (writeW32_outside s.mem base (d := E + 4 * j) (s₃.gpr .r5) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
      rw [tail, r2] at V
      rw [val32, val32, head, r5, pow32_succ, Nat.mul_assoc]
      omega_using [V, wlt]
    · exact (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
        ((m₄.rest _).trans R)

/-- `r2` is the exponent's top four bits, and the exponent is shifted up by them. -/
theorem window_ok {n size expWords : Nat} {base : Addr} {s : State} (hs : Ws s base size)
    (he : expS n + 4 * expWords ≤ size) (h16 : expS n < 2 ^ 16) (hew : expWords ≤ 1024) :
    WP isa (.block (window n expWords)) s fun t => Ws t base size ∧
      Outside base (expS n) (4 * expWords) s.mem t.mem ∧ (t.gpr .r2).toNat < 16 ∧
      val32 t.mem base (expS n) expWords + 2 ^ (32 * expWords) * (t.gpr .r2).toNat =
        16 * val32 s.mem base (expS n) expWords ∧ Rest [.r1, .r2, .r4, .r5] s t := by
  unfold window
  refine wp_ptr (d := .r1) (by decide) h16 fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have w₂ := (hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  have z2 : (s₂.gpr .r2).toNat = 0 := by rw [u₂.gpr]; rfl
  refine WP.mono (shiftUp_ok (E := expS n) expWords 0 s₂ w₂
    (by rw [u₂.other .r1 (by decide), u₂.other .r12 (by decide), u₁.gpr, u₁.other .r12 (by decide)])
    (by omega_using [he]) (by omega_using [hew]) (by omega_using [z2])) fun t ⟨wt, O, c, V, R⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at O V
  rw [u₂.mem, u₁.mem] at O V
  exact ⟨wt, O, c, by rw [V, z2, Nat.add_zero],
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (R.mono (by decide))⟩

/-! ## An exponent shifted up two bits -/

theorem carry_word2 (c x : BitVec 32) (hc : c.toNat < 4) :
    (c ||| x <<< 2).toNat = x.toNat % 2 ^ 30 * 2 ^ 2 + c.toNat := by
  rw [BitVec.toNat_or, toNat_shl]
  have e : x.toNat * 2 ^ 2 % 2 ^ 32 = (x.toNat % 2 ^ 30) <<< 2 := by rw [Nat.shiftLeft_eq]; omega_using []
  rw [e, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (by omega_using [hc] : c.toNat < 2 ^ 2), Nat.shiftLeft_eq]

/-- The `k` words at `[r1 + 4j]` (`r1 = r12 + E`) shifted up two bits: the
bits in `r2` come in, and those that go out are left there. -/
theorem shiftUp2_ok {E size : Nat} {base : Addr} :
    ∀ (k j : Nat) (s : State), Ws s base size → s.gpr .r1 = s.gpr .r12 + BitVec.ofNat 32 E →
    E + 4 * (j + k) ≤ size → 4 * (j + k) ≤ 4096 → (s.gpr .r2).toNat < 4 →
    WP isa (.block (shiftUp2 k j)) s fun t => Ws t base size ∧
      Outside base (E + 4 * j) (4 * k) s.mem t.mem ∧ (t.gpr .r2).toNat < 4 ∧
      val32 t.mem base (E + 4 * j) k + 2 ^ (32 * k) * (t.gpr .r2).toNat =
        4 * val32 s.mem base (E + 4 * j) k + (s.gpr .r2).toNat ∧ Rest [.r2, .r4, .r5] s t
  | 0, j, s, hs, _, _, _, h2 =>
    WP.block_nil ⟨hs, Outside.refl _ _ _ _, h2, by
      simp only [val32, Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add], Rest.refl _ _⟩
  | k + 1, j, s, hs, h1, hk, h4, h2 => by
    have hnw := hs.nowrap
    rw [shiftUp2]
    simp only [List.cons_append, List.nil_append]
    refine wp_ldr (by omega_arith) (hs.ea h1 (by omega_arith)) (hs.read (by omega_arith)) fun s₁ u₁ =>
      wp_dp (op2_lsl (by decide)) fun s₂ u₂ => wp_mov (op2_lsr (by decide)) fun s₃ u₃ => ?_
    have w₃ := ((hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)
    have e3 : s₃.gpr .r1 = s₃.gpr .r12 + BitVec.ofNat 32 E := by
      simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]; exact h1
    refine wp_str (by omega_arith) (w₃.ea e3 (by omega_arith)) (w₃.write (by omega_arith)) fun s₄ m₄ => ?_
    have w₄ := w₃.of_mupd m₄
    have wlt : w32 s.mem base (E + 4 * j) < 2 ^ 32 := (s.mem.readW (off base (E + 4 * j)) 32).isLt
    have r5 : (s₃.gpr .r5).toNat = w32 s.mem base (E + 4 * j) % 2 ^ 30 * 2 ^ 2 + (s.gpr .r2).toNat := by
      simp only [u₃.get, u₂.get, reduceCtorEq, ↓reduceIte, dpVal]
      rw [u₁.other .r2 (by decide), u₁.gpr, carry_word2 _ _ h2]
    have r2 : (s₄.gpr .r2).toNat = w32 s.mem base (E + 4 * j) / 2 ^ 30 := by
      rw [m₄.gpr, u₃.gpr, toNat_shr, u₂.other .r4 (by decide), u₁.gpr]
    have m4 : s₄.mem = s.mem.writeW (off base (E + 4 * j)) (s₃.gpr .r5) := by
      rw [m₄.mem, u₃.mem, u₂.mem, u₁.mem]
    refine WP.mono (shiftUp2_ok (E := E) k (j + 1) s₄ w₄ (by rw [m₄.gpr]; exact e3) (by omega_arith) (by omega_arith)
      (by rw [r2]; omega_using [wlt])) fun t ⟨wt, O, c2, V, R⟩ => ⟨wt, ?_, c2, ?_, ?_⟩
    · rw [m4] at O
      exact ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
        (O.mono (by omega_arith) (by omega_arith))
    · rw [m4, show E + 4 * (j + 1) = E + 4 * j + 4 by omega_arith] at O V
      have head : w32 t.mem base (E + 4 * j) = (s₃.gpr .r5).toNat := by
        rw [O.w32 (by omega_arith) (by omega_arith), w32_write_self]
      have tail : val32 (s.mem.writeW (off base (E + 4 * j)) (s₃.gpr .r5)) base (E + 4 * j + 4) k =
          val32 s.mem base (E + 4 * j + 4) k :=
        (writeW32_outside s.mem base (d := E + 4 * j) (s₃.gpr .r5) (by omega_arith)).val32 (by omega_arith) (by omega_arith)
      rw [tail, r2] at V
      rw [val32, val32, head, r5, pow32_succ, Nat.mul_assoc]
      omega_using [V, wlt]
    · exact (((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (u₃.rest (by decide))).trans
        ((m₄.rest _).trans R)

/-- `r2` is the top two bits of the exponent at `[E]`, which is shifted up by them. -/
theorem windowTwo_ok {E size expWords : Nat} {base : Addr} {s : State} (hs : Ws s base size)
    (he : E + 4 * expWords ≤ size) (h16 : E < 2 ^ 16) (hew : expWords ≤ 1024) :
    WP isa (.block (windowTwo E expWords)) s fun t => Ws t base size ∧
      Outside base (E) (4 * expWords) s.mem t.mem ∧ (t.gpr .r2).toNat < 4 ∧
      val32 t.mem base (E) expWords + 2 ^ (32 * expWords) * (t.gpr .r2).toNat =
        4 * val32 s.mem base (E) expWords ∧ Rest [.r1, .r2, .r4, .r5] s t := by
  unfold windowTwo
  refine wp_ptr (d := .r1) (by decide) h16 fun s₁ u₁ => wp_mov (op2_imm (by decide)) fun s₂ u₂ => ?_
  have w₂ := (hs.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  have z2 : (s₂.gpr .r2).toNat = 0 := by rw [u₂.gpr]; rfl
  refine WP.mono (shiftUp2_ok (E := E) expWords 0 s₂ w₂
    (by rw [u₂.other .r1 (by decide), u₂.other .r12 (by decide), u₁.gpr, u₁.other .r12 (by decide)])
    (by omega_using [he]) (by omega_using [hew]) (by omega_using [z2])) fun t ⟨wt, O, c, V, R⟩ => ?_
  simp only [Nat.mul_zero, Nat.add_zero] at O V
  rw [u₂.mem, u₁.mem] at O V
  exact ⟨wt, O, c, by rw [V, z2, Nat.add_zero],
    ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (R.mono (by decide))⟩

/-! ## The table's next entry -/

/-- The `k` words at `[src]` go to `[dst]`, where `r11` is, which moves past them. -/
theorem copyOut_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {k src dst : Nat}
    (h11 : s.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 dst) (hk : 0 < k)
    (hsrc : src + 4 * k ≤ size) (hdst : dst + 4 * k ≤ size) (h16s : src + 4 * k < 2 ^ 16)
    (h16d : dst + 4 * k < 2 ^ 16) (hsep : src + 4 * k ≤ dst ∨ dst + 4 * k ≤ src) :
    WP isa (copyOut k src) s fun t => Ws t base size ∧
      val32 t.mem base dst k = val32 s.mem base src k ∧ Outside base dst (4 * k) s.mem t.mem ∧
      t.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 (dst + 4 * k) ∧ Rest [.r5, .r9, .r10, .r11] s t := by
  have hn := hs.nowrap
  unfold copyOut
  refine WP.seq (wp_ptr (d := .r10) (by decide) (by omega_using [h16s]) fun s₁ u₁ =>
    wp_ptr (d := .r9) (by decide) (by omega_using [h16s]) fun t u₂ => WP.block_nil ?_)
  obtain R : Rest [.r5, .r9, .r10, .r11] s t := (u₁.rest (by simp)).trans (u₂.rest (by simp))
  obtain wt : Ws t base size := hs.of_rest R (by decide)
  obtain mt : t.mem = s.mem := by rw [u₂.mem, u₁.mem]
  obtain p10 : t.gpr .r10 = s.gpr .r12 + BitVec.ofNat 32 src := by
    simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p9 : t.gpr .r9 = s.gpr .r12 + BitVec.ofNat 32 (src + 4 * k) := by
    simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]
  obtain p11 : t.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 dst := by
    rw [u₂.other _ (by decide), u₁.other _ (by decide)]; exact h11
  clear u₁ u₂
  refine ptrLoop_ok (A := s.gpr .r12 + BitVec.ofNat 32 src) (step := 4) (k := k)
    (fun j u => Ws u base size ∧ Rest [.r5, .r9, .r10, .r11] s u ∧
      u.gpr .r11 = s.gpr .r12 + BitVec.ofNat 32 dst + BitVec.ofNat 32 (4 * j) ∧
      (∀ i < j, w32 u.mem base (dst + 4 * i) = w32 s.mem base (src + 4 * i)) ∧
      Outside base dst (4 * j) s.mem u.mem)
    (by decide) hk (by omega_using [h16s]) (fun j u u' ⟨a, c, d, f, g⟩ F => ⟨a.of_fupd F, c.trans (F.rest _),
      by rw [F.gpr]; exact d, by rw [F.mem]; exact f, by rw [F.mem]; exact g⟩)
    ⟨wt, R, by rw [p11]; exact (BitVec.add_zero _).symm, fun i hi => absurd hi (Nat.not_lt_zero _),
      by rw [mt]; exact Outside.refl _ _ _ _⟩
    p10 (by rw [p9, Offset.add_add]) ?_ fun u ⟨a, c, d, f, g⟩ _ =>
      ⟨a, val32_move f, g, by rw [d, Offset.add_add], c⟩
  intro j hj u ⟨wu, Ru, p11u, Vu, Ou⟩ pu p9u
  obtain e12 : u.gpr .r12 = s.gpr .r12 := Ru.gpr _ (by decide)
  obtain xs : w32 u.mem base (src + 4 * j + 0) = w32 s.mem base (src + 4 * j) :=
    Ou.w32 (by omega_using [hsep, hj]) (by omega_using [h16s, hj])
  refine wp_ldr (by decide) (wu.ea (K := src + 4 * j) (at_ptr pu e12) (by omega_using [hsrc, hj]))
    (wu.read (d := src + 4 * j + 0) (n := 4) (by omega_using [hsrc, hj])) fun u₁ v₁ => ?_
  obtain w₁ := wu.of_upd v₁ (by decide)
  refine wp_str (by decide) (w₁.ea (K := dst + 4 * j) (at_ptr (by rw [v₁.other .r11 (by decide)]; exact p11u)
    (by rw [v₁.other .r12 (by decide)]; exact e12)) (by omega_using [hdst, hj]))
    (w₁.write (d := dst + 4 * j + 0) (n := 4) (by omega_using [hdst, hj])) fun u₂ m₂ =>
    wp_bump (by decide) fun u₃ v₃ => wp_bump (by decide) fun u₄ v₄ => WP.block_nil ?_
  obtain m4 : u₄.mem = u.mem.writeW (off base (dst + 4 * j)) (u₁.gpr .r5) := by
    rw [v₄.mem, v₃.mem, m₂.mem, v₁.mem, Nat.add_zero]
  obtain val : (u₁.gpr .r5).toNat = w32 s.mem base (src + 4 * j) := by rw [v₁.gpr]; exact xs
  refine ⟨⟨((w₁.of_mupd m₂).of_upd v₃ (by decide)).of_upd v₄ (by decide), ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Ru.trans (((v₁.rest (by simp)).trans (m₂.rest _)).trans ((v₃.rest (by simp)).trans (v₄.rest (by simp))))
  · simp only [v₄.get, v₃.get, m₂.gpr, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step p11u
  · intro i hi
    rw [m4]
    rcases Nat.lt_or_ge i j with h | h
    · rw [w32_write_lt (by omega_using [hdst, hn, hj]) (by omega_using [h]), Vu i h]
    · rw [show i = j by omega_using [hi, h], w32_write_self, val]
  · rw [m4]
    exact (Ou.mono (Nat.le_refl _) (by omega_using [])).trans
      ((writeW32_outside _ _ _ (by omega_using [h16d, hj])).mono (by omega_using []) (by omega_using []))
  · simp only [v₄.get, v₃.get, m₂.gpr, v₁.get, reduceCtorEq, ↓reduceIte]; exact ptr_step pu
  · simp only [v₄.get, v₃.get, m₂.gpr, v₁.get, reduceCtorEq, ↓reduceIte]; exact p9u

end VG.Proof.Mont.Arm.Dyn

end

end

/-! ### `Mont.Arm.Dyn.PowerTwo`, which this module and modules that import it used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: one and powers of two

`one n out` writes 1 (`one_ok`) and `wordTop n out w` the top bit of word
`w`, `2^(32 w + 31)` (`wordTop_ok`); `doublings` doubles a number below the
modulus as many times as `lr` counts (`doublings_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_str wp_ldr wp_dp wp_movw wp_subs op2_imm op2_reg op2_lsl
  dpVal)

/-- `[out] = 1`, `2n` words. -/
theorem one_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n out : Nat} (hn : 0 < n)
    (hout : out + 8 * n ≤ size) (h16 : out + 8 * n < 2 ^ 16) :
    WP isa (one n out) s fun t => Ws t base size ∧ val32 t.mem base out (2 * n) = 1 ∧
      Outside base out (8 * n) s.mem t.mem ∧ Rest [.r4, .r7, .r9, .r10] s t := by
  have hnw := hs.nowrap
  unfold one
  refine WP.seq (WP.mono (zeros_ok hs (o := out) (k := 2 * n) (by omega_using [hn]) (by omega_using [hout]) (by omega_using [h16]))
    fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  refine wp_ptr (d := .r10) (by decide) (by omega_using [h16]) fun t₁ u₁ => wp_mov (op2_imm (by decide)) fun t₂ u₂ => ?_
  have w₂ := (w₀.of_upd u₁ (by decide)).of_upd u₂ (by decide)
  refine wp_str (by decide) (w₂.ea (d := 0) (K := out)
    (by simp only [u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]) (by omega_using [hn, hout]))
    (w₂.write (d := out + 0) (n := 4) (by omega_using [hn, hout])) fun t m => WP.block_nil ⟨w₂.of_mupd m, ?_, ?_, ?_⟩
  · rw [m.mem, u₂.mem, u₁.mem, Nat.add_zero, show 2 * n = 1 + (2 * n - 1) by omega_using [hn], val32_append, val32, val32,
      w32_write_self, val32_zeros (k := 2 * n - 1) fun j hj => ?_]
    · simp only [u₂.gpr]; rfl
    · rw [w32_write_ne (size := size) hnw (by omega_using [hn, hout]) (by omega_using [hout, hj]) (by omega_using []),
        show out + 4 * 1 + 4 * j = out + 4 * (1 + j) by omega_using [], Z₀ (1 + j) (by omega_using [hj])]
  · rw [m.mem, u₂.mem, u₁.mem, Nat.add_zero]
    rw [show 4 * (2 * n) = 8 * n by omega_using []] at O₀
    exact O₀.trans ((writeW32_outside _ _ (d := out) _ (by omega_using [h16])).mono (by omega_using []) (by omega_using [hn]))
  · exact (R₀.mono (by decide)).trans ((((u₁.rest (by decide)).trans (u₂.rest (by decide)))).trans (m.rest _))

/-- `[out] = 2^(32 w + 31)`, `2n` words, for a word `w` of theirs. -/
theorem wordTop_ok {s : State} {base : Addr} {size : Nat} (hs : Ws s base size) {n out w : Nat} (hw : w < 2 * n)
    (hout : out + 8 * n ≤ size) (h16 : out + 8 * n < 2 ^ 16) (h12 : 8 * n ≤ 4096) :
    WP isa (wordTop n out w) s fun t => Ws t base size ∧ val32 t.mem base out (2 * n) = 2 ^ (32 * w + 31) ∧
      Outside base out (8 * n) s.mem t.mem ∧ Rest [.r4, .r7, .r9, .r10] s t := by
  have hnw := hs.nowrap
  unfold wordTop
  refine WP.seq (WP.mono (zeros_ok hs (o := out) (k := 2 * n) (by omega_using [hw]) (by omega_using [hout])
    (by omega_using [h16])) fun t₀ ⟨w₀, Z₀, O₀, R₀⟩ => ?_)
  refine wp_ptr (d := .r10) (by decide) (by omega_using [h16]) fun t₁ u₁ => wp_mov (op2_imm (by decide)) fun t₂ u₂ =>
    wp_mov (op2_lsl (by decide)) fun t₃ u₃ => ?_
  have w₃ := ((w₀.of_upd u₁ (by decide)).of_upd u₂ (by decide)).of_upd u₃ (by decide)
  refine wp_str (by omega_using [hw, h12]) (w₃.ea (d := 4 * w) (K := out)
    (by simp only [u₃.get, u₂.get, u₁.get, reduceCtorEq, ↓reduceIte]) (by omega_using [hw, hout]))
    (w₃.write (d := out + 4 * w) (n := 4) (by omega_using [hw, hout])) fun t m =>
      WP.block_nil ⟨w₃.of_mupd m, ?_, ?_, ?_⟩
  · rw [m.mem, u₃.mem, u₂.mem, u₁.mem, show 2 * n = w + ((2 * n - w - 1) + 1) by omega_using [hw], val32_append,
      val32, w32_write_self, val32_zeros (k := w) fun j hj => ?_,
      val32_zeros (k := 2 * n - w - 1) fun j hj => ?_]
    · rw [u₃.gpr, u₂.gpr, Nat.zero_add, Nat.mul_zero, Nat.add_zero,
        show ((1 : BitVec 32) <<< 31).toNat = 2 ^ 31 from rfl, ← Nat.pow_add]
    · rw [w32_write_ne (size := size) hnw (by omega_using [hw, hout]) (by omega_using [hw, hout, hj])
        (.inr (by omega_using [])), show out + 4 * w + 4 + 4 * j = out + 4 * (w + 1 + j) by omega_using [],
        Z₀ (w + 1 + j) (by omega_using [hj])]
    · rw [w32_write_ne (size := size) hnw (by omega_using [hw, hout]) (by omega_using [hw, hout, hj])
        (.inl (by omega_using [hj])), Z₀ j (by omega_using [hj, hw])]
  · rw [m.mem, u₃.mem, u₂.mem, u₁.mem]
    rw [show 4 * (2 * n) = 8 * n by omega_using []] at O₀
    exact O₀.trans ((writeW32_outside _ _ (d := out + 4 * w) _ (by omega_using [h16, hw])).mono
      (by omega_using []) (by omega_using [hw]))
  · exact (R₀.mono (by decide)).trans (((((u₁.rest (by decide)).trans (u₂.rest (by decide)))).trans
      (u₃.rest (by decide))).trans (m.rest _))

/-- A count down by one. -/
theorem ofNat_sub_one {k : Nat} (h0 : 0 < k) (h : k < 2 ^ 32) :
    BitVec.ofNat 32 k - (1 : BitVec 32) = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]
  omega

/-- The invariant of the doublings after `j` of them. -/
structure DblInv (n m : Nat) (base : Addr) (size o count V : Nat) (s : State) (j : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n o) (2 * n) = 2 ^ j * V % m
  mem : Outs base (opRanges n o) s.mem u.mem
  rest : Rest (.lr :: dclob) s u
  lr : u.gpr .lr = BitVec.ofNat 32 (count - j)

/-- `[slot o]`, below `m`, doubled modulo `m` the `count` times in `lr`. -/
theorem doublings_ok {n m size o count V : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 30) (hc : 0 < count) (hc32 : count < 2 ^ 32) (hlr : s.gpr .lr = BitVec.ofNat 32 count)
    (hV : val32 s.mem base (slot n o) (2 * n) = V) (hVm : V < m) :
    WP isa (doublings (contextMod n) (accS n) (slot n o)) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n o) (2 * n) = 2 ^ count * V % m ∧ Outs base (opRanges n o) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have hm0 : 0 < m := by omega_using [hVm]
  have I0 : DblInv n m base size o count V s 0 s :=
    ⟨h, by rw [hV, Nat.pow_zero, Nat.one_mul, Nat.mod_eq_of_lt hVm], Outs.refl _ _ _, Rest.refl _ _, by rw [hlr, Nat.sub_zero]⟩
  unfold doublings
  refine WP.loop (M := isa) (fun r u => ∃ j, r = count - j ∧ j < count ∧ DblInv n m base size o count V s j u) ?_ count s
    ⟨0, rfl, hc, I0⟩
  rintro r u ⟨j, rfl, hj, I⟩
  have hv : val32 u.mem base (slot n o) (2 * n) < m := by rw [I.val]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_add_ok I.ctx ho ho ho hv hv) fun u₁ ⟨c₁, K₁, V₁⟩ => ?_)
  refine wp_subs (op2_imm (encodable_lt (n := 1) (by decide))) fun u₂ v₂ z₂ => WP.block_nil ?_
  have I' : DblInv n m base size o count V s (j + 1) u₂ := by
    refine ⟨⟨c₁.ws.of_upd v₂ (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [v₂.mem]; exact c₁.modulus, c₁.gt_one,
      by rw [v₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [v₂.mem, V₁, I.val, ← Nat.add_mod, Nat.pow_succ, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]
    · rw [v₂.mem]; exact I.mem.trans K₁.mem
    · exact (I.rest.trans (K₁.rest.mono (by decide))).trans (v₂.rest (by decide))
    · rw [v₂.gpr, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hj]) (by omega_using [hc32])]
      congr 1
  have hz : u₂.z = decide (j + 1 = count) := by
    rw [z₂, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hj]) (by omega_using [hc32]),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_using [hc32])]
    simp only [decide_eq_decide]
    omega_using [hj]
  by_cases hj1 : j + 1 = count
  · exact .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hj1]; rfl,
      I'.ctx, by rw [I'.val, hj1], I'.mem, I'.rest⟩
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hj1]; rfl, count - (j + 1),
      by omega_using [hj], j + 1, rfl, by omega_using [hj, hj1], I'⟩

end VG.Proof.Mont.Arm.Dyn

end

end

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: setting up the context

`contextSetup umaal n`, for the odd modulus `m > 1` in slot 0, stores `m'`,
one in slot 6 (`setupHead_ok`) and `R² mod m` in slot 7 (`contextSetup_ok`,
`rSquared_ok`). The top bits of some of the modulus's words (`topTest_ok`)
choose what `2ⁿ R` is doubled from (`start_ok`): the first of them that is
set, which is then below the modulus (`fromTop_ok`); or one, `65 n` times
(`fromOne_ok`). Six Montgomery squarings follow, each of which squares the
power of two beside `R` (`mont_square`, `raise_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Fupd wp_mov wp_ldr wp_movw wp_cmp op2_imm op2_lsr toNat_shr)

variable {umaal : Bool}

/-- The memory the setup changes. -/
def setupRanges (n : Nat) : List (Nat × Nat) :=
  [(0, 4), (slot n 6, 8 * n), (slot n 7, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

/-- The low digit of a number is its low word's. -/
theorem val32_mod16 (m : Mem) (base : Addr) (d k : Nat) (hk : 0 < k) :
    val32 m base d k % 2 ^ 16 = w32 m base d % 2 ^ 16 := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega_using [hk]⟩
  rw [val32, Nat.add_mod, show 2 ^ 32 * val32 m base (d + 4) k = 2 ^ 16 * (2 ^ 16 * val32 m base (d + 4) k) by
    rw [← Nat.mul_assoc], Nat.mul_mod_right, Nat.add_zero, Nat.mod_mod]

/-- A Montgomery square of `2^e R mod m` is `2^(2e) R mod m`. -/
theorem mont_square {v e n m : Nat} (hc : Nat.Coprime (2 ^ (64 * n)) m) (hv : v < m)
    (h : v * 2 ^ (64 * n) % m = (2 ^ e * 2 ^ (64 * n) % m) * (2 ^ e * 2 ^ (64 * n) % m) % m) :
    v = 2 ^ (2 * e) * 2 ^ (64 * n) % m := by
  have he : v % m = 2 ^ (2 * e) * 2 ^ (64 * n) % m := VG.Proof.Bignum.mont_cancel hc (by
    rw [h, ← Nat.mul_mod, show 2 * e = e + e by omega_using [], Nat.pow_add]
    exact congrArg (· % m) (by grind))
  rwa [Nat.mod_eq_of_lt hv] at he

/-- The invariant of the squarings after `i` of them. -/
structure SqInv (n m : Nat) (base : Addr) (size : Nat) (s : State) (i : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 7) (2 * n) = 2 ^ (n * 2 ^ i) * 2 ^ (64 * n) % m
  mem : Outs base (opRanges n 7) s.mem u.mem
  rest : Rest (.lr :: dclob) s u
  lr : u.gpr .lr = BitVec.ofNat 32 (6 - i)

/-- A word's top bit, by a shift. -/
theorem lsr31_beq_zero (x : BitVec 32) :
    (x >>> 31 - (0 : BitVec 32) == (0 : BitVec 32)) = decide (x.toNat < 2 ^ 31) := by
  have e : (x >>> 31).toNat = x.toNat / 2 ^ 31 := toNat_shr x 31
  have z : x >>> 31 - (0 : BitVec 32) = x >>> 31 := BitVec.sub_zero _
  rw [z, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [e, show (0 : BitVec 32).toNat = 0 from rfl] at this
    omega_using [this]
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [e, show (0 : BitVec 32).toNat = 0 from rfl]
    omega_using [h]

/-- The top bit of a number's word `w` is its bit `32 w + 31`. -/
theorem wordTop_iff (m : Mem) (base : Addr) (d : Nat) {k w : Nat} (hw : w < k) :
    w32 m base (d + 4 * w) < 2 ^ 31 ↔ val32 m base d k / 2 ^ (32 * w + 31) % 2 = 0 := by
  have lo := val32_lt m base d w
  have hx : w32 m base (d + 4 * w) < 2 ^ 32 := (m.readW _ 32).isLt
  rw [show k = w + ((k - w - 1) + 1) by omega_using [hw], val32_append, val32, Nat.pow_add,
    ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt lo, Nat.zero_add]
  generalize w32 m base (d + 4 * w) = x at hx ⊢
  generalize val32 m base (d + 4 * w + 4) (k - w - 1) = hi
  omega_using [hx]

/-- `Z` is whether the top bit of the modulus's word `w` is clear. -/
theorem topTest_ok {n m size w : Nat} {base : Addr} {s : State} (h : Context n m base size s) (hw : w < 2 * n) :
    WP isa (.block (topTest n w)) s fun t => t.z = decide (m / 2 ^ (32 * w + 31) % 2 = 0) ∧ t.mem = s.mem ∧
      Rest [.r4] s t := by
  have sz := h.size_le
  have sm := h.small
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  unfold topTest
  refine wp_ldr (by simp only [modS, slot, contextBytes, stride] at *; omega_using [sm, hw])
    (h.ws.ea12 (d := modS n + 4 * w) (by simp only [modS, stride] at *; omega_using [sz, b0, hw]))
    (h.ws.read (d := modS n + 4 * w) (n := 4) (by simp only [modS, stride] at *; omega_using [sz, b0, hw]))
    fun t₁ u₁ => wp_mov (op2_lsr (by decide)) fun t₂ u₂ => wp_cmp (op2_imm (by decide)) fun t f z =>
      WP.block_nil ⟨?_, by rw [f.mem, u₂.mem, u₁.mem], ((u₁.rest (by decide)).trans (u₂.rest (by decide))).trans (f.rest _)⟩
  rw [z, u₂.gpr, u₁.gpr, lsr31_beq_zero, decide_eq_decide, ← h.modulus]
  exact wordTop_iff s.mem base (modS n) hw

/-- What the doublings start from: `[slot 7]`, below `m`, and their count in
`lr`, which make it `2ⁿ R`. -/
structure Start (n m : Nat) (base : Addr) (size count : Nat) (s t : State) : Prop where
  ctx : Context n m base size t
  lt : val32 t.mem base (slot n 7) (2 * n) < m
  pos : 0 < count
  small : count < 2 ^ 16
  lr : t.gpr .lr = BitVec.ofNat 32 count
  val : 2 ^ count * val32 t.mem base (slot n 7) (2 * n) % m = 2 ^ (65 * n) % m
  mem : Outs base (opRanges n 7) s.mem t.mem
  rest : Rest (.lr :: dclob) s t

/-- A start, after a test that changed `r4` and the flags alone. -/
theorem Start.after {n m size count : Nat} {base : Addr} {s s₀ t : State} (S : Start n m base size count s₀ t)
    (M : s₀.mem = s.mem) (R : Rest [.r4] s s₀) : Start n m base size count s t :=
  ⟨S.ctx, S.lt, S.pos, S.small, S.lr, S.val, by rw [← M]; exact S.mem, (R.mono (by decide)).trans S.rest⟩

/-- From the top bit of a word, which is below a modulus that has it set. -/
theorem fromTop_ok {n m size w : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (h128 : 128 * n < 2 ^ 16) (hw : w < 2 * n) (ht : m / 2 ^ (32 * w + 31) % 2 ≠ 0) :
    WP isa (fromTop n w) s fun t => Start n m base size (65 * n - (32 * w + 31)) s t := by
  have sz := h.size_le
  have sm := h.small
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  have lt : 2 ^ (32 * w + 31) < m := by
    have le : 2 ^ (32 * w + 31) ≤ m := by
      by_contra hlt
      rw [Nat.div_eq_of_lt (Nat.lt_of_not_le hlt)] at ht
      exact ht rfl
    have e : 2 ^ (32 * w + 31) = 2 * 2 ^ (32 * w + 30) := by rw [← Nat.pow_succ']
    have := h.odd
    omega_using [e, this, le]
  unfold fromTop
  refine WP.seq (WP.mono (wordTop_ok h.ws (n := n) (out := slot n 7) hw (by simp only [stride] at *; omega_using [b7, sz])
    (by simp only [stride] at *; omega_using [b7, sm]) (by omega_using [h128])) fun t₁ ⟨w₁, V₁, O₁, R₁⟩ => ?_)
  have c₁ := h.of_slot w₁ O₁ (by decide)
  refine wp_movw fun t u => WP.block_nil ?_
  have V : val32 t.mem base (slot n 7) (2 * n) = 2 ^ (32 * w + 31) := by rw [u.mem]; exact V₁
  refine ⟨⟨c₁.ws.of_upd u (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [u.mem]; exact c₁.modulus, c₁.gt_one,
    by rw [u.mem]; exact c₁.inverse⟩, by rw [V]; exact lt, by omega_using [hw], by omega_using [h128],
    by rw [u.gpr, movw_ofNat (by omega_using [h128])], ?_, ?_, ?_⟩
  · rw [V, ← Nat.pow_add]
    exact congrArg (2 ^ · % m) (by omega_using [hw])
  · rw [u.mem]; exact Outs.of_outside O₁ (by simp)
  · exact (R₁.mono (by decide)).trans (u.rest (by decide))

/-- From one, for any modulus. -/
theorem fromOne_ok {n m size : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (h128 : 128 * n < 2 ^ 16) :
    WP isa (fromOne n) s fun t => Start n m base size (65 * n) s t := by
  have hn := h.n0
  have sz := h.size_le
  have sm := h.small
  have b7 := slot_bound (n := n) (i := 7) (by decide)
  unfold fromOne
  refine WP.seq (WP.mono (one_ok h.ws (n := n) (out := slot n 7) hn (by simp only [stride] at *; omega_using [b7, sz])
    (by simp only [stride] at *; omega_using [b7, sm])) fun t₁ ⟨w₁, V₁, O₁, R₁⟩ => ?_)
  have c₁ := h.of_slot w₁ O₁ (by decide)
  refine wp_movw fun t u => WP.block_nil ?_
  have V : val32 t.mem base (slot n 7) (2 * n) = 1 := by rw [u.mem]; exact V₁
  refine ⟨⟨c₁.ws.of_upd u (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [u.mem]; exact c₁.modulus, c₁.gt_one,
    by rw [u.mem]; exact c₁.inverse⟩, by rw [V]; exact h.gt_one, by omega_using [hn], by omega_using [h128],
    by rw [u.gpr, movw_ofNat (by omega_using [h128])], by rw [V, Nat.mul_one], ?_, ?_⟩
  · rw [u.mem]; exact Outs.of_outside O₁ (by simp)
  · exact (R₁.mono (by decide)).trans (u.rest (by decide))

/-- The context, after a test that changed `r4` and the flags alone. -/
theorem Context.after_test {n m size : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (M : t.mem = s.mem) (R : Rest [.r4] s t) : Context n m base size t :=
  ⟨h.ws.of_rest R (by decide), h.size_le, h.small, h.n0, by rw [M]; exact h.modulus, h.gt_one,
    by rw [M]; exact h.inverse⟩

/-- Where the doublings start: at the first of the words that has its top
bit set, or at one. -/
theorem start_ok {n m size : Nat} {base : Addr} (h128 : 128 * n < 2 ^ 16) :
    ∀ (ks : List Nat) {s : State}, (∀ k ∈ ks, 0 < k) → Context n m base size s →
      WP isa (start n ks) s fun t => ∃ count, Start n m base size count s t
  | [], _, _, h => WP.mono (fromOne_ok h h128) fun _ S => ⟨_, S⟩
  | k :: ks, s, hk, h => by
    have hw : 2 * n - k < 2 * n := by have k0 := hk k List.mem_cons_self; have n0 := h.n0; omega_using [k0, n0]
    rw [start]
    refine WP.seq (WP.mono (topTest_ok h hw) fun t₀ ⟨z₀, M₀, R₀⟩ => ?_)
    have c₀ := h.after_test M₀ R₀
    refine WP.ite (!t₀.z) (VG.Proof.X25519.Arm.eval_ne t₀) (fun ht => ?_) (fun hf => ?_)
    · refine WP.mono (fromTop_ok c₀ h128 hw ?_) fun _ S => ⟨_, S.after M₀ R₀⟩
      rw [z₀] at ht
      simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using ht
    · exact WP.mono (start_ok h128 ks (fun k hk' => hk k (List.mem_cons_of_mem _ hk')) c₀)
        fun _ ⟨count, S⟩ => ⟨count, S.after M₀ R₀⟩

/-- The doublings and the squarings: `[slot 7] = R² mod m`. -/
theorem raise_ok {n m size count : Nat} {base : Addr} {s₀ s : State} (S : Start n m base size count s₀ s) :
    WP isa (raise umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (opRanges n 7) s₀.mem t.mem ∧
      Rest (.lr :: dclob) s₀ t := by
  have h := S.ctx
  have hn := h.n0
  have hm0 : 0 < m := by have := h.gt_one; omega_using [this]
  unfold raise
  rw [show squarings = 6 from rfl]
  refine WP.seq (WP.mono (doublings_ok h (o := 7) (by decide) S.pos (by have := S.small; omega_using [this]) S.lr rfl S.lt)
    fun t₀ ⟨c₀, V₀, O₀, R₀⟩ => ?_)
  rw [S.val] at V₀
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 6) (by decide)))
    fun t₁ u₁ => WP.block_nil ?_)
  have I0 : SqInv n m base size s₀ 0 t₁ := by
    refine ⟨⟨c₀.ws.of_upd u₁ (by decide), c₀.size_le, c₀.small, c₀.n0, by rw [u₁.mem]; exact c₀.modulus, c₀.gt_one,
      by rw [u₁.mem]; exact c₀.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [u₁.mem, V₀, ← Nat.pow_add]
      exact congrArg (2 ^ · % m) (by omega_using [])
    · rw [u₁.mem]; exact S.mem.trans O₀
    · exact (S.rest.trans R₀).trans (u₁.rest (by decide))
    · rw [u₁.gpr]
  refine WP.loop (M := isa) (fun r u => ∃ i, r = 6 - i ∧ i < 6 ∧ SqInv n m base size s₀ i u) ?_
    6 t₁ ⟨0, rfl, by decide, I0⟩
  rintro r u ⟨i, rfl, hi, I⟩
  have hv : val32 u.mem base (slot n 7) (2 * n) < m := by rw [I.val]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok I.ctx (o := 7) (a := 7) (b := 7) (by decide) (by decide) (by decide) hv)
    fun u₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  refine VG.Proof.X25519.Arm.wp_subs (VG.Proof.X25519.Arm.op2_imm (encodable_lt (n := 1) (by decide)))
    fun u₂ v₂ z₂ => WP.block_nil ?_
  have I' : SqInv n m base size s₀ (i + 1) u₂ := by
    refine ⟨⟨c₁.ws.of_upd v₂ (by decide), c₁.size_le, c₁.small, c₁.n0, by rw [v₂.mem]; exact c₁.modulus, c₁.gt_one,
      by rw [v₂.mem]; exact c₁.inverse⟩, ?_, ?_, ?_, ?_⟩
    · rw [v₂.mem, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2]
      exact mont_square I.ctx.coprime lt₁ (by rw [V₁, I.val])
    · rw [v₂.mem]; exact I.mem.trans K₁.mem
    · exact (I.rest.trans (K₁.rest.mono (by decide))).trans (v₂.rest (by decide))
    · rw [v₂.gpr, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hi]) (by omega_using [])]
      congr 1
  have hz : u₂.z = decide (i + 1 = 6) := by
    rw [z₂, K₁.rest.gpr .lr (by decide), I.lr, ofNat_sub_one (by omega_using [hi]) (by omega_using []),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_using [])]
    simp only [decide_eq_decide]
    omega_using [hi]
  by_cases hi1 : i + 1 = 6
  · refine .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hi1]; rfl, I'.ctx, ?_, I'.mem, I'.rest⟩
    rw [I'.val, hi1, ← Nat.pow_add]
    exact congrArg (2 ^ · % m) (by omega_using [])
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hi1]; rfl, 6 - (i + 1),
      by omega_using [hi], i + 1, rfl, by omega_using [hi, hi1], I'⟩

/-- `[slot 7] = R² mod m`. -/
theorem rSquared_ok {n m size : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (h128 : 128 * n < 2 ^ 16) :
    WP isa (rSquared umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (opRanges n 7) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  unfold rSquared
  exact WP.seq (WP.mono (start_ok h128 tops (by decide) h) fun _ ⟨_, S⟩ => raise_ok S)

/-- The inverse and one: the context, before `R²`. -/
theorem setupHead_ok {n size m : Nat} {base : Addr} {s : State} (hs : Ws s base size) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (.seq (.block (setupInverse (modS n))) (one n (oneS n))) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 6) (2 * n) = 1 ∧ Outs base (setupRanges n) s.mem t.mem ∧ Rest dclob s t := by
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have h0 := slot_header n 0
  have low : w32 s.mem base (slot n 0) % 2 ^ 16 = m % 2 ^ 16 := by rw [← hv, val32_mod16 _ _ _ _ (by omega_using [hn])]
  refine WP.seq (WP.mono (setupInverse_ok hs (mo := modS n) (by simp only [modS, stride] at *; omega_using [hz, b0])
    (by simp only [modS, stride] at *; omega_using [h16, b0]) (by omega_using [hz, b0, h0]) (by simp only [modS]; omega_using [hodd, low])) fun t₁ ⟨w₁, I₁, O₁, R₁, _⟩ => ?_)
  have c₁ : Context n m base size t₁ := by
    refine ⟨w₁, hz, h16, hn, ?_, hm1, ?_⟩
    · rw [O₁.val32 (by simp only [invO]; omega_using [h0]) (by simp only [stride] at *; omega_using [h16, b0])]; exact hv
    · rw [Nat.add_mod, Nat.mul_mod, ← low, ← Nat.mul_mod, ← Nat.add_mod]; exact I₁
  have b6 := slot_bound (n := n) (i := 6) (by decide)
  refine WP.mono (one_ok w₁ (n := n) (out := oneS n) hn (by simp only [oneS, stride] at *; omega_using [hz, b6])
    (by simp only [oneS, stride] at *; omega_using [h16, b6])) fun t₂ ⟨w₂, V₂, O₂, R₂⟩ => ?_
  have K₂ : OpKeep n base 6 t₁ t₂ := ⟨R₂.mono (by decide), Outs.of_outside O₂ (by simp [oneS])⟩
  exact ⟨c₁.keep (by omega_using []) w₂ K₂, V₂, (Outs.of_outside O₁ (by simp [setupRanges, invO])).trans
    (Outs.of_outside O₂ (by simp [setupRanges, oneS])), (R₁.mono (by decide)).trans (R₂.mono (by decide))⟩

theorem contextSetup_ok {n size m : Nat} {base : Addr} {s : State} (hs : Ws s base size) (hn : 0 < n)
    (hz : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16) (h128 : 128 * n < 2 ^ 16)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (contextSetup umaal n) s fun t => Context n m base size t ∧ val32 t.mem base (slot n 6) (2 * n) = 1 ∧
      val32 t.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m ∧ Outs base (setupRanges n) s.mem t.mem ∧
      Rest (.lr :: dclob) s t := by
  have nw := hs.nowrap
  unfold contextSetup
  refine WP.assoc (WP.seq (WP.mono (setupHead_ok hs hn hz h16 hv hm1 hodd) fun t₂ ⟨c₂, V₂, O₂, R₂⟩ => ?_))
  refine WP.mono (rSquared_ok c₂ h128) fun t ⟨c, V, O, R⟩ => ⟨c, ?_, V, ?_, ?_⟩
  · have nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_using [hz, nw]
    rw [slot_val32 O (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw']; exact V₂
  · refine O₂.trans (O.mono ?_)
    intro r hr; simp only [opRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [setupRanges]
  · exact (R₂.mono (by decide)).trans R

end VG.Proof.Mont.Arm.Dyn
