module

public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
public import VerifiedGarbage.Proof.Dsa.SameTrace
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Arm.Call
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
import VerifiedGarbage.Proof.Framework.KernelRfl
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
import VerifiedGarbage.Proof.Dsa.Arithmetic
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
import VerifiedGarbage.Proof.Mont.Arm.Csub
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Proof.Framework.Arm.TaintErase
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Dsa.ModPowContract
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Timing
meta import VerifiedGarbage.Proof.Framework.Arm.TaintErase
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Context
meta import VerifiedGarbage.Proof.Framework.Arm.Contract
meta import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Dsa.ModPowContract
meta import VerifiedGarbage.Proof.Dsa.SameTrace
public import VerifiedGarbage.Impl.Dsa.Arm.Pow
import VerifiedGarbage.Proof.Mont.Read
public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Framework.Covers
import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Impl.Dsa.Arm.Pow
meta import VerifiedGarbage.Proof.Mont.Read
meta import VerifiedGarbage.TCB.Arm.Target
meta import VerifiedGarbage.Proof.Framework.Covers
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ws
meta import VerifiedGarbage.Proof.Mont.Words32
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Inverse
meta import VerifiedGarbage.Proof.Mont.Arm.Dyn.Add
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc

/-! ### `Dsa.Arm.ContextBody`, which this module and modules that import it used -/

section

/-! ### `Mont.Arm.Dyn.ContextInit`, which this module and modules that import it used -/

section

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

end

end

/-! ### `Dsa.Arm.RegisterSave`, which this module and modules that import it used -/

section

/-! # Workspace register saves and byte/word conversions shared by DSA helpers -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Pow
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Pow
open VG.Proof.Dsa.ModPow (numAt)
open VG.Proof.X25519.Arm (Rest Upd Mupd wp_mov wp_str wp_ldr op2_reg)

/-- Words at the offsets `l` of the working space, four bytes apart. -/
def Apart (l : List (Reg × Nat)) : Prop := l.Pairwise fun a b => a.2 + 4 ≤ b.2 ∨ b.2 + 4 ≤ a.2

/-- The words `l` lists, each within an immediate offset of `r12` and the
working space. -/
def Fit (size : Nat) (l : List (Reg × Nat)) : Prop := ∀ x ∈ l, x.2 < 4096 ∧ x.2 + 4 ≤ size

/-- The ranges of the words. -/
def words (l : List (Reg × Nat)) : List (Nat × Nat) := l.map fun x => (x.2, 4)

/-- Stores of registers at offsets of `r12`, none of them `r12`. -/
theorem stores_ok {base : Addr} {size : Nat} :
    ∀ (l : List (Reg × Nat)) {s : State}, Ws s base size → Fit size l → Apart l →
      WP isa (.block (l.map fun (r, o) => .str r .r12 o)) s fun t =>
        (∀ x ∈ l, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧ Outs base (words l) s.mem t.mem ∧
        Rest [] s t
  | [], s, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Outs.refl _ _ _, Rest.refl _ _⟩
  | (r, o) :: l, s, hs, hf, ha => by
    have nw := hs.nowrap
    obtain ⟨ho, ho'⟩ := hf _ (List.mem_cons_self ..)
    refine wp_str ho (hs.ea12 (by omega_using [ho'])) (hs.write ho') fun s₁ m₁ => ?_
    have ha' := List.pairwise_cons.mp ha
    refine WP.mono (stores_ok l (hs.of_mupd m₁) (fun x hx => hf x (List.mem_cons_of_mem _ hx)) ha'.2)
      fun t ⟨V, O, R⟩ => ⟨fun x hx => ?_, ?_, (m₁.rest _).trans R⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · have k : t.mem.readW (off base o) 32 = s₁.mem.readW (off base o) 32 :=
          Mem.readW_congr fun i hi => O _ fun w hw => by
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hw
            have := ha'.1 y hy
            have := (hf y (List.mem_cons_of_mem _ hy)).2
            rw [ofs_off base (by omega)]; omega
        rw [k, m₁.mem]
        exact Mem.readW_writeW_self32 _ _ _
      · rw [V x hx, m₁.gpr]
    · intro x hx
      rw [O x fun w hw => hx w (List.mem_cons_of_mem _ hw), m₁.mem]
      exact writeW32_outside _ _ _ (by omega) x (hx _ (List.mem_cons_self ..))

/-- Loads of distinct registers, none of them `r12`, from offsets of `r12`. -/
theorem loads_ok {base : Addr} {size : Nat} :
    ∀ (l : List (Reg × Nat)) {s : State}, Ws s base size → Fit size l → (∀ x ∈ l, x.1 ≠ .r12) →
      (l.map (·.1)).Nodup →
      WP isa (.block (l.map fun (r, o) => .ldr r .r12 o)) s fun t =>
        (∀ x ∈ l, t.gpr x.1 = s.mem.readW (off base x.2) 32) ∧ Rest (l.map (·.1)) s t ∧ t.mem = s.mem
  | [], s, _, _, _, _ => WP.block_nil ⟨(fun _ h => nomatch h), Rest.refl _ _, rfl⟩
  | (r, o) :: l, s, hs, hf, h12, hd => by
    have nw := hs.nowrap
    obtain ⟨ho, ho'⟩ := hf _ (List.mem_cons_self ..)
    refine wp_ldr ho (hs.ea12 (by omega_using [ho'])) (hs.read ho') fun s₁ v₁ => ?_
    have hd' := List.nodup_cons.mp hd
    refine WP.mono (loads_ok l (hs.of_upd v₁ (h12 _ (List.mem_cons_self ..)))
      (fun x hx => hf x (List.mem_cons_of_mem _ hx)) (fun x hx => h12 x (List.mem_cons_of_mem _ hx)) hd'.2)
      fun t ⟨V, R, M⟩ => ⟨fun x hx => ?_, ?_, M.trans v₁.mem⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · rw [R.gpr _ hd'.1, v₁.gpr]
      · rw [V x hx, v₁.mem]
    · exact (v₁.rest (List.mem_cons_self ..)).trans (R.mono fun _ h => List.mem_cons_of_mem _ h)

theorem slots_eq : slots =
    [(.r4, 8), (.r5, 12), (.r6, 16), (.r7, 20), (.r8, 24), (.r9, 28), (.r10, 32), (.r11, 36), (.lr, 40)] := rfl

theorem slots_fit {size : Nat} (hz : 44 ≤ size) : Fit size slots := by
  intro x hx
  simp only [slots_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by decide, by omega_using [hz]⟩

theorem slots_apart : Apart slots := by unfold Apart; decide

theorem slots_r12 : ∀ x ∈ slots, x.1 ≠ .r12 := by decide

theorem slots_nodup : (slots.map (·.1)).Nodup := by decide

/-- Every slot's register is kept by the calling convention. -/
theorem slots_regs : slots.map (·.1) = preserved := rfl

/-- The saved words lie in the header, from its byte 8 on, past `m'`. -/
theorem slots_words : ∀ r ∈ words slots, 8 ≤ r.1 ∧ r.1 + r.2 ≤ 44 := by decide

/-- Ranges each within one of others. -/
theorem outs_within {base : Addr} {rs rs' : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m')
    (h : ∀ r ∈ rs, ∃ r' ∈ rs', r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2) : Outs base rs' m m' :=
  fun x hx => O x fun r hr => by
    obtain ⟨r', hr', h₁, h₂⟩ := h r hr
    have := hx r' hr'
    omega_using [h₁, h₂, this]

/-- A word apart from every range that changed. -/
theorem outs_readW {base : Addr} {rs : List (Nat × Nat)} {m m' : Mem} (O : Outs base rs m m') {d : Nat}
    (hd : ∀ r ∈ rs, d + 4 ≤ r.1 ∨ r.1 + r.2 ≤ d) (hd' : d + 4 ≤ 2 ^ 64) :
    m'.readW (off base d) 32 = m.readW (off base d) 32 :=
  Mem.readW_congr fun i hi => O _ fun r hr => by
    have := hd r hr
    rw [ofs_off base (by omega_using [hd', hi])]; omega_using [hi, this]

/-- The function's working space on entry: `r0` holds its base. -/
structure Entry (s : State) (base : Addr) (size : Nat) : Prop where
  wb : State.addr (s.gpr .r0) = base
  wr : ∃ len, size ≤ len ∧ len ≤ 2 ^ 32 ∧ (⟨base, len⟩ : Region) ∈ s.wr
  nowrap : base.toNat + size ≤ 2 ^ 32

theorem contextBytes_bounds {n : Nat} (hn : n ≤ 48) : 44 ≤ contextBytes n ∧ contextBytes n ≤ 12016 := by
  simp only [contextBytes, slot, stride]; omega_using [hn]

/-- Ranges in the header's first 64 bytes or past the modulus's slot are the
function's own. -/
theorem within_scratch {n : Nat} {rs : List (Nat × Nat)}
    (h : ∀ r ∈ rs, r.1 + r.2 ≤ 64 ∨ (slot n 1 ≤ r.1 ∧ r.1 + r.2 ≤ contextBytes n)) :
    ∀ r ∈ rs, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 := fun r hr =>
  (h r hr).elim (fun h => ⟨(0, 64), List.mem_cons_self .., by simp only; omega_using [h]⟩)
    fun h => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), by simp only; omega_using [h]⟩

theorem setup_scratch {n : Nat} (hn : 0 < n) :
    ∀ r ∈ Impl.Dsa.Arm.Context.scratch n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [Impl.Dsa.Arm.Context.scratch, resS, oneS, rrS, tmpS, accS,
      List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
    omega_using [hn])

theorem words_scratch (n : Nat) :
    ∀ r ∈ words slots, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  fun r hr => ⟨(0, 64), List.mem_cons_self .., by have := slots_words r hr; omega_using [this]⟩


/-- The `4k` bytes at `base + d` are its `k` 32-bit words. -/
theorem read_eq_val32 (m : Mem) (base : Addr) : ∀ (k d : Nat),
    (m.read (off base d) (4 * k)).toNat = val32 m base d k
  | 0, d => by simp [Mem.read, val32]
  | k + 1, d => by
    rw [show 4 * (k + 1) = 4 * k + 4 from rfl, read_toNat_add, val32, ← read_eq_val32 m base k (d + 4),
      Offset.add_add]
    congr 1

theorem numAt_eq8 (m : Mem) (base : Addr) (d n : Nat) : numAt m base d (8 * n) = val32 m base d (2 * n) := by
  rw [← wordsVal_eq_val32, ← read_eq_wordsVal]; rfl

theorem numAt_eq4 (m : Mem) (base : Addr) (d e : Nat) : numAt m base d (4 * e) = val32 m base d e := by
  rw [← read_eq_val32]; rfl



/-- The context's bytes, in words: the function's `ws_len`. -/
theorem words_eq {n : Nat} (hn48 : n ≤ 48) :
    ((BitVec.ofNat 16 (contextBytes n / 8)).setWidth 32).toNat * 8 = contextBytes n := by
  have h : contextBytes n / 8 < 2 ^ 16 := by simp only [contextBytes, slot, stride]; omega_using [hn48]
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega_using [h])]
  simp only [contextBytes, slot, stride]
  omega_using []


/-- The context's region, within the working space's. -/
theorem covers_ctx {s : State} {base : Addr} {size n : Nat} (hs : Ws s base size) (hz : contextBytes n ≤ size) :
    Covers [⟨base, contextBytes n⟩] s.wr := by
  have h := hs.write (d := 0) (n := contextBytes n) (by omega_using [hz])
  rw [show off base 0 = base from BitVec.add_zero _] at h
  exact Covers.one h


end VG.Proof.Dsa.Arm.Pow

end

end

/-! # Correctness and contract of shared ARMv7 Montgomery setup -/

@[expose] public section
namespace VG.Proof.Dsa.Arm.Context
open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Mont.Arm.Dyn
open VG.Impl.Dsa.Arm.Context
open VG.Proof.Dsa.ModPow (numAt Keeps)
open VG.Proof.X25519.Arm (Rest wp_mov op2_reg)

variable {umaal : Bool}

theorem slots_eq (n : Nat) : slots n =
    [(.r4, resS n), (.r5, resS n + 4), (.r6, resS n + 8), (.r7, resS n + 12),
      (.r8, resS n + 16), (.r9, resS n + 20), (.r10, resS n + 24), (.lr, resS n + 28)] := by
  simp [slots, regs]

theorem slots_fit {n size : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (hz : contextBytes n ≤ size) :
    Pow.Fit size (slots n) := by
  intro x hx
  simp only [slots_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    constructor <;> simp only [resS, contextBytes, slot, stride] at * <;> omega_arith

theorem slots_apart (n : Nat) : Pow.Apart (slots n) := by
  simp [Pow.Apart, slots_eq] <;> omega_arith

theorem slots_r12 (n : Nat) : ∀ x ∈ slots n, x.1 ≠ .r12 := by simp [slots_eq]
theorem slots_nodup (n : Nat) : ((slots n).map (·.1)).Nodup := by simp [slots_eq]

theorem slots_words {n : Nat} : ∀ r ∈ Pow.words (slots n), resS n ≤ r.1 ∧ r.1 + r.2 ≤ resS n + 32 := by
  simp only [Pow.words, slots_eq, List.map_cons, List.map_nil, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_true]
  omega_arith

/-- The registers saved, with the working space in `r12`. -/
theorem save_ok {s : State} {base : Addr} {size n : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48) :
    WP isa (.block (save n)) s fun t => Ws t base size ∧
      (∀ x ∈ slots n, t.mem.readW (off base x.2) 32 = s.gpr x.1) ∧
      Outs base (Pow.words (slots n)) s.mem t.mem ∧ Rest [.r12] s t := by
  unfold save
  refine wp_mov (op2_reg s .r0) fun s₁ U => ?_
  have W₁ : Ws s₁ base size := ⟨by rw [U.gpr]; exact E.wb, U.wr ▸ E.wr, E.nowrap⟩
  refine WP.mono (Pow.stores_ok (slots n) W₁ (slots_fit hn hn48 hz) (slots_apart n)) fun t ⟨S, O, R⟩ =>
    ⟨W₁.of_rest R (by decide), fun x hx => by rw [S x hx, U.other _ (slots_r12 n x hx)], by rw [← U.mem]; exact O,
      (U.rest (by decide)).trans (R.mono (by decide))⟩

/-- The saves leave the modulus as it was. -/
theorem save_modulus {s t : State} {base : Addr} {size n : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (O : Outs base (Pow.words (slots n)) s.mem t.mem) :
    val32 t.mem base (slot n 0) (2 * n) = val32 s.mem base (slot n 0) (2 * n) :=
  O.val32 (fun r hr => .inl (by have := slots_words r hr; simp only [resS, slot, stride] at *; omega_arith))
    (by have := E.nowrap; simp only [contextBytes, slot, stride] at *; omega_arith)

theorem body_ok {s : State} {base : Addr} {size n m : Nat} (E : Pow.Entry s base size)
    (hz : contextBytes n ≤ size) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv : val32 s.mem base (slot n 0) (2 * n) = m) (hm1 : 1 < m) (hodd : m % 2 = 1) :
    WP isa (body umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % m ∧
      Outs base (scratch n) s.mem t.mem ∧ (∀ r ∈ preserved, t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  unfold body
  refine WP.seq (WP.mono (save_ok E hz hn hn48) fun s₂ ⟨W₂, S, O, R⟩ => ?_)
  have V₂ : val32 s₂.mem base (slot n 0) (2 * n) = m := (save_modulus E hz O).trans hv
  refine WP.seq (WP.mono (contextSetup_ok W₂ hn hz
    (by simp only [contextBytes, slot, stride]; omega_arith) (by omega_arith) V₂ hm1 hodd)
    fun s₃ ⟨C, One, RR, O₃, R₃⟩ => ?_)
  refine WP.mono (Pow.loads_ok (slots n) C.ws (slots_fit hn hn48 hz) (slots_r12 n) (slots_nodup n))
    fun t ⟨L, R₄, M⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨C.ws.of_rest R₄ (by simp [slots_eq]), C.size_le, C.small, C.n0,
      by rw [M]; exact C.modulus, C.gt_one, by rw [M]; exact C.inverse⟩
  · rw [M]; exact One
  · rw [M]; exact RR
  · rw [M]
    refine (Pow.outs_within O fun r hr => ⟨(resS n, 32), by simp [scratch], (slots_words r hr).1,
      (slots_words r hr).2⟩).trans (O₃.mono ?_)
    intro r hr
    simpa only [scratch, setupRanges, oneS, rrS, tmpS, accS] using List.mem_cons_of_mem (resS n, 32) hr
  · intro r hr
    by_cases h11 : r = .r11
    · subst r
      rw [R₄.gpr _ (by simp [slots_eq]), R₃.gpr _ (by decide), R.gpr _ (by decide)]
    · have hr' : r ∈ (slots n).map (·.1) := by
        simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
        simp only [slots_eq, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr'
      rw [L x hx, Pow.outs_readW O₃ (fun a ha => by
          have := slots_words (x.2, 4) (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
          simp only [setupRanges, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl <;>
            simp only [resS, slot, stride] at * <;> omega_arith)
        (by have := (slots_fit hn hn48 hz) x hx; have := E.nowrap; omega_arith), S x hx]
  · rw [R₄.sp, R₃.sp, R.sp]
  · rw [R₄.rd, R₃.rd, R.rd]
  · rw [R₄.wr, R₃.wr, R.wr]

/-- Internal form of the contract, retaining the word-level output facts.
Its time may depend on the working space's address and on the modulus, some
of whose bits choose where the setup's doublings start (`rSquared`). -/
def setupK (n : Nat) : Contract isa where
  pre s :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    s.rd = [] ∧ s.wr = [⟨base, (s.gpr .r1).toNat * 8⟩] ∧
      (s.gpr .r0).toNat + (s.gpr .r1).toNat * 8 ≤ 2 ^ 32 ∧
      contextBytes n ≤ (s.gpr .r1).toNat * 8 ∧ M % 2 = 1 ∧ 1 < M
  post s t :=
    let base := State.addr (s.gpr .r0)
    let M := val32 s.mem base (modS n) (2 * n)
    (M * w32 t.mem base invO + 1) % 2 ^ 16 = 0 ∧
      val32 t.mem base (oneS n) (2 * n) = 1 ∧
      val32 t.mem base (rrS n) (2 * n) = 2 ^ (128 * n) % M ∧
      Outs base (scratch n) s.mem t.mem
  pub s t := s.gpr .r0 = t.gpr .r0 ∧
    val32 s.mem (State.addr (s.gpr .r0)) (modS n) (2 * n) = val32 t.mem (State.addr (t.gpr .r0)) (modS n) (2 * n)

theorem setupK_correct {n : Nat} (hn : 0 < n) (hn48 : n ≤ 48) (s : State) (h : (setupK n).pre s) :
    ∃ tr t, Exec isa (body umaal n) s tr t ∧ abiPreserved s t ∧ (setupK n).post s t := by
  obtain ⟨-, hwr, hnw, hz, ho, hm⟩ := h
  have E : Pow.Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    ⟨rfl, ⟨_, Nat.le_refl _, by omega_arith, by rw [hwr]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact hnw⟩
  obtain ⟨tr, t, Ex, C, One, RR, O, P, SP, -, -⟩ := body_ok E hz hn hn48 rfl hm ho
  exact ⟨tr, t, Ex, ⟨P, SP⟩, C.inverse, One, RR, O⟩

/-- The working space's base, the same in two runs. -/
theorem agreeBase {s₁ s₂ : State} {base : Addr} {size₁ size₂ : Nat} (h₁ : Ws s₁ base size₁) (h₂ : Ws s₂ base size₂) :
    VG.Arm.Taint.Agree (wsT false false) s₁ s₂ :=
  Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
    subst r
    exact BitVec.eq_of_toNat_eq (by rw [h₁.wb_toNat, h₂.wb_toNat])

theorem save_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (Taint.ofRegs [.r0])) (.block (save n)) (VG.Arm.Taint.Agree (wsT false false)) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (Taint.ofRegs [.r0]) (.block (save 1)) h).map
      (taintU.le (wsT false false)) = some true := ⟨_, by taint_decide⟩
  exact erased_relCT h (by simp only [save, slots_eq]; rfl) (Taint.noBase_ofRegs _) H

theorem restore_relCT (n : Nat) :
    RelCT isa (VG.Arm.Taint.Agree (wsT false false)) (.block (restore n)) (fun _ _ => True) := by
  obtain ⟨h, H⟩ : ∃ h, (VG.Taint.check taintU (wsT false false) (.block (restore 1)) h).map
      (taintU.le (Taint.ofRegs [])) = some true := ⟨_, by taint_decide⟩
  exact (erased_relCT h (by simp only [restore, slots_eq]; rfl) (wsT_noBase _ _) H).mono (fun _ _ h => h)
    fun _ _ _ => trivial

/-- Where the doublings start, and what follows, in two runs with the same
modulus: each test reads the same bit in both. -/
theorem start_trace {base : Addr} {size₁ size₂ n m : Nat} (h128 : 128 * n < 2 ^ 16) :
    ∀ (ks : List Nat) {s₁ s₂ : State}, (∀ k ∈ ks, 0 < k) → Dyn.Context n m base size₁ s₁ →
      Dyn.Context n m base size₂ s₂ → SameTrace isa (.seq (start n ks) (raise umaal n)) s₁ s₂
  | [], _, _, _, c₁, c₂ =>
    SameTrace.of_relCT (RelCT.seq (fromOne_relCT n) (raise_relCT n)) (agreeBase c₁.ws c₂.ws)
  | k :: ks, s₁, s₂, hk, c₁, c₂ => by
    have hw : 2 * n - k < 2 * n := by have k0 := hk k List.mem_cons_self; have n0 := c₁.n0; omega_arith
    rw [start]
    refine SameTrace.assoc_left (SameTrace.seq (SameTrace.of_relCT (topTest_relCT n _) (agreeBase c₁.ws c₂.ws))
      (topTest_ok c₁ hw) (topTest_ok c₂ hw) fun x₁ x₂ ⟨z₁, M₁, R₁⟩ ⟨z₂, M₂, R₂⟩ => ?_)
    obtain d₁ := c₁.after_test M₁ R₁
    obtain d₂ := c₂.after_test M₂ R₂
    refine SameTrace.seq_ite (by rw [VG.Proof.X25519.Arm.eval_ne, VG.Proof.X25519.Arm.eval_ne, z₁, z₂])
      (fun _ => SameTrace.of_relCT (RelCT.seq (fromTop_relCT n _) (raise_relCT n)) (agreeBase d₁.ws d₂.ws))
      (fun _ => start_trace h128 ks (fun k hk' => hk k (List.mem_cons_of_mem _ hk')) d₁ d₂)

/-- Two runs from the same working space, with the same modulus, leak the
same trace: some of its bits choose where the doublings start (`rSquared`),
and every other address and branch is public. -/
theorem body_trace {s₁ s₂ : State} {base : Addr} {size₁ size₂ n m : Nat}
    (E₁ : Pow.Entry s₁ base size₁) (E₂ : Pow.Entry s₂ base size₂)
    (hz₁ : contextBytes n ≤ size₁) (hz₂ : contextBytes n ≤ size₂) (hn : 0 < n) (hn48 : n ≤ 48)
    (hv₁ : val32 s₁.mem base (slot n 0) (2 * n) = m) (hv₂ : val32 s₂.mem base (slot n 0) (2 * n) = m)
    (hm1 : 1 < m) (hodd : m % 2 = 1) :
    SameTrace isa (body umaal n) s₁ s₂ := by
  have h16 : contextBytes n < 2 ^ 16 := by simp only [contextBytes, slot, stride]; omega_arith
  have R0 : s₁.gpr .r0 = s₂.gpr .r0 := by
    apply BitVec.eq_of_toNat_eq
    have H := congrArg BitVec.toNat (E₁.wb.trans E₂.wb.symm)
    simpa only [VG.Proof.X25519.Arm.addr_toNat] using H
  unfold body
  refine SameTrace.seq (SameTrace.of_relCT (save_relCT n) (Taint.agree_ofRegs fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact R0))
    (save_ok E₁ hz₁ hn hn48) (save_ok E₂ hz₂ hn hn48) fun u₁ u₂ ⟨W₁, _, O₁, _⟩ ⟨W₂, _, O₂, _⟩ => ?_
  obtain V₁ := (save_modulus E₁ hz₁ O₁).trans hv₁
  obtain V₂ := (save_modulus E₂ hz₂ O₂).trans hv₂
  refine SameTrace.seq ?_ (contextSetup_ok (umaal := umaal) W₁ hn hz₁ h16 (by omega_arith) V₁ hm1 hodd)
    (contextSetup_ok (umaal := umaal) W₂ hn hz₂ h16 (by omega_arith) V₂ hm1 hodd) fun v₁ v₂ ⟨C₁, _⟩ ⟨C₂, _⟩ =>
      SameTrace.of_relCT (restore_relCT n) (agreeBase C₁.ws C₂.ws)
  unfold contextSetup
  refine SameTrace.assoc (SameTrace.seq (SameTrace.of_relCT (setupHead_relCT n) (agreeBase W₁ W₂))
    (setupHead_ok W₁ hn hz₁ h16 V₁ hm1 hodd) (setupHead_ok W₂ hn hz₂ h16 V₂ hm1 hodd)
    fun t₁ t₂ ⟨c₁, _⟩ ⟨c₂, _⟩ => ?_)
  unfold rSquared
  exact start_trace (by omega_arith) tops (by decide) c₁ c₂

theorem setupK_ct (n : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (setupK n).pre (setupK n).pub (body umaal n) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ ⟨e0, em⟩ => ?_
  have E : ∀ {s : State}, (setupK n).pre s → Pow.Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) :=
    fun {s} H => ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; exact List.mem_singleton_self _⟩,
      by rw [VG.Proof.X25519.Arm.addr_toNat]; exact H.2.2.1⟩
  have E₂ : Pow.Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [e0]; exact E h₂
  rw [← e0] at em
  exact body_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48 rfl em.symm h₁.2.2.2.2.2 h₁.2.2.2.2.1

end VG.Proof.Dsa.Arm.Context

end

end

/-! ### `Mont.Arm.Dyn.Exponent`, which this module and modules that import it used -/

section

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: exponentiation

`exponentiate n expWords` writes `[slot 9] = [slot 8]^[slot 11] mod m`
(`exponentiate_ok`), from one in slot 6 and `R² mod m` in slot 7, by windows
of four bits: the table of the base's sixteen powers, encoded (`table_ok`),
then `8 expWords` windows (`windowStep_ok`, counted in `lr`), each of which
raises the result to its sixteenth power (`squareFour_ok`) and multiplies it
by the power that the exponent's top four bits choose, which it shifts out;
then the result is decoded.
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest Upd Mupd Fupd wp_mov wp_movw wp_subs op2_imm)

variable {umaal : Bool}

/-- A context, after a register but `r12` changed. -/
theorem Context.of_upd {n size m : Nat} {base : Addr} {s t : State} {d : Reg} {v : BitVec 32}
    (h : Context n m base size s) (u : Upd s t d v) (hd : d ≠ .r12) : Context n m base size t :=
  ⟨h.ws.of_upd u hd, h.size_le, h.small, h.n0, by rw [u.mem]; exact h.modulus, h.gt_one,
    by rw [u.mem]; exact h.inverse⟩

/-- The first `k` entries of the table: the powers of `a`, encoded. -/
def Tab (n m a k : Nat) (base : Addr) (mem : Mem) : Prop :=
  ∀ j < k, val32 mem base (slot n (12 + j)) (2 * n) = a ^ j * 2 ^ (64 * n) % m

/-! ## The table -/

/-- The invariant of the table's loop after `i` entries. -/
structure TabInv (n m a size expWords : Nat) (base : Addr) (s : State) (i : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  tab : Tab n m a i base u.mem
  cur : val32 u.mem base (slot n 10) (2 * n) = a ^ i * 2 ^ (64 * n) % m
  bas : val32 u.mem base (slot n 8) (2 * n) = a * 2 ^ (64 * n) % m
  exp : val32 u.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords
  r11 : u.gpr .r11 = u.gpr .r12 + BitVec.ofNat 32 (slot n (12 + i))
  lr : u.gpr .lr = BitVec.ofNat 32 (16 - i)
  mem : Outs base (exponentRanges n) s.mem u.mem
  rest : Rest (.r11 :: .lr :: dclob) s u

theorem tableStep_ok {n m a size expWords i : Nat} {base : Addr} {s u : State} (hen : expWords ≤ 2 * n)
    (I : TabInv n m a size expWords base s i u) (hi : i < 16) :
    WP isa (tableStep umaal n) u fun t =>
      TabInv n m a size expWords base s (i + 1) t ∧ t.z = decide (i + 1 = 16) := by
  have h := I.ctx
  have sz := h.size_le
  have sm := h.small
  have hn := h.n0
  have nw := h.ws.nowrap
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
  obtain b10 := slot_bound (n := n) (i := 10) (by decide)
  obtain bi := slot_bound (n := n) (i := 12 + i) (by omega_arith)
  obtain li := slot_le (n := n) (i := 10) (j := 12 + i) (by omega_arith)
  obtain st : stride n = 8 * n + 8 := rfl
  unfold tableStep
  refine WP.seq (WP.mono (copyOut_ok h.ws (k := 2 * n) (src := slot n 10) (dst := slot n (12 + i)) I.r11
    (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
    (.inl (by omega_arith))) fun u₁ ⟨w₁, V₁, O₁, p₁, R₁⟩ => ?_)
  rw [show 4 * (2 * n) = 8 * n by omega_arith] at O₁ p₁
  obtain c₁ := h.of_slot w₁ O₁ (by omega_arith)
  obtain cur₁ : val32 u₁.mem base (slot n 10) (2 * n) = a ^ i * 2 ^ (64 * n) % m := by
    rw [slot_outside O₁ (by omega_arith) (by omega_arith) (by omega_arith) (by decide) sm]; exact I.cur
  obtain bas₁ : val32 u₁.mem base (slot n 8) (2 * n) = a * 2 ^ (64 * n) % m := by
    rw [slot_outside O₁ (by omega_arith) (by omega_arith) (by omega_arith) (by decide) sm]; exact I.bas
  obtain exp₁ : val32 u₁.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [slot_outside O₁ (by omega_arith) (by omega_arith) (by omega_arith) (by decide) sm]; exact I.exp
  obtain tab₁ : Tab n m a (i + 1) base u₁.mem := fun j hj => by
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with h' | h'
    · rw [slot_outside O₁ (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) sm]; exact I.tab j h'
    · rw [h', V₁]; exact I.cur
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 10) (a := 10) (b := 8) (by decide) (by decide) (by decide)
    (by rw [bas₁]; exact Nat.mod_lt _ hm0)) fun u₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain cur₂ : val32 u₂.mem base (slot n 10) (2 * n) = a ^ (i + 1) * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product h.coprime (a := a ^ i) (b := a)
      (by rw [cur₁, Nat.mod_mod]) (by rw [bas₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂, ← Nat.pow_succ] at v
  obtain bas₂ : val32 u₂.mem base (slot n 8) (2 * n) = a * 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', bas₁]
  obtain exp₂ : val32 u₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', exp₁]
  obtain tab₂ : Tab n m a (i + 1) base u₂.mem := fun j hj => by
    rw [K₂.val32 (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']
    exact tab₁ j hj
  refine wp_bump (by decide) fun u₃ v₃ =>
    wp_subs (op2_imm (encodable_lt (n := 1) (by decide))) fun t v₄ z₄ => WP.block_nil ?_
  obtain e11 : u₂.gpr .r11 = u₁.gpr .r11 := K₂.rest.gpr _ (by decide)
  obtain elr : u₂.gpr .lr = BitVec.ofNat 32 (16 - i) := by
    rw [K₂.rest.gpr _ (by decide), R₁.gpr _ (by decide)]; exact I.lr
  obtain e12 : t.gpr .r12 = u.gpr .r12 := by
    rw [v₄.other _ (by decide), v₃.other _ (by decide), K₂.rest.gpr _ (by decide), R₁.gpr _ (by decide)]
  obtain lr₄ : t.gpr .lr = BitVec.ofNat 32 (16 - i - 1) := by
    rw [v₄.gpr, v₃.other _ (by decide), elr, ofNat_sub_one (by omega_arith) (by omega_arith)]
  refine ⟨⟨(c₂.of_upd v₃ (by decide)).of_upd v₄ (by decide), ?_, ?_, ?_, ?_, ?_, lr₄, ?_, ?_⟩, ?_⟩
  · rw [v₄.mem, v₃.mem]; exact tab₂
  · rw [v₄.mem, v₃.mem]; exact cur₂
  · rw [v₄.mem, v₃.mem]; exact bas₂
  · rw [v₄.mem, v₃.mem]; exact exp₂
  · rw [e12, v₄.other _ (by decide), v₃.gpr, e11, p₁, Offset.add_add]
    refine congrArg (fun k => u.gpr .r12 + BitVec.ofNat 32 k) ?_
    rw [show 12 + (i + 1) = 12 + i + 1 from rfl, slot_succ]; omega_arith
  · rw [v₄.mem, v₃.mem]
    exact (I.mem.trans (exponentRanges_of O₁ (by omega_arith) (by omega_arith) (by omega_arith))).trans
      (exponentRanges_op K₂.mem (by decide) (by decide))
  · exact ((I.rest.trans (R₁.mono (by decide))).trans (K₂.rest.mono (by decide))).trans
      ((v₃.rest (by decide)).trans (v₄.rest (by decide)))
  · rw [z₄, v₃.other _ (by decide), elr, ofNat_sub_one (by omega_arith) (by omega_arith),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith

/-- The table's sixteen entries are the powers of the base in slot 8, encoded;
the exponent is kept. -/
theorem table_ok {n size m expWords : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hen : expWords ≤ 2 * n) (hone : val32 s.mem base (slot n 6) (2 * n) = 1)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (table umaal n) s fun t => Context n m base size t ∧
      Tab n m (val32 s.mem base (slot n 8) (2 * n)) 16 base t.mem ∧
      val32 t.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Rest (.r11 :: .lr :: dclob) s t := by
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  have sm := h.small
  obtain b12 := slot_bound (n := n) (i := 12) (by decide)
  unfold table
  refine WP.seq (WP.mono (context_mul_ok h (o := 10) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  obtain Y₁ : val32 s₁.mem base (slot n 10) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  obtain R₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [K₁.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', hr2]
  obtain B₁ := K₁.val32 (i := 8) (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw'
  obtain E₁ := K₁.val32 (i := 11) (by decide) hen (by decide) (by decide) (.inl (by decide)) nw'
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 8) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [R₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain B₂ : val32 s₂.mem base (slot n 8) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, R₁, B₁])
  obtain Y₂ : val32 s₂.mem base (slot n 10) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', Y₁]
  obtain E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  refine WP.seq (wp_ptr (d := .r11) (by decide)
    (by simp only [tabS, Nat.add_zero]; simp only [stride] at b12; omega_using [b12, sm]) fun s₃ u₃ =>
    wp_mov (op2_imm (by decide)) fun s₄ u₄ => WP.block_nil ?_)
  obtain I0 : TabInv n m (val32 s.mem base (slot n 8) (2 * n)) size expWords base s 0 s₄ := by
    refine ⟨(c₂.of_upd u₃ (by decide)).of_upd u₄ (by decide), fun j hj => absurd hj (Nat.not_lt_zero _),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [u₄.mem, u₃.mem, Y₂, Nat.pow_zero, Nat.one_mul]
    · rw [u₄.mem, u₃.mem]; exact B₂
    · rw [u₄.mem, u₃.mem]; exact E₂
    · rw [u₄.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₃.other _ (by decide)]; rfl
    · rw [u₄.gpr]; rfl
    · rw [u₄.mem, u₃.mem]
      exact (exponentRanges_op K₁.mem (by decide) (by decide)).trans (exponentRanges_op K₂.mem (by decide) (by decide))
    · exact ((K₁.rest.trans K₂.rest).mono (by decide)).trans ((u₃.rest (by decide)).trans (u₄.rest (by decide)))
  refine WP.loop (M := isa) (fun r u => ∃ i, r = 16 - i ∧ i < 16 ∧
      TabInv n m (val32 s.mem base (slot n 8) (2 * n)) size expWords base s i u) ?_ 16 s₄ ⟨0, rfl, by decide, I0⟩
  rintro r u ⟨i, rfl, hi, I⟩
  refine WP.mono (tableStep_ok hen I hi) fun t ⟨I', hz⟩ => ?_
  by_cases hi1 : i + 1 = 16
  · refine .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hi1]; rfl, I'.ctx, ?_, I'.exp, I'.mem,
      I'.rest⟩
    have T := I'.tab
    rw [hi1] at T
    exact T
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hi1]; rfl, 16 - (i + 1),
      by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-! ## A window -/

/-- The invariant of a window's squarings after `i` of them. -/
structure SqInv4 (n m y size : Nat) (base : Addr) (s : State) (i : Nat) (u : State) : Prop where
  ctx : Context n m base size u
  val : val32 u.mem base (slot n 9) (2 * n) = y ^ 2 ^ i * 2 ^ (64 * n) % m
  mem : Outs base (opRanges n 9) s.mem u.mem
  rest : Rest (.r11 :: dclob) s u
  r11 : u.gpr .r11 = BitVec.ofNat 32 (4 - i)

/-- The result to its sixteenth power. -/
theorem squareFour_ok {n size m y : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hy : val32 s.mem base (slot n 9) (2 * n) = y * 2 ^ (64 * n) % m) :
    WP isa (squareFour umaal n) s fun t => Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) = y ^ 2 ^ 4 * 2 ^ (64 * n) % m ∧
      Outs base (opRanges n 9) s.mem t.mem ∧ Rest (.r11 :: dclob) s t := by
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  unfold squareFour
  refine WP.seq (wp_mov (op2_imm (by decide)) fun t₁ u₁ => WP.block_nil ?_)
  have I0 : SqInv4 n m y size base s 0 t₁ :=
    ⟨h.of_upd u₁ (by decide), by rw [u₁.mem, hy, Nat.pow_zero, Nat.pow_one],
      by rw [u₁.mem]; exact Outs.refl _ _ _, u₁.rest (by decide), by rw [u₁.gpr]; rfl⟩
  refine WP.loop (M := isa) (fun r u => ∃ i, r = 4 - i ∧ i < 4 ∧ SqInv4 n m y size base s i u) ?_
    4 t₁ ⟨0, rfl, by decide, I0⟩
  rintro r u ⟨i, rfl, hi, I⟩
  have hv : val32 u.mem base (slot n 9) (2 * n) < m := by rw [I.val]; exact Nat.mod_lt _ hm0
  refine WP.seq (WP.mono (context_mul_ok I.ctx (o := 9) (a := 9) (b := 9) (by decide) (by decide) (by decide) hv)
    fun u₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  refine wp_subs (op2_imm (encodable_lt (n := 1) (by decide))) fun u₂ v₂ z₂ => WP.block_nil ?_
  have e : y ^ 2 ^ i * y ^ 2 ^ i = y ^ 2 ^ (i + 1) := by rw [← Nat.pow_add, Nat.pow_succ, Nat.mul_two]
  have I' : SqInv4 n m y size base s (i + 1) u₂ := by
    refine ⟨c₁.of_upd v₂ (by decide), ?_, ?_, ?_, ?_⟩
    · obtain v := VG.Proof.Dsa.mont_product h.coprime (a := y ^ 2 ^ i) (b := y ^ 2 ^ i)
        (by rw [I.val, Nat.mod_mod]) (by rw [I.val, Nat.mod_mod]) V₁
      rw [v₂.mem]
      rwa [Nat.mod_eq_of_lt lt₁, e] at v
    · rw [v₂.mem]; exact I.mem.trans K₁.mem
    · exact (I.rest.trans (K₁.rest.mono (by decide))).trans (v₂.rest (by decide))
    · rw [v₂.gpr, K₁.rest.gpr .r11 (by decide), I.r11, ofNat_sub_one (by omega_arith) (by omega_arith)]
      congr 1
  have hz : u₂.z = decide (i + 1 = 4) := by
    rw [z₂, K₁.rest.gpr .r11 (by decide), I.r11, ofNat_sub_one (by omega_arith) (by omega_arith),
      VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith
  by_cases hi1 : i + 1 = 4
  · refine .inl ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_true hi1]; rfl, I'.ctx, ?_, I'.mem, I'.rest⟩
    rw [I'.val, hi1]
  · exact .inr ⟨by rw [VG.Proof.X25519.Arm.eval_ne, hz, decide_eq_false hi1]; rfl, 4 - (i + 1),
      by omega_arith, i + 1, rfl, by omega_arith, I'⟩

/-- A window: the result is raised to its sixteenth power and multiplied by
the power `w` of the base, the exponent's top four bits, which are shifted out. -/
theorem windowStep_ok {n size m a P expWords k : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024) (T : Tab n m a 16 base s.mem)
    (hy : val32 s.mem base (slot n 9) (2 * n) = a ^ P * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .lr = BitVec.ofNat 32 k) :
    WP isa (windowStep umaal n expWords) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (k - 1) ∧ t.z = decide (k = 1) ∧ Context n m base size t ∧
      Tab n m a 16 base t.mem ∧
      (∃ w, val32 t.mem base (slot n 9) (2 * n) = a ^ (P * 16 + w) * 2 ^ (64 * n) % m ∧
        val32 t.mem base (slot n 11) expWords + w * 2 ^ (32 * expWords) =
          16 * val32 s.mem base (slot n 11) expWords) ∧
      Outs base (exponentRanges n) s.mem t.mem ∧ Rest (.r11 :: .lr :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have hn := h.n0
  have nw := h.ws.nowrap
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by omega_arith
  obtain b11 := slot_bound (n := n) (i := 11) (by decide)
  obtain st : stride n = 8 * n + 8 := rfl
  unfold windowStep scan
  refine WP.seq (WP.mono (squareFour_ok h hy) fun s₁ ⟨c₁, Y₁, O₁, R₁⟩ => ?_)
  obtain T₁ : Tab n m a 16 base s₁.mem := fun j hj => by
    rw [slot_val32 O₁ (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']
    exact T j hj
  obtain E₁ : val32 s₁.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords :=
    slot_val32 O₁ (by decide) hen (by decide) (by decide) (.inl (by decide)) nw'
  refine WP.seq (WP.mono (window_ok c₁.ws (n := n) (expWords := expWords) (by simp only [expS]; omega_arith)
    (by simp only [expS]; omega_arith) hew) fun s₂ ⟨w₂, O₂, cw, V₂, R₂⟩ => ?_)
  simp only [expS] at O₂ V₂
  obtain c₂ : Context n m base size s₂ := c₁.of_slot w₂ (O₂.mono (Nat.le_refl _) (by omega_arith)) (by decide)
  have keep₂ : ∀ {i q : Nat}, i ≠ 11 → i < 30 → 4 * q ≤ stride n →
      val32 s₂.mem base (slot n i) q = val32 s₁.mem base (slot n i) q := fun hi hi' hq =>
    slot_outside O₂ (by omega_arith) hi hq hi' sm
  obtain T₂ : Tab n m a 16 base s₂.mem := fun j hj => by
    rw [keep₂ (by omega_arith) (by omega_arith) (by omega_arith)]; exact T₁ j hj
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = (a ^ P) ^ 2 ^ 4 * 2 ^ (64 * n) % m := by
    rw [keep₂ (by decide) (by decide) (by omega_arith)]; exact Y₁
  obtain h2 : s₂.gpr .r2 = BitVec.ofNat 32 (s₂.gpr .r2).toNat :=
    BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (s₂.gpr .r2).isLt])
  refine WP.seq (WP.mono (scanFrom_ok (fun j => a ^ j * 2 ^ (64 * n) % m) hn sz sm cw 16 0 s₂ rfl w₂ h2
    (fun hlt => absurd hlt (Nat.not_lt_zero _)) (fun i _ hi => T₂ i hi)) fun s₃ ⟨w₃, S₃, O₃, R₃⟩ => ?_)
  obtain c₃ : Context n m base size s₃ := c₂.of_slot w₃ O₃ (by decide)
  have keep₃ : ∀ {i q : Nat}, i ≠ 10 → i < 30 → 4 * q ≤ stride n →
      val32 s₃.mem base (slot n i) q = val32 s₂.mem base (slot n i) q := fun hi hi' hq =>
    slot_outside O₃ (by omega_arith) hi hq hi' sm
  obtain Y₃ : val32 s₃.mem base (slot n 9) (2 * n) = (a ^ P) ^ 2 ^ 4 * 2 ^ (64 * n) % m := by
    rw [keep₃ (by decide) (by decide) (by omega_arith)]; exact Y₂
  refine WP.seq (WP.mono (context_mul_ok c₃ (o := 9) (a := 9) (b := 10) (by decide) (by decide) (by decide)
    (by rw [S₃]; exact Nat.mod_lt _ hm0)) fun s₄ ⟨c₄, K₄, lt₄, V₄⟩ => ?_)
  refine wp_subs (op2_imm (encodable_lt (n := 1) (by decide))) fun t u z => WP.block_nil ?_
  obtain l₄ : s₄.gpr .lr = BitVec.ofNat 32 k := by
    rw [K₄.rest.gpr _ (by decide), R₃.gpr _ (by decide), R₂.gpr _ (by decide), R₁.gpr _ (by decide)]; exact hc
  obtain e : (a ^ P) ^ 2 ^ 4 * a ^ (s₂.gpr .r2).toNat = a ^ (P * 16 + (s₂.gpr .r2).toNat) :=
    (by rw [← Nat.pow_mul, ← Nat.pow_add] :
      (a ^ P) ^ 2 ^ 4 * a ^ (s₂.gpr .r2).toNat = a ^ (P * 2 ^ 4 + (s₂.gpr .r2).toNat))
  refine ⟨by rw [u.gpr, l₄, ofNat_sub_one hk hk32], ?_, c₄.of_upd u (by decide), ?_,
    ⟨(s₂.gpr .r2).toNat, ?_, ?_⟩, ?_, ?_⟩
  · rw [z, l₄, ofNat_sub_one hk hk32, VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith
  · intro j hj
    rw [u.mem, K₄.val32 (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw',
      keep₃ (by omega_arith) (by omega_arith) (by omega_arith)]
    exact T₂ j hj
  · obtain v := VG.Proof.Dsa.mont_product h.coprime (a := (a ^ P) ^ 2 ^ 4) (b := a ^ (s₂.gpr .r2).toNat)
      (by rw [Y₃, Nat.mod_mod]) (by rw [S₃, Nat.mod_mod]) V₄
    rw [u.mem]
    rwa [Nat.mod_eq_of_lt lt₄, e] at v
  · rw [u.mem, K₄.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw',
      keep₃ (by decide) (by decide) (by omega_arith), Nat.mul_comm (s₂.gpr .r2).toNat, ← E₁]
    exact V₂
  · rw [u.mem]
    exact (((exponentRanges_op O₁ (by decide) (by decide)).trans
      (exponentRanges_of O₂ (by decide) (by decide) (by omega_arith))).trans
      (exponentRanges_of O₃ (by decide) (by decide) (by omega_arith))).trans
      (exponentRanges_op K₄.mem (by decide) (by decide))
  · exact (((R₁.mono (by decide)).trans (R₂.mono (by decide))).trans ((R₃.mono (by decide)).trans
      (K₄.rest.mono (by decide)))).trans (u.rest (by decide))

/-! ## The windows -/

/-- The invariant of the exponentiation's loop after `i` of its `steps`
windows: the result is the base to the power `P`, the exponent's bits shifted
out, with those left in the exponent. -/
structure ExponentInv (n size m expWords a E steps i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .lr = BitVec.ofNat 32 (steps - i)
  tab : Tab n m a 16 base t.mem
  value : ∃ P, val32 t.mem base (slot n 9) (2 * n) = a ^ P * 2 ^ (64 * n) % m ∧
    P * 2 ^ (32 * expWords) + val32 t.mem base (slot n 11) expWords = E * 16 ^ i
  mem : Outs base (exponentRanges n) s.mem t.mem
  rest : Rest (.r11 :: .lr :: dclob) s t

theorem exponentLoop_ok {n size m expWords a : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (T : Tab n m a 16 base s.mem) (hy : val32 s.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m)
    (hc : s.gpr .lr = BitVec.ofNat 32 (8 * expWords)) :
    WP isa (.loop (windowStep umaal n expWords) .ne) s
      (ExponentInv n size m expWords a (val32 s.mem base (slot n 11) expWords) (8 * expWords) (8 * expWords)
        base s) := by
  obtain hspos : 0 < 8 * expWords := by omega_arith
  obtain init : ExponentInv n size m expWords a (val32 s.mem base (slot n 11) expWords) (8 * expWords) 0
      base s s :=
    ⟨h, by simpa only [Nat.sub_zero] using hc, T, ⟨0, by rw [Nat.pow_zero, Nat.one_mul]; exact hy,
      by rw [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one]⟩, Outs.refl _ _ _, Rest.refl _ _⟩
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = 8 * expWords - i ∧ i < 8 * expWords ∧
      ExponentInv n size m expWords a (val32 s.mem base (slot n 11) expWords) (8 * expWords) i base s t)
    ?_ (8 * expWords) s ⟨0, rfl, hspos, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain ⟨P, Y, Q⟩ := I.value
  refine WP.mono (windowStep_ok I.context hen hew I.tab Y (by omega_arith) (by omega_arith) I.counter)
    fun u ⟨count, zf, C, T', ⟨w, Y', V'⟩, O, K⟩ => ?_
  obtain next : ExponentInv n size m expWords a (val32 s.mem base (slot n 11) expWords) (8 * expWords) (i + 1)
      base s u := by
    refine ⟨C, ?_, T', ⟨P * 16 + w, Y', ?_⟩, I.mem.trans O, I.rest.trans K⟩
    · rw [count, show 8 * expWords - i - 1 = 8 * expWords - (i + 1) by omega_arith]
    · rw [Nat.add_mul, Nat.mul_right_comm, Nat.pow_succ, ← Nat.mul_assoc]
      omega_using [V', Q]
  by_cases hdone : i + 1 = 8 * expWords
  · refine .inl ⟨?_, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_true (by omega_arith)]; rfl
    · rw [hdone] at next; exact next
  · refine .inr ⟨?_, 8 * expWords - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, next⟩
    rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_false (by omega_arith)]; rfl

theorem pow16 (e : Nat) : 16 ^ (8 * e) = 2 ^ (32 * e) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]
  exact congrArg (2 ^ ·) (by omega_arith)

/-- A number shifted up by its whole width has left it. -/
theorem shifted_out {P v E N : Nat} (hN : 0 < N) (hv : v < N) (Q : P * N + v = E * N) : P = E :=
  calc P = (v + P * N) / N := by rw [Nat.add_mul_div_right _ _ hN, Nat.div_eq_of_lt hv, Nat.zero_add]
    _ = E * N / N := by rw [Nat.add_comm, Q]
    _ = E := Nat.mul_div_cancel _ hN

/-- After the last window, every bit of the exponent is in the power. -/
theorem ExponentInv.finished {n size m expWords a E : Nat} {base : Addr} {s t : State}
    (I : ExponentInv n size m expWords a E (8 * expWords) (8 * expWords) base s t) :
    val32 t.mem base (slot n 9) (2 * n) = a ^ E * 2 ^ (64 * n) % m := by
  obtain ⟨P, Y, Q⟩ := I.value
  rw [pow16] at Q
  rw [Y, shifted_out (Nat.two_pow_pos _) (val32_lt t.mem base (slot n 11) expWords) Q]

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
      Outs base (exponentRanges n) s.mem t.mem ∧ Rest (.r11 :: .lr :: dclob) s t := by
  have sm := h.small
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold exponentiate
  refine WP.seq (WP.mono (table_ok h hen hone hr2) fun s₁ ⟨c₁, T₁, E₁, O₁, R₁⟩ => ?_)
  obtain one₁ : val32 s₁.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges_slot O₁ (.inr (.inl rfl)) (Nat.le_refl _) sm, hone]
  obtain rr₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [exponentRanges_slot O₁ (.inr (.inr rfl)) (Nat.le_refl _) sm, hr2]
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 9) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [one₁]; exact h.gt_one)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₂ (by rw [V₂, one₁, rr₁, Nat.mul_one, Nat.mod_mod])
  obtain T₂ : Tab n m (val32 s.mem base (slot n 8) (2 * n)) 16 base s₂.mem := fun j hj => by
    rw [K₂.val32 (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']
    exact T₁ j hj
  obtain E₂ : val32 s₂.mem base (slot n 11) expWords = val32 s.mem base (slot n 11) expWords := by
    rw [K₂.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw', E₁]
  obtain one₂ : val32 s₂.mem base (slot n 6) (2 * n) = 1 := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', one₁]
  refine WP.seq (wp_movw fun s₃ u₃ => WP.block_nil ?_)
  refine WP.seq (WP.mono (exponentLoop_ok (c₂.of_upd u₃ (by decide)) he hen hew
    (a := val32 s.mem base (slot n 8) (2 * n)) (by rw [u₃.mem]; exact T₂) (by rw [u₃.mem]; exact Y₂)
    (by rw [u₃.gpr, movw_ofNat (by omega_arith)])) fun s₄ I => ?_)
  obtain one₄ : val32 s₄.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges_slot I.mem (.inr (.inl rfl)) (Nat.le_refl _) sm, u₃.mem, one₂]
  refine WP.mono (context_mul_ok I.context (o := 9) (a := 9) (b := 6) (by decide) (by decide) (by decide)
    (by rw [one₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := val32 s₄.mem base (slot n 9) (2 * n))
      (out := val32 t.mem base (slot n 9) (2 * n)) h.coprime (by rw [I.finished, Nat.mod_mod]) (by rw [Vt, one₄])
    rw [Nat.mod_eq_of_lt ltt, u₃.mem, E₂] at v
    exact v
  · have o₃ : Outs base (exponentRanges n) s₂.mem s₃.mem := by rw [u₃.mem]; exact Outs.refl _ _ _
    exact (((O₁.trans (exponentRanges_op K₂.mem (by decide) (by decide))).trans o₃).trans I.mem).trans
      (exponentRanges_op Kt.mem (by decide) (by decide))
  · exact (((R₁.trans (K₂.rest.mono (by decide))).trans (u₃.rest (by decide))).trans I.rest).trans
      (Kt.rest.mono (by decide))

/-! ## A product of two powers

`exponentiate2 n expWords` writes
`[slot 9] = [slot 8]^[slot 11] · [slot 28]^[slot 29] mod m`
(`exponentiate2_ok`): the table's entry `4 i + j` is the second base to the
power `i` times the first to the power `j` (`tabv`, `table2_ok`), and each of
the `16 expWords` windows (`windowStep2_ok`) raises the result to its fourth
power and multiplies it by the entry of the exponents' top two bits. -/

/-- The value of the table's entry `j`. -/
def tabv (b1 b2 j : Nat) : Nat := b2 ^ (j / 4) * b1 ^ (j % 4)

theorem tabv_zero (b1 b2 : Nat) : tabv b1 b2 0 = 1 := by simp [tabv]

theorem tabv_one (b1 b2 : Nat) : tabv b1 b2 1 = b1 := by simp [tabv]

theorem tabv_four (b1 b2 : Nat) : tabv b1 b2 4 = b2 := by simp [tabv]

theorem tabv_mul {b1 b2 k a b : Nat} (h1 : a / 4 + b / 4 = k / 4) (h2 : a % 4 + b % 4 = k % 4) :
    tabv b1 b2 a * tabv b1 b2 b = tabv b1 b2 k := by
  simp only [tabv, ← h1, ← h2, Nat.pow_add]
  ac_rfl

/-- The entries `ops` computes are products of entries already there, `D`. -/
def opsOk : List (Nat × Nat × Nat) → List Nat → Bool
  | [], _ => true
  | (k, a, b) :: r, D =>
    decide (a ∈ D) && decide (b ∈ D) && decide (k < 16) && decide (a / 4 + b / 4 = k / 4) &&
      decide (a % 4 + b % 4 = k % 4) && opsOk r (k :: D)

/-- The entries there after `ops`. -/
def opsDone : List (Nat × Nat × Nat) → List Nat → List Nat
  | [], D => D
  | (k, _, _) :: r, D => opsDone r (k :: D)

theorem tableOps_all : ∀ j < 16, j ∈ opsDone tableOps [4, 1, 0] := by decide

theorem tableFill_ok {n size m b1 b2 : Nat} {base : Addr} :
    ∀ (ops : List (Nat × Nat × Nat)) (D : List Nat) (s : State), opsOk ops D = true → Context n m base size s →
    (∀ j ∈ D, j < 16 ∧ val32 s.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m) →
    WP isa (tableFill umaal n ops) s fun t => Context n m base size t ∧
      (∀ j ∈ opsDone ops D, val32 t.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m) ∧
      (∀ i k, (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → k ≤ 2 * n →
        val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k) ∧
      Outs base (exponentRanges2 n) s.mem t.mem ∧ Rest dclob s t
  | [], D, s, _, h, hD =>
    WP.block_nil ⟨h, fun j hj => (hD j hj).2, fun _ _ _ _ => rfl, Outs.refl _ _ _, Rest.refl _ _⟩
  | (k, a, b) :: r, D, s, ok, h, hD => by
    simp only [opsOk, Bool.and_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨⟨⟨⟨ha, hb⟩, hk⟩, h1⟩, h2⟩, okr⟩ := ok
    obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
    obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
    obtain ⟨a16, Va⟩ := hD a ha
    obtain ⟨b16, Vb⟩ := hD b hb
    rw [tableFill]
    refine WP.seq (WP.mono (context_mul_ok h (o := 12 + k) (a := 12 + a) (b := 12 + b) (by omega_arith)
      (by omega_arith) (by omega_arith) (by rw [Vb]; exact Nat.mod_lt _ hm0)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
    obtain new : val32 s₁.mem base (slot n (12 + k)) (2 * n) = tabv b1 b2 k * 2 ^ (64 * n) % m := by
      obtain v := VG.Proof.Dsa.mont_product h.coprime (a := tabv b1 b2 a) (b := tabv b1 b2 b)
        (by rw [Va, Nat.mod_mod]) (by rw [Vb, Nat.mod_mod]) V₁
      rwa [Nat.mod_eq_of_lt lt₁, tabv_mul h1 h2] at v
    refine WP.mono (tableFill_ok r (k :: D) s₁ okr c₁ (fun j hj => ?_)) fun t ⟨ct, T, Kp, O, R⟩ =>
      ⟨ct, T, fun i q hi hq => ?_, (exponentRanges2_op K₁.mem (by omega_arith) (by omega_arith)).trans O,
        K₁.rest.trans R⟩
    · by_cases e : j = k
      · rw [e]; exact ⟨hk, new⟩
      · obtain ⟨j16, Vj⟩ := hD j ((List.mem_cons.mp hj).resolve_left e)
        refine ⟨j16, ?_⟩
        rw [K₁.val32 (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']
        exact Vj
    · rw [Kp i q hi hq, K₁.val32 (by omega_arith) hq (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']

/-- The table of a product of two powers; the slots from 6 to 11 and the
second base's and exponent's keep their numbers. -/
theorem table2_ok {n size m : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hone : val32 s.mem base (slot n 6) (2 * n) = 1)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (table2 umaal n) s fun t => Context n m base size t ∧
      (∀ j < 16, val32 t.mem base (slot n (12 + j)) (2 * n) =
        tabv (val32 s.mem base (slot n 8) (2 * n)) (val32 s.mem base (slot n 28) (2 * n)) j * 2 ^ (64 * n) % m) ∧
      (∀ i k, (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → k ≤ 2 * n →
        val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k) ∧
      Outs base (exponentRanges2 n) s.mem t.mem ∧ Rest dclob s t := by
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold table2
  refine WP.seq (WP.mono (context_mul_ok h (o := 12) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [hone]; exact h.gt_one)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  obtain T0₁ : val32 s₁.mem base (slot n 12) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₁ (by rw [V₁, hone, hr2, Nat.mul_one, Nat.mod_mod])
  have k₁ : ∀ (i q : Nat), (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → q ≤ 2 * n →
      val32 s₁.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q hi hq =>
    K₁.val32 (by omega_arith) hq (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw'
  obtain rr₁ := (k₁ 7 (2 * n) (.inl (by decide)) (Nat.le_refl _)).trans hr2
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 13) (a := 8) (b := 7) (by decide) (by decide) (by decide)
    (by rw [rr₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain T1₂ : val32 s₂.mem base (slot n 13) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₂ (by rw [V₂, rr₁, k₁ 8 (2 * n) (.inl (by decide)) (Nat.le_refl _)])
  have k₂ : ∀ (i q : Nat), (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → q ≤ 2 * n →
      val32 s₂.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q hi hq =>
    (K₂.val32 (by omega_arith) hq (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw').trans (k₁ i q hi hq)
  obtain T0₂ : val32 s₂.mem base (slot n 12) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₂.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', T0₁]
  obtain rr₂ := (k₂ 7 (2 * n) (.inl (by decide)) (Nat.le_refl _)).trans hr2
  refine WP.seq (WP.mono (context_mul_ok c₂ (o := 16) (a := 28) (b := 7) (by decide) (by decide) (by decide)
    (by rw [rr₂]; exact Nat.mod_lt _ hm0)) fun s₃ ⟨c₃, K₃, lt₃, V₃⟩ => ?_)
  obtain T4₃ : val32 s₃.mem base (slot n 16) (2 * n) = val32 s.mem base (slot n 28) (2 * n) * 2 ^ (64 * n) % m :=
    mont_encode h.coprime lt₃ (by rw [V₃, rr₂, k₂ 28 (2 * n) (.inr (by decide)) (Nat.le_refl _)])
  have k₃ : ∀ (i q : Nat), (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → q ≤ 2 * n →
      val32 s₃.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q hi hq =>
    (K₃.val32 (by omega_arith) hq (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw').trans (k₂ i q hi hq)
  obtain T0₃ : val32 s₃.mem base (slot n 12) (2 * n) = 2 ^ (64 * n) % m := by
    rw [K₃.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', T0₂]
  obtain T1₃ : val32 s₃.mem base (slot n 13) (2 * n) = val32 s.mem base (slot n 8) (2 * n) * 2 ^ (64 * n) % m := by
    rw [K₃.val32 (by decide) (Nat.le_refl _) (by decide) (by decide) (.inl (by decide)) nw', T1₂]
  refine WP.mono (tableFill_ok (b1 := val32 s.mem base (slot n 8) (2 * n)) (b2 := val32 s.mem base (slot n 28) (2 * n))
    tableOps [4, 1, 0] s₃ (by decide) c₃ (fun j hj => ?_)) fun t ⟨ct, T, Kp, O, R⟩ =>
    ⟨ct, fun j hj => T j (tableOps_all j hj), fun i q hi hq => (Kp i q hi hq).trans (k₃ i q hi hq),
      (((exponentRanges2_op K₁.mem (by decide) (by decide)).trans
        (exponentRanges2_op K₂.mem (by decide) (by decide))).trans
        (exponentRanges2_op K₃.mem (by decide) (by decide))).trans O, ((K₁.rest.trans K₂.rest).trans K₃.rest).trans R⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl
  · exact ⟨by decide, by rw [tabv_four]; exact T4₃⟩
  · exact ⟨by decide, by rw [tabv_one]; exact T1₃⟩
  · exact ⟨by decide, by rw [tabv_zero, Nat.one_mul]; exact T0₃⟩

/-- `r2 = 4 w₂ + w₁`, the top two bits of the second exponent and of the
first, which are shifted out; every other slot keeps its numbers. -/
theorem window2_ok {n size m expWords : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024) :
    WP isa (window2 n expWords) s fun t => Context n m base size t ∧
      (∃ w1 w2, w1 < 4 ∧ w2 < 4 ∧ t.gpr .r2 = BitVec.ofNat 32 (4 * w2 + w1) ∧
        val32 t.mem base (slot n 11) expWords + w1 * 2 ^ (32 * expWords) =
          4 * val32 s.mem base (slot n 11) expWords ∧
        val32 t.mem base (slot n 29) expWords + w2 * 2 ^ (32 * expWords) =
          4 * val32 s.mem base (slot n 29) expWords) ∧
      (∀ i q, i ≠ 11 → i ≠ 29 → i < 30 → 4 * q ≤ stride n →
        val32 t.mem base (slot n i) q = val32 s.mem base (slot n i) q) ∧
      Outs base (exponentRanges2 n) s.mem t.mem ∧ Rest [.r1, .r2, .r4, .r5, .r6] s t := by
  have sz := h.size_le
  have sm := h.small
  obtain b11 := slot_bound (n := n) (i := 11) (by decide)
  obtain b29 := slot_bound (n := n) (i := 29) (by decide)
  obtain st : stride n = 8 * n + 8 := rfl
  unfold window2
  refine WP.seq (WP.mono (windowTwo_ok h.ws (E := exp2S n) (expWords := expWords) (by simp only [exp2S]; omega_arith)
    (by simp only [exp2S]; omega_arith) hew) fun s₁ ⟨w₁, O₁, c₁, V₁, R₁⟩ => ?_)
  simp only [exp2S] at O₁ V₁
  obtain x₁ := h.of_slot w₁ (O₁.mono (Nat.le_refl _) (by omega_arith)) (by decide)
  refine WP.seq (VG.Proof.X25519.Arm.wp_mov (VG.Proof.X25519.Arm.op2_lsl (by decide)) fun s₂ u₂ => WP.block_nil ?_)
  obtain x₂ := x₁.of_upd u₂ (by decide)
  refine WP.seq (WP.mono (windowTwo_ok x₂.ws (E := expS n) (expWords := expWords) (by simp only [expS]; omega_arith)
    (by simp only [expS]; omega_arith) hew) fun s₃ ⟨w₃, O₃, c₃, V₃, R₃⟩ => ?_)
  simp only [expS] at O₃ V₃
  obtain x₃ := x₂.of_slot w₃ (O₃.mono (Nat.le_refl _) (by omega_arith)) (by decide)
  refine VG.Proof.X25519.Arm.wp_dp (VG.Proof.X25519.Arm.op2_reg _ _) fun t u₄ => WP.block_nil ?_
  have keep : ∀ i q, i ≠ 11 → i ≠ 29 → i < 30 → 4 * q ≤ stride n →
      val32 t.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q h11 h29 hi hq => by
    rw [u₄.mem, slot_outside O₃ (by omega_arith) h11 hq hi sm, u₂.mem, slot_outside O₁ (by omega_arith) h29 hq hi sm]
  obtain e6 : s₃.gpr .r6 = s₁.gpr .r2 <<< 2 := by rw [R₃.gpr _ (by decide), u₂.gpr]
  obtain r2 : (t.gpr .r2).toNat = (s₁.gpr .r2).toNat % 2 ^ 30 * 2 ^ 2 + (s₃.gpr .r2).toNat := by
    rw [u₄.gpr, VG.Proof.X25519.Arm.dpVal, e6, carry_word2 _ _ c₃]
  refine ⟨x₃.of_upd u₄ (by decide), ⟨(s₃.gpr .r2).toNat, (s₁.gpr .r2).toNat, c₃, c₁, ?_, ?_, ?_⟩, keep, ?_, ?_⟩
  · apply BitVec.eq_of_toNat_eq
    rw [r2, BitVec.toNat_ofNat]
    omega_using [c₁, c₃]
  · rw [u₄.mem, Nat.mul_comm (s₃.gpr .r2).toNat, V₃, u₂.mem,
      slot_outside O₁ (by omega_arith) (by decide) (by omega_arith) (by decide) sm]
  · rw [u₄.mem, slot_outside O₃ (by omega_arith) (by decide) (by omega_arith) (by decide) sm, u₂.mem,
      Nat.mul_comm (s₁.gpr .r2).toNat, V₁]
  · rw [u₄.mem]
    refine (exponentRanges2_of O₁ (by decide) (by decide) (by omega_arith)).trans ?_
    rw [← u₂.mem]
    exact exponentRanges2_of O₃ (by decide) (by decide) (by omega_arith)
  · exact (((R₁.mono (by decide)).trans (u₂.rest (by decide))).trans (R₃.mono (by decide))).trans (u₄.rest (by decide))

theorem pow4 (y : Nat) : y ^ 4 = y * y * (y * y) := by
  rw [show (4 : Nat) = 2 + 2 from rfl, Nat.pow_add, Nat.pow_two]

theorem joint_step (b1 b2 P1 P2 w1 w2 : Nat) :
    (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1) * ((b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1)) * (b2 ^ w2 * b1 ^ w1) =
      b2 ^ (P2 * 4 + w2) * b1 ^ (P1 * 4 + w1) := by
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_mul, Nat.pow_mul, pow4, pow4]
  ac_rfl

/-- A window of both exponents. -/
theorem windowStep2_ok {n size m b1 b2 P1 P2 expWords k : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (T : ∀ j < 16, val32 s.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m)
    (hy : val32 s.mem base (slot n 9) (2 * n) = (b2 ^ P2 * b1 ^ P1) * 2 ^ (64 * n) % m)
    (hk : 0 < k) (hk32 : k < 2 ^ 32) (hc : s.gpr .lr = BitVec.ofNat 32 k) :
    WP isa (windowStep2 umaal n expWords) s fun t =>
      t.gpr .lr = BitVec.ofNat 32 (k - 1) ∧ t.z = decide (k = 1) ∧ Context n m base size t ∧
      (∀ j < 16, val32 t.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m) ∧
      (∃ w1 w2, val32 t.mem base (slot n 9) (2 * n) =
          (b2 ^ (P2 * 4 + w2) * b1 ^ (P1 * 4 + w1)) * 2 ^ (64 * n) % m ∧
        val32 t.mem base (slot n 11) expWords + w1 * 2 ^ (32 * expWords) =
          4 * val32 s.mem base (slot n 11) expWords ∧
        val32 t.mem base (slot n 29) expWords + w2 * 2 ^ (32 * expWords) =
          4 * val32 s.mem base (slot n 29) expWords) ∧
      Outs base (exponentRanges2 n) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  have sz := h.size_le
  have sm := h.small
  have hn := h.n0
  obtain hm0 : 0 < m := by have := h.gt_one; omega_arith
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; omega_arith
  obtain st : stride n = 8 * n + 8 := rfl
  unfold windowStep2 scan
  refine WP.seq (WP.mono (context_mul_ok h (o := 9) (a := 9) (b := 9) (by decide) (by decide) (by decide)
    (by rw [hy]; exact Nat.mod_lt _ hm0)) fun s₁ ⟨c₁, K₁, lt₁, V₁⟩ => ?_)
  obtain Y₁ : val32 s₁.mem base (slot n 9) (2 * n) =
      (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1) * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product h.coprime (a := b2 ^ P2 * b1 ^ P1) (b := b2 ^ P2 * b1 ^ P1)
      (by rw [hy, Nat.mod_mod]) (by rw [hy, Nat.mod_mod]) V₁
    rwa [Nat.mod_eq_of_lt lt₁] at v
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 9) (a := 9) (b := 9) (by decide) (by decide) (by decide)
    (by rw [Y₁]; exact Nat.mod_lt _ hm0)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) =
      (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1) * ((b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1)) * 2 ^ (64 * n) % m := by
    obtain v := VG.Proof.Dsa.mont_product h.coprime (a := (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1))
      (b := (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1)) (by rw [Y₁, Nat.mod_mod]) (by rw [Y₁, Nat.mod_mod]) V₂
    rwa [Nat.mod_eq_of_lt lt₂] at v
  have keep₂ : ∀ (i q : Nat), i ≠ 9 → 6 ≤ i → i < 30 → q ≤ 2 * n →
      val32 s₂.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q h9 h6 hi hq => by
    rw [K₂.val32 hi hq h9 (by omega_arith) (.inl h6) nw', K₁.val32 hi hq h9 (by omega_arith) (.inl h6) nw']
  refine WP.seq (WP.mono (window2_ok c₂ hen hew) fun s₃ ⟨c₃, ⟨w1, w2, hw1, hw2, r2, E1, E2⟩, keep₃, O₃, R₃⟩ => ?_)
  refine WP.seq (WP.mono (scanFrom_ok (fun j => tabv b1 b2 j * 2 ^ (64 * n) % m) hn sz sm
    (show 4 * w2 + w1 < 16 by omega_arith) 16 0 s₃ rfl c₃.ws r2 (fun hlt => absurd hlt (Nat.not_lt_zero _))
    (fun i _ hi => by
      rw [keep₃ (12 + i) (2 * n) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith),
        keep₂ (12 + i) (2 * n) (by omega_arith) (by omega_arith) (by omega_arith) (Nat.le_refl _)]
      exact T i hi)) fun s₄ ⟨w₄, S₄, O₄, R₄⟩ => ?_)
  obtain c₄ : Context n m base size s₄ := c₃.of_slot w₄ O₄ (by decide)
  have keep₄ : ∀ (i q : Nat), i ≠ 10 → i < 30 → 4 * q ≤ stride n →
      val32 s₄.mem base (slot n i) q = val32 s₃.mem base (slot n i) q := fun i q hi hi' hq =>
    slot_outside O₄ (by omega_arith) hi hq hi' sm
  obtain Y₄ : val32 s₄.mem base (slot n 9) (2 * n) =
      (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1) * ((b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1)) * 2 ^ (64 * n) % m := by
    rw [keep₄ 9 (2 * n) (by decide) (by decide) (by omega_arith),
      keep₃ 9 (2 * n) (by decide) (by decide) (by decide) (by omega_arith)]
    exact Y₂
  obtain S₄' : val32 s₄.mem base (slot n 10) (2 * n) = (b2 ^ w2 * b1 ^ w1) * 2 ^ (64 * n) % m := by
    rw [S₄, tabv, show (4 * w2 + w1) / 4 = w2 by omega_arith, show (4 * w2 + w1) % 4 = w1 by omega_arith]
  refine WP.seq (WP.mono (context_mul_ok c₄ (o := 9) (a := 9) (b := 10) (by decide) (by decide) (by decide)
    (by rw [S₄']; exact Nat.mod_lt _ hm0)) fun s₅ ⟨c₅, K₅, lt₅, V₅⟩ => ?_)
  refine wp_subs (op2_imm (encodable_lt (n := 1) (by decide))) fun t u z => WP.block_nil ?_
  obtain l₅ : s₅.gpr .lr = BitVec.ofNat 32 k := by
    rw [K₅.rest.gpr _ (by decide), R₄.gpr _ (by decide), R₃.gpr _ (by decide), K₂.rest.gpr _ (by decide),
      K₁.rest.gpr _ (by decide)]
    exact hc
  have keep₅ : ∀ (i q : Nat), i ≠ 9 → i ≠ 10 → i ≠ 11 → i ≠ 29 → 6 ≤ i → i < 30 → q ≤ 2 * n →
      val32 t.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q h9 h10 h11 h29 h6 hi hq => by
    rw [u.mem, K₅.val32 hi hq h9 (by omega_arith) (.inl h6) nw', keep₄ i q h10 hi (by omega_arith),
      keep₃ i q h11 h29 hi (by omega_arith), keep₂ i q h9 h6 hi hq]
  refine ⟨by rw [u.gpr, l₅, ofNat_sub_one hk hk32], ?_, c₅.of_upd u (by decide), ?_, ⟨w1, w2, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [z, l₅, ofNat_sub_one hk hk32, VG.Proof.X25519.Arm.ofNat_beq_zero (by omega_arith)]
    simp only [decide_eq_decide]
    omega_arith
  · intro j hj
    rw [keep₅ (12 + j) (2 * n) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith) (by omega_arith)
      (by omega_arith) (Nat.le_refl _)]
    exact T j hj
  · obtain v := VG.Proof.Dsa.mont_product h.coprime
      (a := (b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1) * ((b2 ^ P2 * b1 ^ P1) * (b2 ^ P2 * b1 ^ P1)))
      (b := b2 ^ w2 * b1 ^ w1) (by rw [Y₄, Nat.mod_mod]) (by rw [S₄', Nat.mod_mod]) V₅
    rw [u.mem]
    rwa [Nat.mod_eq_of_lt lt₅, joint_step] at v
  · rw [u.mem, K₅.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw',
      keep₄ 11 expWords (by decide) (by decide) (by omega_arith), E1,
      keep₂ 11 expWords (by decide) (by decide) (by decide) hen]
  · rw [u.mem, K₅.val32 (by decide) hen (by decide) (by decide) (.inl (by decide)) nw',
      keep₄ 29 expWords (by decide) (by decide) (by omega_arith), E2,
      keep₂ 29 expWords (by decide) (by decide) (by decide) hen]
  · rw [u.mem]
    exact ((((exponentRanges2_op K₁.mem (by decide) (by decide)).trans
      (exponentRanges2_op K₂.mem (by decide) (by decide))).trans O₃).trans
      (exponentRanges2_of O₄ (by decide) (by decide) (by omega_arith))).trans
      (exponentRanges2_op K₅.mem (by decide) (by decide))
  · exact ((((K₁.rest.trans K₂.rest).mono (by decide)).trans (R₃.mono (by decide))).trans
      ((R₄.mono (by decide)).trans (K₅.rest.mono (by decide)))).trans (u.rest (by decide))

/-- The invariant of the loop after `i` of its windows, as `ExponentInv`,
for both exponents. -/
structure JointInv (n size m expWords b1 b2 E1 E2 steps i : Nat) (base : Addr) (s t : State) : Prop where
  context : Context n m base size t
  counter : t.gpr .lr = BitVec.ofNat 32 (steps - i)
  tab : ∀ j < 16, val32 t.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m
  value : ∃ P1 P2, val32 t.mem base (slot n 9) (2 * n) = (b2 ^ P2 * b1 ^ P1) * 2 ^ (64 * n) % m ∧
    P1 * 2 ^ (32 * expWords) + val32 t.mem base (slot n 11) expWords = E1 * 4 ^ i ∧
    P2 * 2 ^ (32 * expWords) + val32 t.mem base (slot n 29) expWords = E2 * 4 ^ i
  mem : Outs base (exponentRanges2 n) s.mem t.mem
  rest : Rest (.lr :: dclob) s t

theorem jointLoop_ok {n size m expWords b1 b2 : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (T : ∀ j < 16, val32 s.mem base (slot n (12 + j)) (2 * n) = tabv b1 b2 j * 2 ^ (64 * n) % m)
    (hy : val32 s.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m)
    (hc : s.gpr .lr = BitVec.ofNat 32 (16 * expWords)) :
    WP isa (.loop (windowStep2 umaal n expWords) .ne) s
      (JointInv n size m expWords b1 b2 (val32 s.mem base (slot n 11) expWords)
        (val32 s.mem base (slot n 29) expWords) (16 * expWords) (16 * expWords) base s) := by
  obtain hspos : 0 < 16 * expWords := by omega_arith
  obtain init : JointInv n size m expWords b1 b2 (val32 s.mem base (slot n 11) expWords)
      (val32 s.mem base (slot n 29) expWords) (16 * expWords) 0 base s s :=
    ⟨h, by simpa only [Nat.sub_zero] using hc, T, ⟨0, 0, by rw [Nat.pow_zero, Nat.pow_zero, Nat.one_mul]; exact hy,
      by rw [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one],
      by rw [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, Nat.mul_one]⟩, Outs.refl _ _ _, Rest.refl _ _⟩
  refine WP.loop (M := isa)
    (fun k t => ∃ i, k = 16 * expWords - i ∧ i < 16 * expWords ∧
      JointInv n size m expWords b1 b2 (val32 s.mem base (slot n 11) expWords)
        (val32 s.mem base (slot n 29) expWords) (16 * expWords) i base s t)
    ?_ (16 * expWords) s ⟨0, rfl, hspos, init⟩
  rintro k t ⟨i, rfl, hi, I⟩
  obtain ⟨P1, P2, Y, Q1, Q2⟩ := I.value
  refine WP.mono (windowStep2_ok I.context hen hew I.tab Y (by omega_arith) (by omega_arith) I.counter)
    fun u ⟨count, zf, C, T', ⟨w1, w2, Y', V1, V2⟩, O, K⟩ => ?_
  obtain next : JointInv n size m expWords b1 b2 (val32 s.mem base (slot n 11) expWords)
      (val32 s.mem base (slot n 29) expWords) (16 * expWords) (i + 1) base s u := by
    refine ⟨C, ?_, T', ⟨P1 * 4 + w1, P2 * 4 + w2, Y', ?_, ?_⟩, I.mem.trans O, I.rest.trans K⟩
    · rw [count, show 16 * expWords - i - 1 = 16 * expWords - (i + 1) by omega_arith]
    · rw [Nat.add_mul, Nat.mul_right_comm, Nat.pow_succ, ← Nat.mul_assoc]
      omega_using [V1, Q1]
    · rw [Nat.add_mul, Nat.mul_right_comm, Nat.pow_succ, ← Nat.mul_assoc]
      omega_using [V2, Q2]
  by_cases hdone : i + 1 = 16 * expWords
  · refine .inl ⟨?_, ?_⟩
    · rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_true (by omega_arith)]; rfl
    · rw [hdone] at next; exact next
  · refine .inr ⟨?_, 16 * expWords - (i + 1), by omega_arith, i + 1, rfl, by omega_arith, next⟩
    rw [VG.Proof.X25519.Arm.eval_ne, zf, decide_eq_false (by omega_arith)]; rfl

theorem pow4_16 (e : Nat) : 4 ^ (16 * e) = 2 ^ (32 * e) := by
  rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_mul]
  exact congrArg (2 ^ ·) (by omega_arith)

/-- `[slot 9] = [slot 8]^[slot 11] · [slot 28]^[slot 29] mod m`, the exponents
`expWords` words, from one in slot 6 and `R² mod m` in slot 7. -/
theorem exponentiate2_ok {n size m expWords : Nat} {base : Addr} {s : State}
    (h : Context n m base size s) (he : 0 < expWords) (hen : expWords ≤ 2 * n) (hew : expWords ≤ 1024)
    (hone : val32 s.mem base (slot n 6) (2 * n) = 1)
    (hr2 : val32 s.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m) :
    WP isa (exponentiate2 umaal n expWords) s fun t =>
      Context n m base size t ∧
      val32 t.mem base (slot n 9) (2 * n) =
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) expWords *
          val32 s.mem base (slot n 28) (2 * n) ^ val32 s.mem base (slot n 29) expWords % m ∧
      Outs base (exponentRanges2 n) s.mem t.mem ∧ Rest (.lr :: dclob) s t := by
  have sm := h.small
  obtain nw' : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega_arith
  unfold exponentiate2
  refine WP.seq (WP.mono (table2_ok h hone hr2) fun s₁ ⟨c₁, T₁, Kp₁, O₁, R₁⟩ => ?_)
  obtain one₁ : val32 s₁.mem base (slot n 6) (2 * n) = 1 := by
    rw [Kp₁ 6 (2 * n) (.inl (by decide)) (Nat.le_refl _), hone]
  obtain rr₁ : val32 s₁.mem base (slot n 7) (2 * n) = 2 ^ (128 * n) % m := by
    rw [Kp₁ 7 (2 * n) (.inl (by decide)) (Nat.le_refl _), hr2]
  refine WP.seq (WP.mono (context_mul_ok c₁ (o := 9) (a := 7) (b := 6) (by decide) (by decide) (by decide)
    (by rw [one₁]; exact h.gt_one)) fun s₂ ⟨c₂, K₂, lt₂, V₂⟩ => ?_)
  obtain Y₂ : val32 s₂.mem base (slot n 9) (2 * n) = 2 ^ (64 * n) % m :=
    mont_one h.coprime lt₂ (by rw [V₂, one₁, rr₁, Nat.mul_one, Nat.mod_mod])
  have keep₂ : ∀ (i q : Nat), (6 ≤ i ∧ i < 12) ∨ (28 ≤ i ∧ i < 30) → i ≠ 9 → q ≤ 2 * n →
      val32 s₂.mem base (slot n i) q = val32 s.mem base (slot n i) q := fun i q hi h9 hq => by
    rw [K₂.val32 (by omega_arith) hq h9 (by omega_arith) (.inl (by omega_arith)) nw', Kp₁ i q hi hq]
  refine WP.seq (wp_movw fun s₃ u₃ => WP.block_nil ?_)
  refine WP.seq (WP.mono (jointLoop_ok (c₂.of_upd u₃ (by decide)) he hen hew
    (b1 := val32 s.mem base (slot n 8) (2 * n)) (b2 := val32 s.mem base (slot n 28) (2 * n))
    (fun j hj => by
      rw [u₃.mem, K₂.val32 (by omega_arith) (Nat.le_refl _) (by omega_arith) (by omega_arith) (.inl (by omega_arith)) nw']
      exact T₁ j hj)
    (by rw [u₃.mem]; exact Y₂) (by rw [u₃.gpr, movw_ofNat (by omega_arith)])) fun s₄ I => ?_)
  obtain one₄ : val32 s₄.mem base (slot n 6) (2 * n) = 1 := by
    rw [exponentRanges2_slot I.mem (.inr (.inl rfl)) (Nat.le_refl _) sm, u₃.mem,
      keep₂ 6 (2 * n) (.inl (by decide)) (by decide) (Nat.le_refl _), hone]
  obtain fin : val32 s₄.mem base (slot n 9) (2 * n) =
      (val32 s.mem base (slot n 28) (2 * n) ^ val32 s.mem base (slot n 29) expWords *
        val32 s.mem base (slot n 8) (2 * n) ^ val32 s.mem base (slot n 11) expWords) * 2 ^ (64 * n) % m := by
    obtain ⟨P1, P2, Y, Q1, Q2⟩ := I.value
    rw [pow4_16] at Q1 Q2
    rw [Y, shifted_out (Nat.two_pow_pos _) (val32_lt s₄.mem base (slot n 11) expWords) Q1,
      shifted_out (Nat.two_pow_pos _) (val32_lt s₄.mem base (slot n 29) expWords) Q2, u₃.mem,
      keep₂ 11 expWords (.inl (by decide)) (by decide) hen, keep₂ 29 expWords (.inr (by decide)) (by decide) hen]
  refine WP.mono (context_mul_ok I.context (o := 9) (a := 9) (b := 6) (by decide) (by decide) (by decide)
    (by rw [one₄]; exact h.gt_one)) fun t ⟨ct, Kt, ltt, Vt⟩ => ⟨ct, ?_, ?_, ?_⟩
  · have v := VG.Proof.Dsa.mont_decode (A := val32 s₄.mem base (slot n 9) (2 * n))
      (out := val32 t.mem base (slot n 9) (2 * n)) h.coprime (by rw [fin, Nat.mod_mod]) (by rw [Vt, one₄])
    rw [Nat.mod_eq_of_lt ltt,
      Nat.mul_comm (val32 s.mem base (slot n 28) (2 * n) ^ val32 s.mem base (slot n 29) expWords)] at v
    exact v
  · have o₃ : Outs base (exponentRanges2 n) s₂.mem s₃.mem := by rw [u₃.mem]; exact Outs.refl _ _ _
    exact (((O₁.trans (exponentRanges2_op K₂.mem (by decide) (by decide))).trans o₃).trans I.mem).trans
      (exponentRanges2_op Kt.mem (by decide) (by decide))
  · exact ((((R₁.mono (by decide)).trans (K₂.rest.mono (by decide))).trans (u₃.rest (by decide))).trans I.rest).trans
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

variable {umaal : Bool}

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

theorem body_noCalls (n : Nat) : (body umaal n).noCalls = true := by
  cases umaal <;> rfl

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
    WP isa (Impl.Dsa.Arm.Context.call umaal n) s fun t => Context n m base size t ∧
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
    (O₂ : val32 s₂.mem base (modS n) (2 * n) % 2 = 1) (M₂ : 1 < val32 s₂.mem base (modS n) (2 * n))
    (T : val32 s₁.mem base (modS n) (2 * n) = val32 s₂.mem base (modS n) (2 * n)) :
    SameTrace isa (Impl.Dsa.Arm.Context.call umaal n) s₁ s₂ := by
  have nothing : ∀ a b : State, VG.Arm.Taint.Agree (Taint.ofRegs []) a b :=
    fun _ _ => Taint.agree_ofRegs fun _ h => nomatch h
  unfold Impl.Dsa.Arm.Context.call
  refine SameTrace.seq (SameTrace.of_relCT
    (erased_relCT (τ := Taint.ofRegs []) (σ := Taint.ofRegs [])
      (c₀ := .block [.mov .r4 (.reg .r12), .mov .r0 (.reg .r12), .movw .r1 0])
      (.block []) rfl (Taint.noBase_ofRegs _) (by decide)) (nothing _ _))
    (head_ok n) (head_ok n) fun u₁ u₂ ⟨_, h0₁, h1₁, R₁, H₁⟩ ⟨_, h0₂, h1₂, R₂, H₂⟩ => ?_
  refine SameTrace.of_relCT (P := fun a b => a = u₁ ∧ b = u₂) (RelCT.seq
    (RelCT.call (setupK_correct hn hn48) (setupK_ct n hn hn48) [] [⟨base, contextBytes n⟩] ?_)
    ((relCT_of_check (τ := Taint.ofRegs []) (σ := Taint.ofRegs []) (h := .block []) (by decide)).mono
      (fun _ _ _ => nothing _ _) fun _ _ _ => trivial)) ⟨rfl, rfl⟩
  rintro a b ⟨rfl, rfl⟩
  have b₁ : State.addr (a.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0₁, W₁.wb]
  have b₂ : State.addr (b.callEntry.gpr .r0) = base := by rw [State.callEntry_gpr _ (by decide), h0₂, W₂.wb]
  refine ⟨entry_pre W₁ Z₁ hn48 h0₁ h1₁ H₁ O₁ M₁, entry_pre W₂ Z₂ hn48 h0₂ h1₂ H₂ O₂ M₂, ⟨?_, ?_⟩,
    Covers.right (Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁), Pow.covers_ctx (W₁.of_rest R₁ (by decide)) Z₁,
    Covers.right (Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂), Pow.covers_ctx (W₂.of_rest R₂ (by decide)) Z₂⟩
  · simp only [State.withRegions_gpr]
    rw [State.callEntry_gpr _ (by decide), State.callEntry_gpr _ (by decide), h0₁, h0₂]
    exact BitVec.eq_of_toNat_eq (by rw [W₁.wb_toNat, W₂.wb_toNat])
  · simp only [State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, b₁, b₂, H₁, H₂]
    exact T

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

theorem exponent_scratch (n : Nat) :
    ∀ r ∈ exponentRanges n, ∃ r' ∈ scratch n, r'.1 ≤ r.1 ∧ r.1 + r.2 ≤ r'.1 + r'.2 :=
  within_scratch (by
    simp only [exponentRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
      contextBytes, slot, stride]
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
    exact (O₂'.trans (outs_within O₃ (setup_scratch hn))).trans (outs_within O₄ (exponent_scratch n))
  · rw [← slots_regs] at hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx12 := slots_r12 x hx
    have hw := slots_words _ (List.mem_map_of_mem (f := fun x => (x.2, 4)) hx)
    simp only at hw
    rw [L x hx,
      outs_readW O₄ (by
        simp only [exponentRanges, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
          and_true, slot, stride]
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
of `r1` words, and the numbers as `val32` reads them. Its time may depend on
the modulus, as its context's does (`Context.setupK`). -/
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
  pub s t := s.gpr .r0 = t.gpr .r0 ∧
    val32 s.mem (State.addr (s.gpr .r0)) (slot n 0) (2 * n) = val32 t.mem (State.addr (t.gpr .r0)) (slot n 0) (2 * n)

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
    (T : val32 s₁.mem base (modS n) (2 * n) = val32 s₂.mem base (modS n) (2 * n))
    (H : RelCT isa (VG.Arm.Taint.Agree (wsT false false)) rest (fun _ _ => True)) :
    SameTrace isa (.seq (.block save) (.seq (Impl.Dsa.Arm.Context.call umaal n) rest)) s₁ s₂ := by
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
    (by rw [mod Q₂]; exact O₂) (by rw [mod Q₂]; exact M₂) (by rw [mod Q₁, mod Q₂]; exact T))
    (Context.call_ok W₁ Z₁ hn hn48 rfl (by rw [mod Q₁]; exact M₁) (by rw [mod Q₁]; exact O₁))
    (Context.call_ok W₂ Z₂ hn hn48 rfl (by rw [mod Q₂]; exact M₂) (by rw [mod Q₂]; exact O₂))
    fun v₁ v₂ ⟨C₁, _⟩ ⟨C₂, _⟩ => ?_
  exact SameTrace.of_relCT H (VG.Arm.Taint.agree_ofRegs fun r hr => by
    simp only [wsRegs, Bool.false_eq_true, ↓reduceIte, List.nil_append, List.mem_singleton] at hr
    subst r
    exact BitVec.eq_of_toNat_eq (by rw [C₁.ws.wb_toNat, C₂.ws.wb_toNat]))

theorem powK_ct (n e : Nat) (hn : 0 < n) (hn48 : n ≤ 48) :
    ConstantTime isa (powK n e).pre (powK n e).pub (body umaal n e) := by
  refine SameTrace.constantTime fun s₁ s₂ h₁ h₂ ⟨Eq, T⟩ => ?_
  have E : ∀ {s : State}, (powK n e).pre s → Entry s (State.addr (s.gpr .r0)) ((s.gpr .r1).toNat * 8) := by
    intro s H
    exact ⟨rfl, ⟨_, Nat.le_refl _, by have := H.2.2.1; omega_arith, by rw [H.2.1]; simp⟩,
      by simpa only [VG.Proof.X25519.Arm.addr_toNat] using H.2.2.1⟩
  have E₂ : Entry s₂ (State.addr (s₁.gpr .r0)) ((s₂.gpr .r1).toNat * 8) := by rw [Eq]; exact E h₂
  unfold body
  refine savedSetup_trace (E h₁) E₂ h₁.2.2.2.1 h₂.2.2.2.1 hn hn48
    h₁.2.2.2.2.1 h₁.2.2.2.2.2 ?_ ?_ ?_ ?_
  · rw [Eq]; exact h₂.2.2.2.2.1
  · rw [Eq]; exact h₂.2.2.2.2.2
  · rw [← Eq] at T; exact T
  · refine RelCT.seq (exponentiate_relCT n e) ?_
    exact (relCT_of_check (σ := VG.Arm.Taint.ofRegs []) (h := .block []) (by decide)).mono (fun _ _ h => h)
      fun _ _ _ => trivial

end VG.Proof.Dsa.Arm.Pow
