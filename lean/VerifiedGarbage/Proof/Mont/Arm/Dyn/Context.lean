module

public import VerifiedGarbage.Impl.Mont.Arm.Context
public import VerifiedGarbage.Proof.Mont.Arm.Dyn.Mul
import VerifiedGarbage.Proof.Mont.Arm.Dyn.Ops
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Runtime-modulus Montgomery arithmetic on 32-bit ARM: the context

The working space's slots (`slot_le`, `slot_sep`), the context of a modulus
`m` (`Context`: the modulus in slot 0 and `m'` in the header), what an
operation on its slots keeps (`OpKeep`), and the multiplication and addition
of slots 6 to 11 (`context_mul_ok`, `context_add_ok`).
-/

@[expose] public section

namespace VG.Proof.Mont.Arm.Dyn

open VG VG.Arm VG.Impl.Mont VG.Impl.Mont.Arm VG.Impl.Mont.Arm.Dynamic VG.Proof.Mont VG.Proof.Mont.Arm
open VG.Proof.X25519.Arm (Rest)

theorem slot_le {n i j : Nat} (h : i < j) : slot n i + stride n ≤ slot n j := by
  have := Nat.mul_le_mul_right (stride n) h
  simp only [slot, Nat.succ_mul] at *
  omega

theorem slot_bound {n i : Nat} (h : i < 12) : slot n i + stride n ≤ contextBytes n := slot_le h

theorem slot_sep {n i j : Nat} (h : i ≠ j) :
    slot n i + stride n ≤ slot n j ∨ slot n j + stride n ≤ slot n i := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · exact .inl (slot_le h)
  · exact .inr (slot_le h)

theorem slot_header (n i : Nat) : 256 ≤ slot n i := by unfold slot; omega

/-- The accumulator's four slots. -/
theorem slot_acc (n : Nat) : slot n 6 = slot n 2 + 4 * stride n := by simp only [slot]; omega

theorem contextMod_words (n : Nat) : words (contextMod n) = 2 * n := rfl

/-- The context of the modulus `m`: in slot 0 of the working space, with
`m' = -m⁻¹ mod 2¹⁶` in the header, and the working space's offsets below
`2¹⁶`. -/
structure Context (n m : Nat) (base : Addr) (size : Nat) (s : State) : Prop where
  ws : Ws s base size
  size_le : contextBytes n ≤ size
  small : contextBytes n < 2 ^ 16
  n0 : 0 < n
  modulus : val32 s.mem base (slot n 0) (2 * n) = m
  gt_one : 1 < m
  inverse : (m * w32 s.mem base invO + 1) % 2 ^ 16 = 0

/-- The memory an operation on slot `o` may change: the slot, the temporary
slot and the accumulator. -/
abbrev opRanges (n o : Nat) : List (Nat × Nat) := [(slot n o, 8 * n), (slot n 1, 8 * n), (slot n 2, 4 * (8 * n + 2))]

/-- What an operation writing slot `o` keeps: the registers but `dclob`, the
regions, and the memory but `opRanges n o`. -/
structure OpKeep (n : Nat) (base : Addr) (o : Nat) (s t : State) : Prop where
  rest : Rest dclob s t
  mem : Outs base (opRanges n o) s.mem t.mem

/-- The layout of an operation on slots 6 to 11. -/
theorem context_lay {n size o a b : Nat} (hs : contextBytes n ≤ size) (h16 : contextBytes n < 2 ^ 16)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12) :
    MulLayD (contextMod n) size invO (accS n) (slot n o) (slot n a) (slot n b) := by
  have b0 := slot_le (n := n) (i := 0) (j := 1) (by decide)
  have b1 := slot_le (n := n) (i := 1) (j := 2) (by decide)
  have b5 := slot_le (n := n) (i := 5) (j := 6) (by decide)
  have b2 := slot_le (n := n) (i := 2) (j := 5) (by decide)
  have bo := slot_bound (n := n) ho.2
  have ba := slot_bound (n := n) ha.2
  have bb := slot_bound (n := n) hb.2
  have lo := slot_le (n := n) (i := 5) (j := o) (by omega)
  have la := slot_le (n := n) (i := 5) (j := a) (by omega)
  have lb := slot_le (n := n) (i := 5) (j := b) (by omega)
  have hd := slot_header n 0
  simp only [stride] at *
  have e6 : slot n 6 = slot n 2 + 4 * (8 * n + 8) := by simp only [slot, stride]; omega
  have e5 : slot n 6 = slot n 5 + (8 * n + 8) := by simp only [slot, stride]; omega
  constructor <;> (try simp only [accLen, digits, Impl.Mont.Arm.words, contextMod, accS, modS, tmpS, invO]) <;> omega

theorem slot_val32 {n o i k : Nat} {base : Addr} {s t : State} (K : Outs base (opRanges n o) s.mem t.mem)
    (hi : i < 12) (hk : k ≤ 2 * n) (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : 6 ≤ i ∨ i = 0)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k := by
  have so := slot_sep (n := n) hio
  have st := slot_sep (n := n) hi1
  have bi := slot_bound (n := n) hi
  have l6 := slot_le (n := n) (i := 5) (j := 6) (by decide)
  have l2 := slot_le (n := n) (i := 2) (j := 5) (by decide)
  have h0 := slot_le (n := n) (i := 0) (j := 2) (by decide)
  have l6i : 6 ≤ i → slot n 6 ≤ slot n i := fun h => by
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := slot_le (n := n) h; omega
    · rw [h]
  simp only [stride] at *
  have e6 : slot n 6 = slot n 2 + 4 * (8 * n + 8) := by simp only [slot, stride]; omega
  apply K.val32
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hi2 with hi2 | rfl
    · have := l6i hi2
      rcases hr with rfl | rfl | rfl <;> omega
    · rcases hr with rfl | rfl | rfl <;> omega
  · omega

theorem OpKeep.val32 {n o i k : Nat} {base : Addr} {s t : State} (K : OpKeep n base o s t)
    (hi : i < 12) (hk : k ≤ 2 * n) (hio : i ≠ o) (hi1 : i ≠ 1) (hi2 : 6 ≤ i ∨ i = 0)
    (hn : base.toNat + contextBytes n ≤ 2 ^ 32) :
    val32 t.mem base (slot n i) k = val32 s.mem base (slot n i) k :=
  slot_val32 K.mem hi hk hio hi1 hi2 hn

theorem Context.keep {n size m o : Nat} {base : Addr} {s t : State} (h : Context n m base size s) (ho0 : o ≠ 0)
    (w : Ws t base size) (K : OpKeep n base o s t) : Context n m base size t := by
  have nw : base.toNat + contextBytes n ≤ 2 ^ 32 := by have := h.ws.nowrap; have := h.size_le; omega
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [K.val32 (by decide) (Nat.le_refl _) (Ne.symm ho0) (by decide) (.inr rfl) nw]; exact h.modulus
  · have hv : val32 t.mem base 0 1 = val32 s.mem base 0 1 := by
      apply K.mem.val32
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        have h0 := slot_header n o
        have h1 := slot_header n 1
        have h2 := slot_header n 2
        rcases hr with rfl | rfl | rfl <;> omega
      · decide
    have e : w32 t.mem base invO = w32 s.mem base invO := by
      simpa only [val32, Nat.mul_zero, Nat.add_zero, invO] using hv
    rw [e]; exact h.inverse

/-- A context, after code that changed only a slot from 6 on. -/
theorem Context.of_slot {n size m i : Nat} {base : Addr} {s t : State} (h : Context n m base size s)
    (w : Ws t base size) (O : Outside base (slot n i) (8 * n) s.mem t.mem) (hi : 6 ≤ i) :
    Context n m base size t := by
  have nw := h.ws.nowrap
  have b0 := slot_bound (n := n) (i := 0) (by decide)
  have l0 := slot_le (n := n) (i := 0) (j := i) (by omega)
  have hd := slot_header n 0
  have sz := h.size_le
  simp only [stride] at *
  refine ⟨w, h.size_le, h.small, h.n0, ?_, h.gt_one, ?_⟩
  · rw [O.val32 (by omega) (by omega)]; exact h.modulus
  · rw [O.w32 (by simp only [invO]; omega) (by decide)]; exact h.inverse

theorem context_mul_ok {n size m o a b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12)
    (hB : val32 s.mem base (slot n b) (2 * n) < m) :
    WP isa (Dynamic.mul (contextMod n) invO (accS n) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep n base o s t ∧
      val32 t.mem base (slot n o) (2 * n) < m ∧
      val32 t.mem base (slot n o) (2 * n) * 2 ^ (64 * n) % m =
        val32 s.mem base (slot n a) (2 * n) * val32 s.mem base (slot n b) (2 * n) % m := by
  refine WP.mono (mul_ok h.ws h.n0 (context_lay h.size_le h.small ho ha hb) (m := m) h.modulus h.inverse hB)
    fun t ⟨w, lt, V, O, R⟩ => ?_
  have K : OpKeep n base o s t := ⟨R, by
    simpa only [Impl.Mont.Arm.words, contextMod, tmpS, accS, show 4 * (2 * n) = 8 * n by omega,
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega] using O⟩
  exact ⟨h.keep (by omega) w K, K, lt, by rw [show 64 * n = 32 * (2 * n) by omega]; exact V⟩

theorem context_add_ok {n size m o a b : Nat} {base : Addr} {s : State} (h : Context n m base size s)
    (ho : 6 ≤ o ∧ o < 12) (ha : 6 ≤ a ∧ a < 12) (hb : 6 ≤ b ∧ b < 12)
    (hA : val32 s.mem base (slot n a) (2 * n) < m) (hB : val32 s.mem base (slot n b) (2 * n) < m) :
    WP isa (addD (contextMod n) (accS n) (slot n o) (slot n a) (slot n b)) s fun t =>
      Context n m base size t ∧ OpKeep n base o s t ∧
      val32 t.mem base (slot n o) (2 * n) =
        (val32 s.mem base (slot n a) (2 * n) + val32 s.mem base (slot n b) (2 * n)) % m := by
  refine WP.mono (addD_ok h.ws h.n0 (context_lay h.size_le h.small ho ha hb) (m := m) h.modulus
    (by have := h.gt_one; omega) hA hB) fun t ⟨w, V, O, R⟩ => ?_
  have K : OpKeep n base o s t := ⟨R, by
    simpa only [Impl.Mont.Arm.words, contextMod, tmpS, accS, show 4 * (2 * n) = 8 * n by omega,
      show 4 * (4 * (2 * n) + 2) = 4 * (8 * n + 2) by omega] using O⟩
  exact ⟨h.keep (by omega) w K, K, V⟩

end VG.Proof.Mont.Arm.Dyn
