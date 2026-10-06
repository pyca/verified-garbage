import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.TCB.AArch64.Isa

/-!
# RSA encryption on AArch64: bytes, one at a time

What the byte loops of RSAES-PKCS1-v1_5 (and OAEP) need: a byte load and a
byte store at a register (`exec_ldrb0`, `exec_strb0`), a byte written to
memory (`write1_apply`), and a loop that runs a down-counter from `n` to
zero (`count_loop`).
-/

namespace VG.AArch64.Bytes

open VG

theorem read1 (m : Mem) (a : Addr) : (m.read a 1).setWidth 32 = (m a).setWidth 32 := by
  simp only [Mem.read]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft,
    Nat.zero_or]

/-- `ldrb wt, [n]`. -/
theorem exec_ldrb0 {s : State} {t n : Reg} (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 0) 1) :
    exec (.ldrb t n 0) s = some (s.write .w t ((s.mem (s.gpr n)).setWidth 32)) := by
  have h' : InRegions (s.rd ++ s.wr) (s.gpr n + 0#64) 1 := h
  simp only [exec, addr, Nat.mod_one, and_self, show (0 : Nat) < 4096 * 1 from by decide, ite_true,
    Option.bind_some, State.load, BitVec.add_zero]
  simp only [BitVec.add_zero] at h'
  simp only [h', ite_true, Option.map_some, read1]

/-- `strb wt, [n]`. -/
theorem exec_strb0 {s : State} {t n : Reg} (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 0) 1) :
    exec (.strb t n 0) s = some { s with mem := s.mem.write (s.gpr n) 1 ((s.gpr t).setWidth 8) } := by
  have h' : InRegions s.wr (s.gpr n + 0#64) 1 := h
  simp only [exec, addr, Nat.mod_one, show (0 : Nat) < 4096 * 1 from by decide, and_self, ite_true,
    Option.bind_some, State.store]
  simp only [BitVec.add_zero] at h' ⊢
  simp only [h', ite_true, State.read, Size.bits, BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 32 by decide)]

/-- A byte written to memory. -/
theorem write1_apply (m : Mem) (a x : Addr) (v : BitVec (8 * 1)) :
    m.write a 1 v x = if x = a then v else m x := by
  simp only [Mem.write]
  by_cases hx : x = a
  · subst hx; simp
  · have : (x - a).toNat ≠ 0 := fun h => hx (by
      have := BitVec.eq_of_toNat_eq (x := x - a) (y := 0) (by simpa using h)
      rw [← BitVec.sub_add_cancel x a, this]; exact BitVec.zero_add _)
    simp only [hx, ite_false]
    exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

/-- A byte of the `n` bytes at `p`, from memory written elsewhere. -/
theorem write1_ne (m : Mem) {a x : Addr} (v : BitVec (8 * 1)) (h : x ≠ a) : m.write a 1 v x = m x := by
  rw [write1_apply, ite_eq_right_iff.mpr fun e => absurd e h]

theorem write1_self (m : Mem) (a : Addr) (v : BitVec (8 * 1)) : m.write a 1 v a = v := by
  rw [write1_apply, ite_eq_left_iff.mpr fun e => absurd rfl e]

theorem eval_nonzero (s : State) (r : Reg) : isa.eval (.nonzero .x r) s = some (s.gpr r != 0) := by
  show eval (.nonzero .x r) s = _
  simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]

/-- A down-counter in `cr`: after `k` of `n` iterations it is `n - k`. -/
theorem count_loop {body : Prog isa} {cr : Reg} {n : Nat} (hn : 0 < n) (I : Nat → State → Prop)
    (hstep : ∀ k < n, ∀ s, I k s →
      WP isa body s fun s' => I (k + 1) s' ∧ (s'.gpr cr != 0) = decide (k + 1 ≠ n))
    {s : State} (h0 : I 0 s) : WP isa (.loop body (.nonzero .x cr)) s (I n) := by
  refine WP.loop (M := isa) (fun m s => ∃ k, m = n - k ∧ k < n ∧ I k s) ?_ n s ⟨0, by omega, hn, h0⟩
  rintro m s ⟨k, rfl, hk, hi⟩
  refine WP.mono (hstep k hk s hi) fun s' ⟨hi', hc⟩ => ?_
  have hz : isa.eval (.nonzero .x cr) s' = some (decide (k + 1 ≠ n)) := by rw [eval_nonzero, hc]
  by_cases hl : k + 1 = n
  · refine .inl ⟨by rw [hz]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [hz]; simp [hl], n - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-- The counter after one more iteration. -/
theorem counter_step {n k : Nat} (hk : k < n) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 (n - k) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (n - (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show n - k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show n - (k + 1) < 2 ^ 64 by omega),
    show (1 : Nat) % 2 ^ 64 = 1 from rfl]
  rw [show 2 ^ 64 - 1 + (n - k) = (n - (k + 1)) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- Whether the counter is zero. -/
theorem counter_ne {n k : Nat} (hk : k + 1 ≤ n) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 (n - (k + 1)) != 0) = decide (k + 1 ≠ n) := by
  have : BitVec.ofNat 64 (n - (k + 1)) = 0 ↔ k + 1 = n := by
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    · intro h; rw [h, Nat.sub_self]; rfl
  by_cases h : k + 1 = n
  · simp [h]
  · have h' : ¬ BitVec.ofNat 64 (n - (k + 1)) = 0 := fun e => h (this.mp e)
    rw [decide_eq_true h, bne_iff_ne]
    exact h'

/-- A word read apart from a write. -/
theorem readW_write_sep {m : Mem} {a b : Addr} {w k : Nat} {v : BitVec (8 * k)} (h : Mem.Sep a (w / 8) b k)
    (hn : w / 8 < 2 ^ 64) : (m.write b k v).readW a w = m.readW a w := by
  simp only [Mem.readW, Mem.read_write_sep h hn]

/-- A byte apart from a write. -/
theorem byte_write_sep {m : Mem} {x b : Addr} {k : Nat} {v : BitVec (8 * k)} (h : Mem.Sep x 1 b k) :
    m.write b k v x = m x :=
  Mem.write_apply (h x (by simp))

theorem byte_writeW_sep {m : Mem} {x b : Addr} {w : Nat} {v : BitVec w} (h : Mem.Sep x 1 b (w / 8)) :
    m.writeW b v x = m x :=
  byte_write_sep h

/-- `movz xd, #imm`. -/
theorem exec_movz_x (s : State) (d : Reg) (imm : BitVec 16) :
    exec (.movz .x d imm 0) s = some (s.write .x d (imm.setWidth 64)) := by
  simp only [exec, Size.bits, Nat.mul_zero, show (0 : Nat) < 64 from by decide, ite_true,
    BitVec.shiftLeft_zero]

theorem read_one (m : Mem) (a : Addr) : m.read a 1 = m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [Mem.read, BitVec.toNat_append, BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]

/-- A byte, zero-extended to 32 bits and then to 64. -/
theorem byte64 (b : Byte) : BitVec.setWidth 64 (BitVec.setWidth 32 b) = b.setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

/-- A byte, zero-extended and truncated back. -/
theorem byte_rt (b : Byte) :
    BitVec.setWidth 8 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 b))) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

theorem byte_rt64 (b : Byte) : BitVec.setWidth 8 (BitVec.setWidth 32 (b.setWidth 64)) = b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have := b.isLt
  omega

/-- `x - 1`'s borrow, by `x + NOT(x) + C` after `subs` of 1: all ones exactly
when `x` is zero. -/
theorem borrow (x : BitVec 64) :
    x + ~~~x + BitVec.ofNat 64 (decide (2 ^ 64 ≤ x.toNat + (~~~(1 : BitVec 64)).toNat + 1)).toNat =
      if x = 0 then BitVec.allOnes 64 else 0 := by
  have h1 : (~~~(1 : BitVec 64)).toNat = 2 ^ 64 - 2 := by rw [BitVec.toNat_not]; rfl
  have hn : x + ~~~x = BitVec.allOnes 64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_allOnes]
    have := x.isLt
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [hn, h1]
  by_cases hx : x = 0
  · subst hx
    simp
  · have : 1 ≤ x.toNat := by
      rcases Nat.eq_zero_or_pos x.toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hx
      · exact h
    rw [decide_eq_true (by omega)]
    simp only [hx, ite_false]
    decide

theorem setWidth64_eq_zero (b : Byte) : b.setWidth 64 = 0 ↔ b = 0 := by
  constructor
  · intro h
    bv_omega
  · intro h; subst h; rfl

theorem rotateRight_zero (x : BitVec 64) : x.rotateRight 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- `ldr xt, [sp, #off]`. -/
theorem exec_ldrSp {s : State} {t : Reg} {off : Nat} (ho : off % 8 = 0 ∧ off < 32768)
    (h : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 off) 8) :
    exec (.ldrSp t off) s = some (s.write .x t (s.mem.readW (s.sp + BitVec.ofNat 64 off) 64)) := by
  simp only [exec, ho, and_self, ite_true, State.load, h, Option.map_some, Mem.readW, Nat.reduceDiv]

end VG.AArch64.Bytes
