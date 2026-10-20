module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Mont.Words32

/-! # The window's exponent words: their top four bits, and the arithmetic of their shift -/

@[expose] public section
namespace VG.Proof.Mont.X86.Dynamic
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Proof.Mont
open VG.Proof.Mont.X86

theorem times16_toNat (x : BitVec 32) :
    ((((x + x) + (x + x)) + ((x + x) + (x + x))) + (((x + x) + (x + x)) + ((x + x) + (x + x)))).toNat =
      x.toNat * 16 % 2 ^ 32 := by
  simp only [BitVec.toNat_add]
  omega

theorem shr28_toNat (x : BitVec 32) : (x >>> 28).toNat = x.toNat / 2 ^ 28 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `(V + P w) · 16 mod P 2³²`, for `V < P`: the low part times 16 mod `P`, and
the top word times 16 mod 2³² with the four bits carried up from below. -/
theorem shift_top {V P w : Nat} (hP : 0 < P) (hV : V < P) :
    (V + P * w) * 16 % (P * 2 ^ 32) = V * 16 % P + P * (w * 16 % 2 ^ 32 + V * 16 / P) := by
  have hq : V * 16 / P < 16 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  have split : V * 16 = V * 16 % P + P * (V * 16 / P) := (Nat.mod_add_div _ _).symm
  have hx : V * 16 % P < P := Nat.mod_lt _ hP
  generalize V * 16 % P = x at split hx ⊢
  generalize V * 16 / P = q at split hq ⊢
  have e' : ∀ r d, r + 2 ^ 32 * d = q + w * 16 → (V + P * w) * 16 = x + P * r + P * 2 ^ 32 * d := by
    intro r d hd
    rw [Nat.add_mul, split, Nat.mul_assoc P w 16, Nat.add_assoc, ← Nat.mul_add, ← hd, Nat.mul_add,
      Nat.mul_assoc P (2 ^ 32), Nat.add_assoc]
  have e := e' _ _ (Nat.mod_add_div (q + w * 16) (2 ^ 32))
  have lt : x + P * ((q + w * 16) % 2 ^ 32) < P * 2 ^ 32 := by
    have hm : (q + w * 16) % 2 ^ 32 + 1 ≤ 2 ^ 32 := Nat.mod_lt _ (by decide)
    have := Nat.mul_le_mul_left P hm
    rw [Nat.mul_add, Nat.mul_one] at this
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt lt]
  congr 2
  omega

theorem val32_top_bits (m : Mem) (base : Addr) (d j : Nat) :
    val32 m base d (j + 1) * 16 / 2 ^ (32 * (j + 1)) = w32 m base (d + 4 * j) / 2 ^ 28 := by
  have hP : 0 < 2 ^ (32 * j) := Nat.two_pow_pos _
  have hV := val32_lt m base d j
  have hq : val32 m base d j * 16 / 2 ^ (32 * j) < 16 := (Nat.div_lt_iff_lt_mul hP).2 (by omega)
  rw [val32_succ, pow32_succ, Nat.mul_comm (2 ^ 32), ← Nat.div_div_eq_div_mul, Nat.add_mul,
    Nat.mul_assoc, Nat.add_mul_div_left _ _ hP]
  generalize val32 m base d j * 16 / 2 ^ (32 * j) = q at hq
  omega

/-- The top four bits of the `k`-word number at `exp`, into the window word. -/
theorem topWindow_ok {s : State} {base : Addr} {size exp k : Nat} (hs : Scr s base size)
    (hk : 0 < k) (he : exp + 4 * k ≤ size) (hw : 8 ≤ size) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.topWindow exp k)) s fun t =>
      Outside base 4 4 s.mem t.mem ∧
      w32 t.mem base 4 = val32 s.mem base exp k * 16 / 2 ^ (32 * k) ∧
      Keeps [.eax] s t := by
  have hn := hs.nowrap
  unfold VG.Impl.Mont.X86.Dynamic.topWindow VG.Impl.Mont.X86.Dynamic.windowOffset
  refine wp_movS (readSrc_sc hs (d := exp + 4 * (k - 1)) (by omega)) fun s₁ u₁ _ => ?_
  refine wp_shr (by decide) fun s₂ u₂ _ => ?_
  have k₂ : Keeps [.eax] s s₂ := (u₁.keeps.mono (by decide)).widen u₂.keeps
  have hs₂ := hs.of_keeps k₂ (by decide)
  refine wp_storeS (hs₂.ea (by omega)) (hs₂.write (d := 4) (by omega)) fun t mt =>
    WP.block_nil ⟨?_, ?_, k₂.trans (mt.keeps _)⟩
  · rw [mt.mem, u₂.mem, u₁.mem]
    exact writeW32_outside _ _ _ (by omega)
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [mt.mem, w32_write_self, u₂.gpr, u₁.gpr, shr28_toNat, Nat.add_sub_cancel, val32_top_bits]

/-- The exponent's next window, from its top bits. -/
theorem window_exponent (X P : Nat) (hP : 0 < P) : X * 16 / P = 16 * (X / P) + X % P * 16 / P := by
  have e : X * 16 = X % P * 16 + P * (16 * (X / P)) := by
    have := Nat.mod_add_div X P
    calc X * 16 = (X % P + P * (X / P)) * 16 := by rw [this]
      _ = _ := by rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (X / P) 16]
  rw [e, Nat.add_mul_div_left _ _ hP, Nat.add_comm]

theorem window_power (b c w : Nat) : (b ^ c) ^ 16 * b ^ w = b ^ (16 * c + w) := by
  rw [← Nat.pow_mul, ← Nat.pow_add, Nat.mul_comm c 16]

/-- `8k` windows cover the exponent. -/
theorem window_all (E k : Nat) : E * 16 ^ (8 * k) / 2 ^ (32 * k) = E := by
  rw [show (16 : Nat) ^ (8 * k) = 2 ^ (32 * k) by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_mul]; congr 1; omega]
  exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)

end VG.Proof.Mont.X86.Dynamic
