module

public import VerifiedGarbage.Impl.Mont.X86.Window
public import VerifiedGarbage.Proof.Mont.X86.Instr

/-! # The window's exponent words: shifting four bits up, and the top four bits -/

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

/-- Four doublings of a word, with the top four bits of the word below. -/
theorem shiftUpWord_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size)
    (out : Nat) (lowest : Bool) (ho : out + 4 ≤ size) (hl : lowest = false → 4 ≤ out) :
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftUpWord out lowest)) s fun t =>
      Outside base out 4 s.mem t.mem ∧
      w32 t.mem base out = w32 s.mem base out * 16 % 2 ^ 32 +
        (if lowest then 0 else w32 s.mem base (out - 4) / 2 ^ 28) ∧
      Keeps [.eax, .edx] s t := by
  have hn := hs.nowrap
  have code : VG.Impl.Mont.X86.Dynamic.shiftUpWord out lowest =
      .mov .edx (.mem (sc out)) :: .alu .add .edx (.reg .edx) :: .alu .add .edx (.reg .edx) ::
      .alu .add .edx (.reg .edx) :: .alu .add .edx (.reg .edx) ::
      ((if lowest then [] else
        [.mov .eax (.mem (sc (out - 4))), .shift .shr .eax 28, .alu .add .edx (.reg .eax)]) ++
      [.store (sc out) .edx]) := rfl
  rw [code]
  refine wp_movS (readSrc_sc hs ho) fun s₁ u₁ _ => ?_
  refine wp_addS rfl fun s₂ u₂ _ => ?_
  refine wp_addS rfl fun s₃ u₃ _ => ?_
  refine wp_addS rfl fun s₄ u₄ _ => ?_
  refine wp_addS rfl fun s₅ u₅ _ => ?_
  have k₅ : Keeps [.eax, .edx] s s₅ :=
    ((((u₁.keeps.mono (by decide)).widen u₂.keeps).widen u₃.keeps).widen u₄.keeps).widen u₅.keeps
  have hs₅ := hs.of_keeps k₅ (by decide)
  have mem₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have edx₅ : (s₅.gpr .edx).toNat = w32 s.mem base out * 16 % 2 ^ 32 := by
    rw [u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, times16_toNat]
  cases lowest with
  | true =>
    simp only [↓reduceIte, List.nil_append]
    refine wp_storeS (hs₅.ea (by omega)) (hs₅.write ho) fun t mt => WP.block_nil ⟨?_, ?_, k₅.trans (mt.keeps _)⟩
    · rw [mt.mem, mem₅]
      exact writeW32_outside _ _ _ (by omega)
    · rw [mt.mem, w32_write_self, edx₅]
      rfl
  | false =>
    have h4 := hl rfl
    simp only [Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]
    refine wp_movS (readSrc_sc hs₅ (d := out - 4) (by omega)) fun s₆ u₆ _ => ?_
    refine wp_shr (by decide) fun s₇ u₇ _ => ?_
    refine wp_addS rfl fun s₈ u₈ _ => ?_
    have k₈ : Keeps [.eax, .edx] s s₈ := ((k₅.widen u₆.keeps).widen u₇.keeps).widen u₈.keeps
    have hs₈ := hs.of_keeps k₈ (by decide)
    refine wp_storeS (hs₈.ea (by omega)) (hs₈.write ho) fun t mt => WP.block_nil ⟨?_, ?_, k₈.trans (mt.keeps _)⟩
    · rw [mt.mem, u₈.mem, u₇.mem, u₆.mem, mem₅]
      exact writeW32_outside _ _ _ (by omega)
    · have eax₇ : (s₇.gpr .eax).toNat = w32 s.mem base (out - 4) / 2 ^ 28 := by
        rw [u₇.gpr, u₆.gpr, shr28_toNat, mem₅]
      have edx₇ : s₇.gpr .edx = s₅.gpr .edx := by
        rw [u₇.other _ (by decide), u₆.other _ (by decide)]
      rw [mt.mem, w32_write_self, u₈.gpr, BitVec.toNat_add, edx₇, edx₅, eax₇]
      have : w32 s.mem base (out - 4) < 2 ^ 32 := (s.mem.readW (off base (out - 4)) 32).isLt
      omega

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

/-- The `k` words at `exp` times 16, modulo their width. -/
theorem shiftUp_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) :
    ∀ k exp, exp + 4 * k ≤ size →
    WP isa (.block (VG.Impl.Mont.X86.Dynamic.shiftUp k exp)) s fun t =>
      Outside base exp (4 * k) s.mem t.mem ∧
      val32 t.mem base exp k = val32 s.mem base exp k * 16 % 2 ^ (32 * k) ∧
      Keeps [.eax, .edx] s t
  | 0, exp, _ => WP.block_nil ⟨Outside.refl _ _ _ _, by simp only [val32, Nat.zero_mul, Nat.zero_mod],
      Keeps.refl _ _⟩
  | k + 1, exp, he => by
    have hn := hs.nowrap
    rw [VG.Impl.Mont.X86.Dynamic.shiftUp]
    refine WP.block_append (WP.mono (shiftUpWord_ok hs (exp + 4 * k) (k == 0) (by omega)
      (fun h => by have : k ≠ 0 := by intro e; subst e; contradiction
                   omega)) fun s₁ ⟨O₁, V₁, K₁⟩ => ?_)
    have hs₁ := hs.of_keeps K₁ (by decide)
    refine WP.mono (shiftUp_ok hs₁ k exp (by omega)) fun t ⟨O₂, V₂, K₂⟩ => ?_
    refine ⟨(O₁.mono (o' := exp) (n' := 4 * (k + 1)) (by omega) (by omega)).trans
      (O₂.mono (o' := exp) (n' := 4 * (k + 1)) (by omega) (by omega)), ?_, K₁.trans K₂⟩
    have low : val32 s₁.mem base exp k = val32 s.mem base exp k := O₁.val32 (by omega) (by omega)
    have top : w32 t.mem base (exp + 4 * k) = w32 s₁.mem base (exp + 4 * k) := O₂.w32 (by omega) (by omega)
    have carry : (if (k == 0) = true then 0 else w32 s.mem base (exp + 4 * k - 4) / 2 ^ 28) =
        val32 s.mem base exp k * 16 / 2 ^ (32 * k) := by
      cases k with
      | zero => simp only [val32, Nat.zero_mul, Nat.zero_div, beq_self_eq_true, ite_true]
      | succ j =>
        simp only [show (j + 1 == 0) = false from rfl, Bool.false_eq_true, ite_false]
        rw [val32_top_bits, show exp + 4 * (j + 1) - 4 = exp + 4 * j by omega]
    rw [val32_succ, val32_succ, V₂, low, top, V₁, carry, pow32_succ, Nat.mul_comm (2 ^ 32),
      shift_top (Nat.two_pow_pos _) (val32_lt _ _ _ _)]

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

end VG.Proof.Mont.X86.Dynamic
