import VerifiedGarbage.Proof.Mont.X86.Instr

/-!
# Montgomery arithmetic on x86 (32-bit): a multiply-accumulate step

`mulStep acc b j` adds `ecx · b_j` and the carry `ebx` to the word of the
accumulator at `[ebp + acc + 4j]`, and leaves the carry word in `ebx`
(`mulStep_ok`): `x = c b_j + k + t` is below `2⁶⁴`, its low word is stored
and its high word is the carry.
-/

namespace VG.Proof.Mont.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Proof.Mont

/-- The sum of a step fits two words. -/
theorem step_lt {c b k t : Nat} (hc : c < 2 ^ 32) (hb : b < 2 ^ 32) (hk : k < 2 ^ 32) (ht : t < 2 ^ 32) :
    c * b + k + t < 2 ^ 64 := by
  have : c * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem ofBool_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 32).toNat = c.toNat := by
  cases c <;> rfl

/-- The registers of a step: `edx:eax = A C`, then `+ K` and `+ T` with the
carries into `edx`, are the low and high words of `C A + K + T`. -/
theorem step_regs (A C K T : BitVec 32) (c3 c5 : Bool)
    (hc3 : c3 = decide (2 ^ 32 ≤ (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat + K.toNat))
    (hc5 : c5 = decide (2 ^ 32 ≤ (BitVec.ofNat 32 (A.toNat * C.toNat) + K).toNat + T.toNat)) :
    (BitVec.ofNat 32 (A.toNat * C.toNat) + K + T).toNat = (C.toNat * A.toNat + K.toNat + T.toNat) % 2 ^ 32 ∧
    (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32) + 0 + (BitVec.ofBool c3).setWidth 32 + 0 +
      (BitVec.ofBool c5).setWidth 32).toNat = (C.toNat * A.toNat + K.toNat + T.toNat) / 2 ^ 32 := by
  obtain ⟨hw, hq⟩ := mul_words A C
  have hx := step_lt C.isLt A.isLt K.isLt T.isLt
  have hK := K.isLt
  have hT := T.isLt
  rw [Nat.mul_comm C.toNat] at hx ⊢
  have he2 : (BitVec.ofNat 32 (A.toNat * C.toNat)).toNat = A.toNat * C.toNat % 2 ^ 32 := BitVec.toNat_ofNat _ _
  have hd2 : (BitVec.ofNat 32 (A.toNat * C.toNat / 2 ^ 32)).toNat = A.toNat * C.toNat / 2 ^ 32 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : ∀ x : BitVec 32, x + 0 = x := BitVec.add_zero
  rw [h0, h0]
  rw [add3_toNat, ofBool_toNat, BitVec.toNat_add, BitVec.toNat_add, he2, hd2]
  rw [BitVec.toNat_add, he2] at hc5
  rw [he2] at hc3
  subst hc3 hc5
  generalize A.toNat * C.toNat = P at *
  by_cases h1 : 2 ^ 32 ≤ P % 2 ^ 32 + K.toNat <;> by_cases h2 : 2 ^ 32 ≤ (P % 2 ^ 32 + K.toNat) % 2 ^ 32 + T.toNat <;>
    simp only [h1, h2, decide_true, decide_false, Bool.toNat_true, Bool.toNat_false, Nat.add_zero] <;>
    constructor <;> omega

/-- `[ebp + acc + 4j] += ecx · [edi + b + 4j] + ebx`, the carry word to `ebx`. -/
theorem mulStep_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {acc b i j : Nat}
    (hp : s.gpr .ebp = s.gpr .edi + BitVec.ofNat 32 (4 * i))
    (hb : b + 4 * j + 4 ≤ size) (ht : 4 * i + (acc + 4 * j) + 4 ≤ size) :
    WP isa (.block (mulStep acc b j)) s fun u =>
      u.mem = s.mem.writeW (off base (4 * i + (acc + 4 * j))) (BitVec.ofNat 32
        ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) + (s.gpr .ebx).toNat +
          w32 s.mem base (4 * i + (acc + 4 * j)))) ∧
      (u.gpr .ebx).toNat = ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) + (s.gpr .ebx).toNat +
          w32 s.mem base (4 * i + (acc + 4 * j))) / 2 ^ 32 ∧
      Keeps [.eax, .ebx, .edx] s u := by
  simp only [mulStep]
  refine wp_movS (readSrc_sc hs hb) fun s₁ u₁ _ => ?_
  refine wp_mul fun s₂ m₂ => ?_
  refine wp_addS rfl fun s₃ u₃ c₃ => ?_
  refine wp_adcS rfl c₃ fun s₄ u₄ c₄ => ?_
  have hs₄ : Scr s₄ base size := ⟨by rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide)
    (by decide), u₁.other _ (by decide)]; exact hs.edi, by rw [u₄.wr, u₃.wr, m₂.wr, u₁.wr]; exact hs.wr, hs.nowrap⟩
  have hp₄ : s₄.gpr .ebp = s₄.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide) (by decide), u₁.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
    exact hp
  refine wp_addS (readSrc_at hs₄ hp₄ ht) fun s₅ u₅ c₅ => ?_
  refine wp_adcS rfl c₅ fun s₆ u₆ c₆ => ?_
  have hs₆ : Scr s₆ base size := ⟨by rw [u₆.other _ (by decide), u₅.other _ (by decide)]; exact hs₄.edi,
    by rw [u₆.wr, u₅.wr]; exact hs₄.wr, hs.nowrap⟩
  have hp₆ : s₆.gpr .ebp = s₆.gpr .edi + BitVec.ofNat 32 (4 * i) := by
    rw [u₆.other _ (by decide), u₅.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide)]
    exact hp₄
  refine wp_storeS (hs₆.ea_at hp₆ (by omega)) (hs₆.write ht) fun s₇ m₇ => ?_
  refine wp_movS rfl fun s₈ u₈ _ => WP.block_nil ?_
  -- The registers and memory along the way.
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, m₂.mem, u₁.mem]
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, m₄]
  have ecx₂ : s₁.gpr .ecx = s.gpr .ecx := u₁.other _ (by decide)
  have eax₂ := m₂.eax
  have edx₂ := m₂.edx
  rw [u₁.gpr, ecx₂] at eax₂ edx₂
  have ebx₂ : s₂.gpr .ebx = s.gpr .ebx := by rw [m₂.other _ (by decide) (by decide), u₁.other _ (by decide)]
  have eax₃ : s₃.gpr .eax = s₂.gpr .eax + s₂.gpr .ebx := u₃.gpr
  have edx₄ : s₄.gpr .edx = s₃.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₄.gpr
  have eax₄ : s₄.gpr .eax = s₃.gpr .eax := u₄.other _ (by decide)
  have edx₃ : s₃.gpr .edx = s₂.gpr .edx := u₃.other _ (by decide)
  have eax₅ : s₅.gpr .eax = s₄.gpr .eax + s.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := by
    rw [u₅.gpr, m₄]
  have edx₆ : s₆.gpr .edx = s₅.gpr .edx + 0 + (BitVec.ofBool _).setWidth 32 := u₆.gpr
  have eax₆ : s₆.gpr .eax = s₅.gpr .eax := u₆.other _ (by decide)
  have edx₅ : s₅.gpr .edx = s₄.gpr .edx := u₅.other _ (by decide)
  -- The arithmetic.
  have hpost := step_regs (s.mem.readW (off base (b + 4 * j)) 32) (s.gpr .ecx) (s.gpr .ebx)
    (s.mem.readW (off base (4 * i + (acc + 4 * j))) 32) _ _ rfl rfl
  have ex₆ : s₆.gpr .eax = BitVec.ofNat 32 ((s.mem.readW (off base (b + 4 * j)) 32).toNat * (s.gpr .ecx).toNat) +
      s.gpr .ebx + s.mem.readW (off base (4 * i + (acc + 4 * j))) 32 := by
    rw [eax₆, eax₅, eax₄, eax₃, eax₂, ebx₂]
  have dx₆ := edx₆
  rw [edx₅, edx₄, edx₃, edx₂, eax₄, eax₃, eax₂, ebx₂, m₄] at dx₆
  have hx : s₆.gpr .eax = BitVec.ofNat 32 ((s.gpr .ecx).toNat * w32 s.mem base (b + 4 * j) +
      (s.gpr .ebx).toNat + w32 s.mem base (4 * i + (acc + 4 * j))) := by
    apply BitVec.eq_of_toNat_eq
    rw [ex₆, hpost.1, BitVec.toNat_ofNat]
  refine ⟨by rw [u₈.mem, m₇.mem, m₆, hx], by rw [u₈.gpr, m₇.gpr, dx₆, hpost.2], fun r hr => ?_,
    by rw [u₈.rd, m₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, m₂.rd, u₁.rd],
    by rw [u₈.wr, m₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, m₂.wr, u₁.wr]⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  obtain ⟨h1, h2, h3⟩ := hr
  rw [u₈.other _ h2, m₇.gpr, u₆.other _ h3, u₅.other _ h1, u₄.other _ h3, u₃.other _ h1, m₂.other _ h1 h3,
    u₁.other _ h1]

end VG.Proof.Mont.X86
