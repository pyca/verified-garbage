module

public import VerifiedGarbage.Proof.ChaCha20Poly1305.AArch64.Short.Branch
import VerifiedGarbage.Proof.ChaCha20.AArch64.Xor
import VerifiedGarbage.Proof.Framework.AArch64.Lit

/-!
# ChaCha20-Poly1305 on AArch64: the route to the one-time key from the stream

`routeKey`: `x10 = 0` iff the length is `keyLo` to 704 bytes (`OpenKey.openMain`,
`SealKey.sealMain`),
then `route`'s `x9`, writing only `x9` and `x10` (`Short.Agree`).
-/

@[expose] public section

namespace VG.Proof.ChaCha20Poly1305.AArch64.OpenKey

open VG VG.AArch64 VG.Impl.ChaCha20Poly1305.AArch64
open VG.Proof.ChaCha20.AArch64.Xor (wp_addImm wp_subImm wp_sub wp_lsr wp_movz eval_zero)
open VG.Proof.ChaCha20Poly1305.AArch64.Short (Agree routeVal pad_ok)

/-- `(x - k) >> 63`, for a 64-bit `x`. -/
theorem shr63_sub {x k : Nat} (hx : x < 2 ^ 64) (hk : k ≤ 1024) :
    ((BitVec.ofNat 64 x - BitVec.ofNat 64 k) >>> 63).toNat = if x < k then 1 else (x - k) / 2 ^ 63 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  split
  · rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - k + x < 2 ^ 64)]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · rw [show 2 ^ 64 - k + x = (x - k) + 2 ^ 64 by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : x - k < 2 ^ 64)]

/-- The value `routeKey` leaves in `x10`. -/
abbrev keyVal (lo : Nat) (x : BitVec 64) : BitVec 64 :=
  (x - BitVec.ofNat 64 lo) >>> 63 - (x - BitVec.ofNat 64 705) >>> 63 + BitVec.ofNat 64 1

theorem keyVal_eq {lo x : Nat} (hlo : 1 ≤ lo) (hlo' : lo ≤ 705) (hx : x < 2 ^ 64) :
    (keyVal lo (BitVec.ofNat 64 x) == 0) = decide (lo ≤ x ∧ x ≤ 704) := by
  have b₂ := shr63_sub hx (k := lo) (by omega)
  have b₁ := shr63_sub hx (k := 705) (by decide)
  have q₂ : (x - lo) / 2 ^ 63 ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have q₁ : (x - 705) / 2 ^ 63 ≤ 1 := Nat.le_of_lt_succ (Nat.div_lt_of_lt_mul (by omega))
  have hz : ∀ y : BitVec 64, (y == 0) = decide (y.toNat = 0) := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · have : y.toNat ≠ 0 := fun h' => hy (BitVec.eq_of_toNat_eq (by simpa using h'))
      rw [show (y == 0) = false from beq_eq_false_iff_ne.mpr hy]
      simp [this]
  rw [hz, keyVal, BitVec.toNat_add, BitVec.toNat_sub, b₁, b₂, BitVec.toNat_ofNat]
  congr 1
  apply propext
  by_cases h513 : x < lo
  · simp only [h513, show x < 705 by omega, ite_true]; omega
  · by_cases h705 : x < 705
    · simp only [h513, h705, ite_true, ite_false]; omega
    · simp only [h513, h705, ite_false]
      by_cases hb : x - 705 < 2 ^ 63
      · rw [Nat.div_eq_of_lt hb]; omega
      · rw [Nat.div_eq_of_lt_le (k := 1) (by omega) (by omega),
          Nat.div_eq_of_lt_le (k := 1) (m := x - lo) (by omega) (by omega)]
        omega

/-- `routeKey`: `x10` and then `route`'s `x9`. -/
theorem routeKey_ok (sve enc : Bool) (s₀ : State) :
    WP isa (.block (routeKey sve enc)) s₀ fun s₁ => Agree s₀ s₁ ∧
      s₁.gpr .x9 = routeVal sve enc (s₀.gpr .x5) ∧ s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) := by
  have hlo : wideLo sve enc < 4096 := by cases sve <;> cases enc <;> decide
  have hsh : wideSh sve enc < 64 := by cases sve <;> cases enc <;> decide
  have h : WP isa (.block (routeKey sve enc)) s₀ fun s₁ => (∀ r, r ≠ .x9 → r ≠ .x10 → s₁.gpr r = s₀.gpr r) ∧
      s₁.gpr .x9 = routeVal sve enc (s₀.gpr .x5) ∧ s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) ∧
      s₁.mem = s₀.mem ∧ s₁.rd = s₀.rd ∧ s₁.wr = s₀.wr := by
    unfold routeKey
    refine WP.block_append (WP.block_append ((pad_ok 4 s₀).mono fun s₄ ⟨g₄, m₄, rd₄, wr₄⟩ => ?_))
    refine wp_subImm (by decide) fun s₅ u₅ => wp_lsr (by decide) fun s₆ u₆ =>
      wp_subImm (by cases sve <;> cases enc <;> decide) fun s₇ u₇ => wp_lsr (by decide) fun s₈ u₈ => wp_sub fun s₉ u₉ =>
      wp_addImm (by decide) fun s₁₀ u₁₀ => WP.block_nil ?_
    have x5 : s₄.gpr .x5 = s₀.gpr .x5 := g₄ _ (by decide)
    have x10₁₀ : s₁₀.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5) := by
      rw [u₁₀.gpr, u₉.gpr, u₈.gpr, u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), x5,
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.gpr, x5]
    show WP isa (.block (List.take 4 (route sve false))) s₁₀ _
    rw [show (route sve enc).take 4 = [.lsl .x .x9 .x5 55, .lsr .x .x9 .x9 55,
        .subImm .x .x9 .x9 (wideLo sve enc), .lsr .x .x9 .x9 (wideSh sve enc)] by simp [route]]
    refine wp_lsl (by decide) fun t₁ v₁ => wp_lsr (by decide) fun t₂ v₂ =>
      wp_subImm hlo fun t₃ v₃ => wp_lsr hsh fun t₄ v₄ => WP.block_nil
        ⟨fun r h9 h10 => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [v₄.other r h9, v₃.other r h9, v₂.other r h9, v₁.other r h9, u₁₀.other r h10, u₉.other r h10,
        u₈.other r h10, u₇.other r h10, u₆.other r h9, u₅.other r h9, g₄ r h10]
    · rw [v₄.gpr, v₃.gpr, v₂.gpr, v₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide),
        u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), x5]
    · rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.other _ (by decide), v₁.other _ (by decide),
        x10₁₀]
    · rw [v₄.mem, v₃.mem, v₂.mem, v₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]
    · rw [v₄.rd, v₃.rd, v₂.rd, v₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, rd₄]
    · rw [v₄.wr, v₃.wr, v₂.wr, v₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, wr₄]
  exact WP.mono (WP.preservedV (WP.withSp h) (by cases sve <;> cases enc <;> lit_decide))
    fun s₁ ⟨⟨⟨g, x9, x10, m, rd, wr⟩, sp⟩, v⟩ => ⟨⟨g, m, v, sp, rd, wr⟩, x9, x10⟩

/-- The branch: to `OpenKey.openMain` iff the length is 513 to 704 bytes. -/
theorem key_eval {sve enc : Bool} {s₀ s₁ : State} (h : s₁.gpr .x10 = keyVal (keyLo sve enc) (s₀.gpr .x5)) :
    isa.eval (.zero .x .x10) s₁ = some (decide (keyLo sve enc ≤ L s₀ ∧ L s₀ ≤ 704)) := by
  have e : isa.eval (.zero .x .x10) s₁ = some (s₁.gpr .x10 == 0) := eval_zero s₁ .x10
  rw [e, h, VG.Proof.ChaCha20Poly1305.AArch64.hL s₀,
    keyVal_eq (by cases sve <;> cases enc <;> decide) (by cases sve <;> cases enc <;> decide) (s₀.gpr .x5).isLt]

end VG.Proof.ChaCha20Poly1305.AArch64.OpenKey
