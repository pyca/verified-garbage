module

public import VerifiedGarbage.Proof.Rsa.X86.WordRt.Prep
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Chain
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Zero
import VerifiedGarbage.Proof.Rsa.X86.KeyRt.Scalar
import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Power
import VerifiedGarbage.Proof.Bignum.X86.R2Words.Quot
import VerifiedGarbage.Proof.X25519.X86.Column
import VerifiedGarbage.Proof.Framework.Omega

/-! # `WordModRt` on i686: products

A word of a row (`mulBody_ok`): `[o] := [o] + aᵢ b_j + c`, its high word the
next carry; a row (`mulRow_ok`): `[o]` from word `j` on, `w + 1` words, plus
`a b_j`; `mulWide_ok`: the product of two numbers over `2 w` words; and
`mulShort_ok`: a number times the low two words of another.
-/

@[expose] public section

namespace VG.Proof.Rsa.X86.WordRt

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Rsa.X86.KeyRt VG.Proof.Mont VG.Proof.Mont.X86
open VG.Proof.Mont.X86.Rt VG.Proof.Bignum.X86
open VG.Proof.Rsa.X86.Keys (Keep arr num S slot)
open VG.Proof.Rsa.X86.KeyRt (RtWs kw arrPtr_ok lenSrc bytesB_ok)

variable {L : Lay} {B : Addr} {Z len N : Nat}

/-- The block of a row's word. -/
abbrev mulBody : List Instr :=
  [.mov .eax (.mem (at_ .esi 0)), .mul .ecx, .alu .add .eax (.reg .ebx), .alu .adc .edx (.imm 0),
    .alu .add .eax (.mem (at_ .ebp 0)), .alu .adc .edx (.imm 0), .store (at_ .ebp 0) .eax, .mov .ebx (.reg .edx),
    .alu .add .esi (.imm 4), .alu .add .ebp (.imm 4), .alu .sub .edi (.imm 4)]

/-- A word of a row, with `esi` at `aᵢ` (`xa`), `ebp` at `oᵢ` (`xo`), `b_j` in `ecx` and the carry
in `ebx`: `o'ᵢ + 2^32 c' = aᵢ b_j + c + oᵢ`. -/
theorem mulBody_ok {t : State} {bytes xa xo : Nat} (ws : Ws t B bytes) (pa : PtrAt t B .esi xa)
    (po : PtrAt t B .ebp xo) (ha : xa + 4 ≤ bytes) (ho : xo + 4 ≤ bytes) :
    WP isa (.block mulBody) t fun t' =>
      w32 t'.mem B xo + 2 ^ 32 * (t'.gpr .ebx).toNat =
        w32 t.mem B xa * (t.gpr .ecx).toNat + (t.gpr .ebx).toNat + w32 t.mem B xo ∧
      t'.mem = t.mem.writeW (off B xo) (BitVec.ofNat 32 (w32 t'.mem B xo)) ∧
      PtrAt t' B .esi (xa + 4) ∧ PtrAt t' B .ebp (xo + 4) ∧ t'.gpr .edi = t.gpr .edi - 4 ∧
      t'.zf = some (t.gpr .edi - 4 == 0) ∧ Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t' := by
  have nw := ws.nowrap
  simp only [mulBody]
  refine wp_movS (readSrc_ptr ws pa (d := 0) (by omega)) fun t₁ U₁ _ => wp_mul fun t₂ U₂ => ?_
  refine wp_addS rfl fun t₃ U₃ c₃ => wp_adcS rfl c₃ fun t₄ U₄ _ => ?_
  have ws₄ := ws.of_wr (U₄.wr.trans (U₃.wr.trans (U₂.wr.trans U₁.wr)))
  have po₄ : PtrAt t₄ B .ebp xo := by
    rw [PtrAt, U₄.other _ (by decide), U₃.other _ (by decide), U₂.other _ (by decide) (by decide),
      U₁.other _ (by decide)]; exact po
  refine wp_addS (readSrc_ptr ws₄ po₄ (d := 0) (by omega)) fun t₅ U₅ c₅ => wp_adcS rfl c₅ fun t₆ U₆ _ => ?_
  have ws₆ := ws₄.of_wr (U₆.wr.trans U₅.wr)
  have po₆ : PtrAt t₆ B .ebp xo := by rw [PtrAt, U₆.other _ (by decide), U₅.other _ (by decide)]; exact po₄
  refine wp_storeS (ea_ptr ws₆ po₆ (d := 0) (by omega)) (ws_write ws₆ (by omega)) fun t₇ M₇ => ?_
  refine wp_movS rfl fun t₈ U₈ _ => wp_addS rfl fun t₉ U₉ _ => wp_addS rfl fun t₁₀ U₁₀ _ =>
    wp_subZ rfl fun t₁₁ U₁₁ z₁₁ => WP.block_nil ?_
  -- The values.
  have hA : (t₁.gpr .eax).toNat = w32 t.mem B xa := by rw [U₁.gpr, Nat.add_zero]
  have hq : t₁.gpr .ecx = t.gpr .ecx := U₁.other _ (by decide)
  have hc : t₂.gpr .ebx = t.gpr .ebx := by rw [U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]
  have hb : w32 t.mem B xa * (t.gpr .ecx).toNat / 2 ^ 32 < 2 ^ 32 - 1 :=
    (mul_words (t.mem.readW (off B xa) 32) (t.gpr .ecx)).2
  have lo₂ : (t₂.gpr .eax).toNat = w32 t.mem B xa * (t.gpr .ecx).toNat % 2 ^ 32 := by
    rw [U₂.eax, hA, hq, BitVec.toNat_ofNat]
  have hi₂ : (t₂.gpr .edx).toNat = w32 t.mem B xa * (t.gpr .ecx).toNat / 2 ^ 32 := by
    rw [U₂.edx, hA, hq, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have m₆ : t₆.mem = t.mem := by rw [U₆.mem, U₅.mem, U₄.mem, U₃.mem, U₂.mem, U₁.mem]
  have hO : (t₄.mem.readW (off B (xo + 0)) 32).toNat = w32 t.mem B xo := by
    rw [U₄.mem, U₃.mem, U₂.mem, U₁.mem, Nat.add_zero]
  -- `lo₃ + 2^32 c₃ = lo₂ + c`, `hi₄ = hi₂ + c₃`, `lo₅ + 2^32 c₅ = lo₃ + o`, `hi₆ = hi₄ + c₅`.
  have e₃ := VG.Proof.Bignum.X86.R2Words.add32_toNat (t₂.gpr .eax) (t₂.gpr .ebx)
  have e₅ := VG.Proof.Bignum.X86.R2Words.add32_toNat (t₄.gpr .eax) (t₄.mem.readW (off B (xo + 0)) 32)
  have hc32 := (t.gpr .ebx).isLt
  have ho32 : w32 t.mem B xo < 2 ^ 32 := (t.mem.readW _ 32).isLt
  have hca : (t₃.gpr .eax).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat =
      (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat := by rw [U₃.gpr]; exact e₃
  have h₄ : (t₄.gpr .edx).toNat = (t₂.gpr .edx).toNat +
      (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat := by
    rw [U₄.gpr, add3_toNat, U₃.other .edx (by decide), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero]
    apply Nat.mod_eq_of_lt
    have := Bool.toNat_le (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat))
    rw [hi₂]; omega
  have ea₄ : t₄.gpr .eax = t₃.gpr .eax := U₄.other _ (by decide)
  rw [ea₄] at e₅
  have hcb : (t₅.gpr .eax).toNat + 2 ^ 32 * (decide (2 ^ 32 ≤ (t₃.gpr .eax).toNat + w32 t.mem B xo)).toNat =
      (t₃.gpr .eax).toNat + w32 t.mem B xo := by rw [U₅.gpr, ea₄, ← hO]; exact e₅
  have hdiv := Nat.div_add_mod (w32 t.mem B xa * (t.gpr .ecx).toNat) (2 ^ 32)
  have hP : w32 t.mem B xa * (t.gpr .ecx).toNat ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) :=
    Nat.mul_le_mul (by have := (t.mem.readW (off B xa) 32).isLt; simp only [w32]; omega) (by omega)
  rw [hc, lo₂] at hca
  have hl3 := (t₃.gpr .eax).isLt
  have hl5 := (t₅.gpr .eax).isLt
  generalize hc1 : (decide (2 ^ 32 ≤ w32 t.mem B xa * (t.gpr .ecx).toNat % 2 ^ 32 + (t.gpr .ebx).toNat)).toNat = c1
    at hca h₄
  generalize hc2 : (decide (2 ^ 32 ≤ (t₃.gpr .eax).toNat + w32 t.mem B xo)).toNat = c2 at hcb
  have c1b : c1 ≤ 1 := hc1 ▸ Bool.toNat_le _
  have c2b : c2 ≤ 1 := hc2 ▸ Bool.toNat_le _
  obtain ⟨P, hPe⟩ : ∃ P, P = w32 t.mem B xa * (t.gpr .ecx).toNat := ⟨_, rfl⟩
  rw [← hPe] at hdiv hP hca hi₂
  have hsum : 2 ^ 32 * (P / 2 ^ 32 + c1 + c2) + (t₅.gpr .eax).toNat = P + (t.gpr .ebx).toNat + w32 t.mem B xo := by
    omega
  have hX : P / 2 ^ 32 + c1 + c2 < 2 ^ 32 := by
    by_contra hcon
    have h1 := Nat.mul_le_mul_left (2 ^ 32) (Nat.le_of_not_lt hcon)
    have h2 : (2 : Nat) ^ 32 * 2 ^ 32 = 2 ^ 64 := by decide
    omega
  have e1 : (decide (2 ^ 32 ≤ (t₂.gpr .eax).toNat + (t₂.gpr .ebx).toNat)).toNat = c1 := by
    rw [lo₂, hc, ← hc1]
  have e4 : (t₄.gpr .edx).toNat = P / 2 ^ 32 + c1 := by rw [h₄, hi₂, e1]
  have h₆ : (t₆.gpr .edx).toNat = (t₄.gpr .edx).toNat + c2 := by
    rw [U₆.gpr, add3_toNat, U₅.other .edx (by decide), show (0 : BitVec 32).toNat = 0 from rfl, Nat.add_zero, ea₄,
      hO, hc2]
    apply Nat.mod_eq_of_lt
    rw [e4]; exact hX
  have m₇ : t₇.mem = t.mem.writeW (off B xo) (t₆.gpr .eax) := by rw [M₇.mem, m₆, Nat.add_zero]
  have m₁₁ : t₁₁.mem = t₇.mem := by rw [U₁₁.mem, U₁₀.mem, U₉.mem, U₈.mem]
  have bx : t₁₁.gpr .ebx = t₆.gpr .edx := by
    rw [U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.gpr, M₇.gpr]
  have K : Keeps [.eax, .ebx, .edx, .esi, .ebp, .edi] t t₁₁ := by
    refine ((((U₁.keeps.mono (by decide)).trans (U₂.keeps.mono (by decide))).trans
      ((U₃.keeps.mono (by decide)).trans (U₄.keeps.mono (by decide)))).trans
      (((U₅.keeps.mono (by decide)).trans (U₆.keeps.mono (by decide))).trans (M₇.keeps _))).trans
      (((U₈.keeps.mono (by decide)).trans (U₉.keeps.mono (by decide))).trans
      ((U₁₀.keeps.mono (by decide)).trans (U₁₁.keeps.mono (by decide))))
  have pa₇ : PtrAt t₇ B .esi xa := by
    rw [PtrAt, M₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]; exact pa
  have po₇ : PtrAt t₇ B .ebp xo := by rw [PtrAt, M₇.gpr]; exact po₆
  have di₇ : t₇.gpr .edi = t.gpr .edi := by
    rw [M₇.gpr, U₆.other _ (by decide), U₅.other _ (by decide), U₄.other _ (by decide),
      U₃.other _ (by decide), U₂.other _ (by decide) (by decide), U₁.other _ (by decide)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, K⟩
  · rw [m₁₁, m₇, w32_write_self, bx, U₆.other .eax (by decide), h₆, e4, ← hPe]
    omega
  · rw [m₁₁, m₇, w32_write_self, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [PtrAt, U₁₁.other _ (by decide), U₁₀.other _ (by decide), U₉.gpr, U₈.other _ (by decide), ptr_add pa₇]; rfl
  · rw [PtrAt, U₁₁.other _ (by decide), U₁₀.gpr, U₉.other _ (by decide), U₈.other _ (by decide), ptr_add po₇]; rfl
  · rw [U₁₁.gpr, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), di₇]
  · rw [z₁₁, U₁₀.other _ (by decide), U₉.other _ (by decide), U₈.other _ (by decide), di₇]

end VG.Proof.Rsa.X86.WordRt
