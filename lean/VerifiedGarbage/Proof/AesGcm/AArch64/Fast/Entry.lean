module

public import VerifiedGarbage.Proof.AesGcm.AArch64.Fast.Mul
public import VerifiedGarbage.Proof.AesGcm.AArch64.Seal
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# AES-GCM on AArch64, the path for TLS records: the entry

Untrusted: everything here is checked by Lean. The entry of `seal` keeps the
argument registers `x4`–`x7` (`entry_keeps`), which the path for TLS records
reads after it, as well as what `sealEntry_ok` gives (`fastEntry_ok`).
-/

@[expose] public section

namespace VG.Proof.AesGcm.AArch64.Fast

open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.AesGcm.AArch64
open VG.Proof.AesGcm.AArch64

/-- The entry keeps `x4`–`x7`. -/
theorem entry_keeps {s : State} {k j : Nat} {W : Addr} (hk : k % 8 = 0 ∧ k < 32768) (hj : j % 8 = 0 ∧ j < 32768)
    (hW : s.mem.readW (s.sp + BitVec.ofNat 64 k) 64 = W)
    (hspk : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 k) 8)
    (hspj : InRegions (s.rd ++ s.wr) (s.sp + BitVec.ofNat 64 j) 8)
    (hw : Covers [⟨W, 2560⟩] s.wr) :
    WP isa (.block (oneEntry k ++ stashArg j)) s fun s' => ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s'.gpr r = s.gpr r := by
  obtain ⟨s₀, run₀, x9₀, g₀, sp₀, m₀, rd₀, wr₀⟩ := ldrSp_ok (t := .x9) hk hW hspk
  obtain ⟨s₁, run₁, g₁, sp₁, rd₁, wr₁, m₁⟩ := save_ok s₀ .x9 x9₀ (by rw [wr₀]; exact hw)
  have w (d : Nat) (h : d + 8 ≤ 2560) := in_off hw h (by decide)
  have x9₁ : s₁.gpr .x9 = W := by rw [g₁, x9₀]
  obtain ⟨s₂, run₂, g₂, sp₂, rd₂, wr₂, x19₂⟩ : ∃ s₂, runBlock isa
      [mov .x19 .x9, ptr .x20 .x19 16, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
        .str .x .x5 .x19 alenO, .str .x .x6 .x19 dataO, .str .x .x7 .x19 lenO, mov .x23 .x2,
        mov .x24 .x3, mov .x26 .x3, imm .x27 0] s₁ = some s₂ ∧
      Others [.x19, .x20, .x21, .x22, .x23, .x24, .x26, .x27] s₁ s₂ ∧ s₂.sp = s₁.sp ∧ s₂.rd = s₁.rd ∧
      s₂.wr = s₁.wr ∧ s₂.gpr .x19 = W := by
    have w₁ := w 216 (by decide)
    have w₂ := w 224 (by decide)
    have w₃ := w 232 (by decide)
    have w₄ := w 240 (by decide)
    rw [← wr₀, ← wr₁] at w₁ w₂ w₃ w₄
    refine ⟨_, by arun [x9₁, BitVec.add_zero, w₁, w₂, w₃, w₄], ?_⟩
    exact ⟨by others_tac, rfl, rfl, rfl, by simp [gpr_write]⟩
  have hspj₂ : InRegions (s₂.rd ++ s₂.wr) (s₂.sp + BitVec.ofNat 64 j) 8 := by
    rw [rd₂, wr₂, sp₂, rd₁, wr₁, sp₁, rd₀, wr₀, sp₀]; exact hspj
  refine WP.block_append (WP.block_append (WP.block_append (WP.of_runBlock ⟨s₀, run₀, WP.of_runBlock ⟨s₁, run₁,
    WP.of_runBlock ⟨s₂, run₂, ?_⟩⟩⟩)))
  refine WP.mono (stashArg_ok (V := s₂.mem.readW (s₂.sp + BitVec.ofNat 64 j) 64) hj x19₂
    (by rw [wr₂, wr₁, wr₀]; exact hw) hspj₂ rfl) fun s₃ ⟨_, _, og₃, _⟩ r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;>
    rw [og₃ _ (by decide), g₂ _ (by decide), g₁, g₀ _ (by decide)]

/-- The entry of `seal`, with `x4`–`x7` kept. -/
theorem fastEntry_ok {w : Nat} (hw : w = 1 ∨ w = 2) {extra : List Region} {s : State}
    (hs : sealPreXW w extra s) :
    WP isa (.block (oneEntry (8 * w) ++ stashArg 0)) s fun s₁ =>
      SealEntry w s s₁ ∧ ∀ r ∈ [Reg.x4, .x5, .x6, .x7], s₁.gpr r = s.gpr r := by
  obtain ⟨ol, -, -, -⟩ := sealLay hs
  exact WP.block_and (sealEntry_ok hw hs) (entry_keeps (by omega) (by decide) rfl (ol.hsp w (by omega))
    (ol.hsp 0 (by omega)) ol.perm.w)

end VG.Proof.AesGcm.AArch64.Fast
