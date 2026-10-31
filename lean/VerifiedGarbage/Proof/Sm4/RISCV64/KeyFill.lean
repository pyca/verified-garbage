module

public import VerifiedGarbage.Impl.Sm4.RISCV64.Layers
public import VerifiedGarbage.Proof.Framework.RISCV64.Straight
import VerifiedGarbage.Proof.Framework.RISCV64.Exec
import VerifiedGarbage.Proof.Framework.RISCV64.RegUpd
import VerifiedGarbage.Proof.Framework.Interleave
import all Init.Data.Nat.Bitwise.Basic

/-!
# Filling a round key's plane by a subtraction, on RISC-V

A plane of a round key has its bits at `16 i` (`keyBit`), and `keyFill`
fills each 16-bit group with its bit: `(x ⋘ 16) - x` is `x · 0xFFFF`,
which, with no carries between the groups, copies bit `16 i` to bits
`16 i … 16 i + 15`. `getLsbD_fill` proves it for the sixteen such words, by
evaluation, and `keyFill_ok` runs the code.
-/

@[expose] public section

namespace VG.Proof.Sm4.RISCV64

/-- What `keyFill` makes of a plane. -/
def fill (x : BitVec 64) : BitVec 64 := (x <<< 16) - x

/-- The word with bits `b₀ … b₃` at `0`, `16`, `32` and `48`. -/
def sparse (b₀ b₁ b₂ b₃ : Bool) : BitVec 64 :=
  (if b₀ then 1 else 0) ||| (if b₁ then 0x10000 else 0) ||| (if b₂ then 0x100000000 else 0) |||
    (if b₃ then 0x1000000000000 else 0)

theorem getLsbD_sparse : ∀ b₀ b₁ b₂ b₃ : Bool, ∀ p < 64, (sparse b₀ b₁ b₂ b₃).getLsbD p =
    (decide (p = 0) && b₀ || decide (p = 16) && b₁ || decide (p = 32) && b₂ || decide (p = 48) && b₃) := by
  decide +kernel

theorem getLsbD_fill_sparse : ∀ b₀ b₁ b₂ b₃ : Bool, ∀ p < 64,
    (fill (sparse b₀ b₁ b₂ b₃)).getLsbD p = (sparse b₀ b₁ b₂ b₃).getLsbD (16 * (p / 16)) := by
  decide +kernel

/-- A word with its bits at `16 i` only, filled: bit `p` is bit `16 ⌊p / 16⌋`. -/
theorem getLsbD_fill {x : BitVec 64} (hx : ∀ p < 64, p % 16 ≠ 0 → x.getLsbD p = false) {p : Nat}
    (hp : p < 64) : (fill x).getLsbD p = x.getLsbD (16 * (p / 16)) := by
  have hs : x = sparse (x.getLsbD 0) (x.getLsbD 16) (x.getLsbD 32) (x.getLsbD 48) := by
    refine BitVec.eq_of_getLsbD_eq fun k hk => ?_
    rw [getLsbD_sparse _ _ _ _ k hk]
    by_cases h : k % 16 = 0
    · have : k = 0 ∨ k = 16 ∨ k = 32 ∨ k = 48 := by omega
      rcases this with rfl | rfl | rfl | rfl <;> simp
    · have : k ≠ 0 ∧ k ≠ 16 ∧ k ≠ 32 ∧ k ≠ 48 := by omega
      simp [hx k hk h, this.1, this.2.1, this.2.2.1, this.2.2.2]
  rw [hs]
  exact getLsbD_fill_sparse _ _ _ _ p hp

open VG.RISCV64 VG.RISCV64.Straight
open VG.Impl.Aes.RISCV64 (q t0 shlI)

/-- `r := ` its fill, through `t0`. -/
theorem fillOne_ok (s : State) {r : Reg} (hr : r ≠ t0) :
    ∃ s', runBlock isa [shlI t0 r 16, .sub r t0 r] s = some s' ∧ s'.gpr r = fill (s.gpr r) ∧
      (∀ r', r' ≠ r → r' ≠ t0 → s'.gpr r' = s.gpr r') ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := s.write t0 (s.gpr r <<< 16)
  refine ⟨s₁.write r (s₁.gpr t0 - s₁.gpr r),
    by simp only [shlI, runBlock_cons, exec_shift_d (show 16 < 64 by decide), runStep_some]; rfl,
    ?_, fun r' h1 h2 => ?_, rfl, rfl, rfl⟩
  · simp only [s₁]
    rw [RegUpd.gpr_write_self, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne _ _ hr]; rfl
  · simp only [s₁]
    rw [RegUpd.gpr_write_of_ne _ _ h1, RegUpd.gpr_write_of_ne _ _ h2]

/-- The registers `rs`, each to its fill. -/
theorem fillList_ok : ∀ (rs : List Reg), rs.Nodup → t0 ∉ rs → ∀ s : State,
    ∃ s', runBlock isa (rs.flatMap fun r => [shlI t0 r 16, .sub r t0 r]) s = some s' ∧
      (∀ r ∈ rs, s'.gpr r = fill (s.gpr r)) ∧ (∀ r, r ∉ rs → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr
  | [], _, _, s => ⟨s, rfl, by simp, fun _ _ _ => rfl, rfl, rfl, rfl⟩
  | r :: rs, hn, ht, s => by
    have hr : r ≠ t0 := fun h => ht (h ▸ List.mem_cons_self)
    have hn' := List.nodup_cons.mp hn
    obtain ⟨s₁, e₁, v₁, o₁, m₁, rd₁, wr₁⟩ := fillOne_ok s hr
    obtain ⟨s₂, e₂, v₂, o₂, m₂, rd₂, wr₂⟩ := fillList_ok rs hn'.2 (fun h => ht (List.mem_cons_of_mem _ h)) s₁
    refine ⟨s₂, by rw [List.flatMap_cons, Interleave.runBlock_append, e₁, Option.bind_some, e₂], fun r' hr' => ?_,
      fun r' h1 h2 => ?_, by rw [m₂, m₁], by rw [rd₂, rd₁], by rw [wr₂, wr₁]⟩
    · rcases List.mem_cons.mp hr' with rfl | h
      · rw [o₂ _ hn'.1 hr, v₁]
      · rw [v₂ r' h, o₁ r' (fun e => hn'.1 (e ▸ h)) (fun e => ht (e ▸ List.mem_cons_of_mem _ h))]
    · rw [o₂ r' (fun h => h1 (List.mem_cons_of_mem _ h)) h2, o₁ r' (fun h => h1 (h ▸ List.mem_cons_self)) h2]

/-- `keyFill`: each plane to its fill. -/
theorem keyFill_ok (s : State) :
    ∃ s', runBlock isa VG.Impl.Sm4.RISCV64.keyFill s = some s' ∧
      (∀ j < 8, s'.gpr (q j) = fill (s.gpr (q j))) ∧
      (∀ r, (∀ j < 8, r ≠ q j) → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hq : (List.range 8).map q = [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7] := rfl
  obtain ⟨s', e', v', o', m', rd', wr'⟩ := fillList_ok ((List.range 8).map q) (by rw [hq]; decide)
    (by rw [hq]; decide) s
  refine ⟨s', by rw [VG.Impl.Sm4.RISCV64.keyFill]; rw [List.flatMap_map] at e'; exact e', fun j hj =>
    v' _ (List.mem_map_of_mem (List.mem_range.mpr hj)), fun r hr h0 => o' r (fun h => ?_) h0, m', rd', wr'⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
  exact hr j (List.mem_range.mp hj) rfl

end VG.Proof.Sm4.RISCV64
