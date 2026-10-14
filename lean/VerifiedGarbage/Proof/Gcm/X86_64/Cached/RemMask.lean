module

public import VerifiedGarbage.Proof.Gcm.X86_64.Cached.RemBody
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-!
# The mask of the first blocks after the last group

`remMask_ok`: from `r9 = 16 + m` with `m mod 4` 2 or 3, `StitchZH.remMask`
puts in `r10` the mask of the first `m mod 4` blocks, `4 ^ (m mod 4) - 1`
(`mask_ok`: its quadwords are the first `2 (m mod 4)`). `remAfterK_ok`:
`StitchZH.remAfterK` then sets `r10 = 16 (m mod 4)` and takes those blocks
from `r9`. `Prod.acc_zero_right`: a product with zero adds nothing, as the
masked-off lanes do.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod)
open VG.Impl.Gcm.X86_64.StitchZH (remMask remAfterK)

/-- Whether `16 + m` has bit 1 clear, as `test r9, 2` finds it. -/
theorem test2 : ∀ m < 16, (BitVec.ofNat 64 (16 + m) &&& BitVec.signExtend 64 (2 : BitVec 32) == 0) =
    decide (m % 4 < 2) := by decide

/-- Whether `16 + m` is even, as `test r9, 1` finds it. -/
theorem test1 : ∀ m < 16, (BitVec.ofNat 64 (16 + m) &&& BitVec.signExtend 64 (1 : BitVec 32) == 0) =
    decide (m % 2 = 0) := by decide

/-- `test r9, v`. -/
theorem testR9_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.alu .test .r9 (.imm v)]) s fun s' =>
      s'.zf = some (s.gpr .r9 &&& BitVec.signExtend 64 v == 0) ∧ s'.gpr = s.gpr ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags, State.setFlags, isa,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The masks of two and three blocks: their first `2 c` quadwords. -/
theorem mask_ok : ∀ c < 4, 2 ≤ c →
    State.qOn (BitVec.ofNat 64 (4 ^ c - 1)) = List.range (2 * c) ∧
      ∀ j < 8, (BitVec.ofNat 64 (4 ^ c - 1)).getLsbD j = decide (j < 2 * c) := by decide

/-- `mov32 r10, imm`. -/
theorem movR10_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.mov32 .r10 (.imm v)]) s fun s' =>
      s'.gpr .r10 = v.setWidth 64 ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, State.setReg32, State.setReg,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, fun q hq => by simp [hq], fun _ _ => rfl, trivial, trivial, trivial⟩

/-- The mask of the first `m mod 4` (2 or 3) blocks, in `r10`. -/
theorem remMask_ok (s : State) {m : Nat} (hm : m < 16) (hc : 2 ≤ m % 4)
    (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) :
    WP isa remMask s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (4 ^ (m % 4) - 1) ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.seq (WP.mono (testR9_ok s 1) fun t ⟨z, g, l, m', rd, wr⟩ => ?_)
  have zt : t.zf = some (decide (m % 2 = 0)) := by rw [z, h9, test1 m hm]
  refine WP.ite (decide (m % 2 = 0)) (by simp only [eval, zt]) (fun h => ?_) (fun h => ?_)
  · have h2 : m % 4 = 2 := by simp at h; omega
    refine WP.mono (movR10_ok t 15) fun t' ⟨a, b, c, d, e, f⟩ => ⟨?_, fun q hq => by rw [b q hq, g], fun x l' => by
      rw [c, l], by rw [d, m'], by rw [e, rd], by rw [f, wr]⟩
    rw [a, h2]; decide
  · have h3 : m % 4 = 3 := by simp at h; omega
    refine WP.mono (movR10_ok t 63) fun t' ⟨a, b, c, d, e, f⟩ => ⟨?_, fun q hq => by rw [b q hq, g], fun x l' => by
      rw [c, l], by rw [d, m'], by rw [e, rd], by rw [f, wr]⟩
    rw [a, h3]; decide

theorem afterK10 : ∀ m < 16,
    (BitVec.ofNat 64 (16 + m) &&& BitVec.signExtend 64 (3 : BitVec 32)) <<< 4 = BitVec.ofNat 64 (16 * (m % 4)) := by
  decide

theorem afterK9 : ∀ m < 16,
    (BitVec.ofNat 64 (16 + m) &&& BitVec.signExtend 64 (0xFFFFFFFC : BitVec 32)) =
      BitVec.ofNat 64 (16 + (m - m % 4)) := by
  decide

/-- `r10 = 16 (m mod 4)` and `r9 = 16 + m - m mod 4`. -/
theorem remAfterK_ok (s : State) {m : Nat} (hm : m < 16) (h9 : s.gpr .r9 = BitVec.ofNat 64 (16 + m)) :
    WP isa (.block remAfterK) s fun s' =>
      s'.gpr .r10 = BitVec.ofNat 64 (16 * (m % 4)) ∧ s'.gpr .r9 = BitVec.ofNat 64 (16 + (m - m % 4)) ∧
      (∀ q, q ≠ .r9 → q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [remAfterK, reduceCtorEq, ↓reduceIte, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    execShift, readSrc, arithFlags, State.setFlags, isa, State.setReg, h9, afterK10 m hm, afterK9 m hm,
    show 1 ≤ 4 ∧ 4 ≤ 63 by decide, and_self, Option.bind_some, Option.map_some, Option.some.injEq,
    exists_eq_left']
  exact ⟨trivial, trivial, fun r h1 h2 => by simp only [h1, h2, ite_false], fun _ _ => rfl, trivial⟩

theorem xor_zero128 (x : BitVec 128) : x ^^^ 0 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp

theorem clmul_zero_right (a : BitVec 64) : clmul a 0 = 0 := by
  have hf : (fun acc j => if a.getLsbD j then acc ^^^ ((0 : BitVec 64).setWidth 128 <<< j) else acc) =
      fun (acc : BitVec 128) (_ : Nat) => acc := by
    funext acc j
    have hs : (0 : BitVec 64).setWidth 128 <<< j = 0 := by
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp
    rw [hs, xor_zero128, ite_self]
  unfold clmul
  rw [hf]
  generalize List.range 64 = l
  induction l with
  | nil => rfl
  | cons j l ih => exact ih

/-- A product with zero adds nothing. -/
theorem Prod.acc_zero_right (p : Prod) (a : BitVec 128) : p.acc a 0 = p := by
  have he : ∀ i, BitVec.extractLsb' i 64 (0 : BitVec 128) = 0 := fun i => by
    apply BitVec.eq_of_getLsbD_eq; intro j _; simp
  simp only [Prod.acc, pclmul, qword, he, clmul_zero_right, xor_zero128]

end VG.Proof.Gcm.X86_64.StitchZH
