module
public import VerifiedGarbage.Proof.Gcm.X86_64.Pclmul.Exec

import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem

/-!
# The mask of the last blocks after the last group

`testR9_ok` and `movR10_ok`, which `remMaskG_ok` (`RemGKs.lean`) puts the
mask of the last register's blocks in `r10` with, from `r9 = 16 + m`
(`test1`, `test2`). `Prod.acc_zero_right`: a product with zero adds nothing,
as the masked-off lanes do.
-/

@[expose] public section

namespace VG.Proof.Gcm.X86_64.StitchZH

open VG VG.X86_64
open VG.Proof.Gcm.X86_64.Pclmul (Prod)

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

/-- `mov32 r10, imm`. -/
theorem movR10_ok (s : State) (v : BitVec 32) :
    WP isa (.block [.mov32 .r10 (.imm v)]) s fun s' =>
      s'.gpr .r10 = v.setWidth 64 ∧ (∀ q, q ≠ .r10 → s'.gpr q = s.gpr q) ∧
      (∀ x l, s'.zlane x l = s.zlane x l) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, isa, State.setReg32, State.setReg,
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨by simp, fun q hq => by simp [hq], fun _ _ => rfl, trivial, trivial, trivial⟩

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
