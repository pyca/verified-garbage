module

public import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
public import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Argon2.AArch64.BlockAddress
meta import VerifiedGarbage.Proof.Argon2.AArch64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Taint
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
public import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.Impl.Argon2.AArch64.Instructions
meta import VerifiedGarbage.Proof.Framework.Semantics

/-! ### `Argon2.AArch64.MemoryInitScale`, which this module and modules that import it used -/

section

/-! # Fixed scaling by public powers of two on ARM64 -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.MemoryInit
open VG VG.AArch64 VG.Impl.Argon2.AArch64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block (Instructions.add r r)) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧
      (∀ q, q ≠ r → q ≠ .x15 → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil,
    exec, State.read, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hq hq' => ?_, rfl, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_write, ite_true, BitVec.setWidth_eq, BitVec.add_zero, ite_self]
  · simp only [RegUpd.gpr_write, hq, hq', ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (Instructions.add r r)).flatten) s
      fun t => Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [WP.block_append_iff]
    refine (double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr, sp⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq hq' => (ht.other q hq hq').trans (other q hq hq'),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr, ht.sp.trans sp⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)
end VG.Proof.Argon2.AArch64.MemoryInit

end

end

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

@[expose] public section

namespace VG.Proof.Argon2.AArch64.BlockAddress

open VG VG.AArch64 VG.Impl.Argon2.AArch64.BlockAddress
open VG.Impl.Argon2.AArch64

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .x8 = s.gpr .x8 * s.gpr .x20 + s.gpr .x3 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  apply WP.of_runBlock
  simp only [flatten, Instructions.mul, Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.1, hr.2.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .x8 = s.gpr .x8 * 1024 ∧ Divide.Keeps [.x8, .x15] s t := by
  refine (MemoryInit.scale_ok s .x8 10).mono ?_
  intro t h
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, h.sp⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h.other r hr.1 hr.2

theorem base_ok (s : State) : WP isa (.block ([Instructions.add .x8 .x4].flatten)) s fun t =>
    t.gpr .x8 = s.gpr .x8 + s.gpr .x4 ∧ Divide.Keeps [.x8, .x15] s t := by
  apply WP.of_runBlock
  simp only [Instructions.add, Instructions.mark, Instructions.mov,
    List.flatten_cons, List.flatten_nil, List.cons_append, List.nil_append,
    runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    RegUpd.gpr_write, Size.bits, BitVec.setWidth_eq,
    show 0 < 4096 from by decide, BitVec.add_zero,
    reduceCtorEq, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .x8 = (s.gpr .x8 * s.gpr .x20 + s.gpr .x3) * 1024 + s.gpr .x4 ∧
    Divide.Keeps [.x8, .x2, .x15] s t := by
  unfold code
  refine WP.seq ((flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by decide)).trans (kt.mono (by decide)))⟩
  rw [result, scaled, flat, kb.regs .x4 (by decide), ka.regs .x4 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .x8 = BitVec.ofNat 64 lane)
    (hc : s.gpr .x3 = BitVec.ofNat 64 column)
    (hq : s.gpr .x20 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .x8 = s.gpr .x4 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.x8, .x2, .x15] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .x4 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

end VG.Proof.Argon2.AArch64.BlockAddress
