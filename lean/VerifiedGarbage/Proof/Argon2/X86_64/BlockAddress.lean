module

public import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
public import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Abi
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Impl.Argon2.X86_64.BlockAddress
meta import VerifiedGarbage.Proof.Argon2.X86_64.DivideStep
meta import VerifiedGarbage.Proof.Framework.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Abi
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.Taint
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.TCB.X86_64.Isa
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
meta import VerifiedGarbage.Proof.Framework.Semantics
meta import VerifiedGarbage.TCB.X86_64.Isa
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.PlainSimp
meta import VerifiedGarbage.Proof.Framework.X86_64.Reduce

/-! ### `Argon2.X86_64.MemoryInitScale`, which this module and modules that import it used -/

section

/-! # Fixed public scaling by powers of two using baseline additions -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.MemoryInit

open VG VG.X86_64

structure Scaled (s t : State) (r : Reg) (n : Nat) : Prop where
  value : t.gpr r = s.gpr r * BitVec.ofNat 64 (2 ^ n)
  other : ∀ q, q ≠ r → t.gpr q = s.gpr q
  mem : t.mem = s.mem
  rd : t.rd = s.rd
  wr : t.wr = s.wr

theorem double_ok (s : State) (r : Reg) :
    WP isa (.block [.alu .add r (.reg r)]) s fun t =>
      t.gpr r = s.gpr r + s.gpr r ∧ (∀ q, q ≠ r → t.gpr q = s.gpr q) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, reduceExec, readSrc, execAlu,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun q hr => ?_, rfl, rfl, rfl⟩
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, ite_true]
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg, hr, ite_false]

theorem scale_ok (s : State) (r : Reg) (n : Nat) :
    WP isa (.block (List.replicate n (.alu .add r (.reg r)))) s fun t => Scaled s t r n := by
  induction n generalizing s with
  | zero =>
    exact WP.block_nil ⟨by rw [Nat.pow_zero]; exact (BitVec.mul_one _).symm,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    change WP isa (.block (([.alu .add r (.reg r)] : List Instr) ++
      List.replicate n (.alu .add r (.reg r)))) s _
    rw [WP.block_append_iff]
    refine (double_ok s r).mono ?_
    rintro a ⟨value, other, mem, rd, wr⟩
    refine (ih a).mono ?_
    intro t ht
    refine ⟨?_, fun q hq => (ht.other q hq).trans (other q hq),
      ht.mem.trans mem, ht.rd.trans rd, ht.wr.trans wr⟩
    rw [ht.value, value, ← BitVec.mul_two, Nat.pow_succ, BitVec.ofNat_mul,
      BitVec.mul_assoc]
    exact congrArg (fun v => s.gpr r * v) (BitVec.mul_comm _ _)

end VG.Proof.Argon2.X86_64.MemoryInit

end

end

/-! Fault-free matrix pointer calculation, with no memory accesses. -/

@[expose] public section

namespace VG.Proof.Argon2.X86_64.BlockAddress

open VG VG.X86_64 VG.Impl.Argon2.X86_64.BlockAddress

theorem flatten_ok (s : State) : WP isa (.block flatten) s fun t =>
    t.gpr .rax = s.gpr .rax * s.gpr .r12 + s.gpr .rcx ∧
    Divide.Keeps [.rax, .rdx] s t := by
  apply WP.of_runBlock
  simp only [flatten, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    execMul, execAlu, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    reduceCtorEq, ite_true, ite_false, Option.bind_some, Option.some.injEq,
    exists_eq_left', BitVec.ofNat_mul, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine ⟨trivial, ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
      hr.1, hr.2, ite_false]
  all_goals rfl

theorem scale_ok (s : State) : WP isa (.block scale) s fun t =>
    t.gpr .rax = s.gpr .rax * 1024 ∧ Divide.Keeps [.rax] s t := by
  refine WP.mono_mx (by decide +kernel) (MemoryInit.scale_ok s .rax 10) ?_
  intro t h mx
  refine ⟨h.value, ?_, h.mem, h.rd, h.wr, mx⟩
  intro r hr
  exact h.other r (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using hr)

theorem base_ok (s : State) : WP isa (.block [.alu .add .rax (.reg .r8)]) s fun t =>
    t.gpr .rax = s.gpr .rax + s.gpr .r8 ∧ Divide.Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨by simp only [ite_true], ?_⟩
  constructor
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ite_eq_right hr
  all_goals rfl

theorem code_ok (s : State) : WP isa code s fun t =>
    t.gpr .rax = (s.gpr .rax * s.gpr .r12 + s.gpr .rcx) * 1024 + s.gpr .r8 ∧
    Divide.Keeps [.rax, .rdx] s t := by
  unfold code
  refine WP.seq ((flatten_ok s).mono ?_)
  rintro a ⟨flat, ka⟩
  refine WP.seq ((scale_ok a).mono ?_)
  rintro b ⟨scaled, kb⟩
  refine (base_ok b).mono ?_
  rintro t ⟨result, kt⟩
  refine ⟨?_, ka.trans ((kb.mono (by simp)).trans (kt.mono (by simp)))⟩
  rw [result, scaled, flat, kb.regs .r8 (by decide), ka.regs .r8 (by decide)]

theorem code_nat_ok (s : State) (lane column q : Nat)
    (hl : s.gpr .rax = BitVec.ofNat 64 lane)
    (hc : s.gpr .rcx = BitVec.ofNat 64 column)
    (hq : s.gpr .r12 = BitVec.ofNat 64 q) :
    WP isa code s fun t =>
      t.gpr .rax = s.gpr .r8 + BitVec.ofNat 64 ((lane * q + column) * 1024) ∧
      Divide.Keeps [.rax, .rdx] s t := by
  refine (code_ok s).mono ?_
  rintro t ⟨h, k⟩
  refine ⟨?_, k⟩
  rw [h, hl, hc, hq, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  change BitVec.ofNat 64 (lane * q + column) * BitVec.ofNat 64 1024 + s.gpr .r8 = _
  rw [← BitVec.ofNat_mul, BitVec.add_comm]

end VG.Proof.Argon2.X86_64.BlockAddress
