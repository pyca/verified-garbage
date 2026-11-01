module

public import VerifiedGarbage.Proof.Dsa.LimbContract
public import VerifiedGarbage.Impl.Dsa.X86_64
public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.PowLit

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.X86_64.RegUpd

private def limbContract (f : BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64) : Contract isa where
  pre _ := True
  post s t := t.gpr .rax = f (s.gpr .rdi) (s.gpr .rsi) (s.gpr .rdx) ∧ t.mem = s.mem
  pub _ _ := True

private def sat : State where
  gpr _ := 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := []
  wr := []

private theorem lo_correct (s : State) (_ : (limbContract fun a b _ => Proof.Dsa.Limb.mulLo a b).pre s) :
    ∃ t s', Exec isa Impl.Dsa.X86_64.mulLo s t s' ∧ abiPreserved s s' ∧
      (limbContract fun a b _ => Proof.Dsa.Limb.mulLo a b).post s s' := by
  refine ⟨[], _, .block rfl, ?_, ?_, ?_⟩
  · simp [abiPreserved, calleeSaved, execMul, gpr_setReg, gpr_setFlags,
      mem_setReg, mem_setFlags, mxcsr_setReg, mxcsr_setFlags]
  · simp only [Proof.Dsa.Limb.mulLo, execMul, gpr_setReg, gpr_setFlags,
      reduceCtorEq, ite_true, ite_false]
  · simp only [execMul, mem_setReg, mem_setFlags]

private theorem hi_correct (s : State) (_ : (limbContract fun a b _ => Proof.Dsa.Limb.mulHi a b).pre s) :
    ∃ t s', Exec isa Impl.Dsa.X86_64.mulHi s t s' ∧ abiPreserved s s' ∧
      (limbContract fun a b _ => Proof.Dsa.Limb.mulHi a b).post s s' := by
  refine ⟨[], _, .block rfl, ?_, ?_, ?_⟩
  · simp [abiPreserved, calleeSaved, execMul, gpr_setReg, gpr_setFlags,
      mem_setReg, mem_setFlags, mxcsr_setReg, mxcsr_setFlags]
  · simp only [Proof.Dsa.Limb.mulHi, execMul, gpr_setReg, gpr_setFlags,
      reduceCtorEq, ite_true, ite_false]
  · simp only [execMul, mem_setReg, mem_setFlags]

private theorem mxcsr_arithFlags (s : State) {w : Nat} (x : BitVec w) (c o : Bool) :
    (arithFlags s x c o).mxcsr = s.mxcsr := rfl

private theorem select_correct (s : State) (_ : (limbContract Proof.Dsa.Limb.select).pre s) :
    ∃ t s', Exec isa Impl.Dsa.X86_64.select s t s' ∧ abiPreserved s s' ∧
      (limbContract Proof.Dsa.Limb.select).post s s' := by
  refine ⟨[], _, .block rfl, ?_, ?_, ?_⟩
  · simp [abiPreserved, calleeSaved, gpr_setReg, gpr_arithFlags,
      mem_setReg, mem_arithFlags, mxcsr_setReg, mxcsr_arithFlags]
  · simp only [Proof.Dsa.Limb.select, gpr_setReg, gpr_arithFlags,
      reduceCtorEq, ite_true, ite_false]
    rw [BitVec.xor_comm (s.gpr .rsi) (s.gpr .rdi), BitVec.xor_comm]
  · simp only [mem_setReg, mem_arithFlags]

private theorem lo_ct : ConstantTime isa (limbContract fun a b _ => Proof.Dsa.Limb.mulLo a b).pre
    (limbContract fun a b _ => Proof.Dsa.Limb.mulLo a b).pub Impl.Dsa.X86_64.mulLo := by
  refine ConstantTime.of_silent fun s t s' _ h => ?_
  rw [Impl.Dsa.X86_64.mulLo, Exec.block_iff] at h
  cases h
  rfl

private theorem hi_ct : ConstantTime isa (limbContract fun a b _ => Proof.Dsa.Limb.mulHi a b).pre
    (limbContract fun a b _ => Proof.Dsa.Limb.mulHi a b).pub Impl.Dsa.X86_64.mulHi := by
  refine ConstantTime.of_silent fun s t s' _ h => ?_
  rw [Impl.Dsa.X86_64.mulHi, Exec.block_iff] at h
  cases h
  rfl

private theorem select_ct : ConstantTime isa (limbContract Proof.Dsa.Limb.select).pre
    (limbContract Proof.Dsa.Limb.select).pub Impl.Dsa.X86_64.select := by
  refine ConstantTime.of_silent fun s t s' _ h => ?_
  rw [Impl.Dsa.X86_64.select, Exec.block_iff] at h
  cases h
  rfl

theorem mulLo_verified : Verified target Impl.Dsa.X86_64.mulLo (Proof.Dsa.Limb.mulLoContract abi) :=
  Verified.of_correct lo_correct lo_ct (by
    sig_implies [Proof.Dsa.Limb.mulLoContract, Proof.Dsa.Limb.mulSig, limbContract, abi, argRegs]
      [sat] using sat)

theorem mulHi_verified : Verified target Impl.Dsa.X86_64.mulHi (Proof.Dsa.Limb.mulHiContract abi) :=
  Verified.of_correct hi_correct hi_ct (by
    sig_implies [Proof.Dsa.Limb.mulHiContract, Proof.Dsa.Limb.mulSig, limbContract, abi, argRegs]
      [sat] using sat)

theorem select_verified : Verified target Impl.Dsa.X86_64.select (Proof.Dsa.Limb.selectContract abi) :=
  Verified.of_correct select_correct select_ct (by
    sig_implies [Proof.Dsa.Limb.selectContract, Proof.Dsa.Limb.selectSig, limbContract, abi, argRegs]
      [sat] using sat)

end VG.Proof.Dsa.X86_64
