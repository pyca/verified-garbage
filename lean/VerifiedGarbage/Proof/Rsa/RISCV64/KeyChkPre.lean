module

public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.TCB.RISCV64.Target
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.Proof.Framework.Contract

@[expose] public section

namespace VG.Proof.Rsa.RISCV64.KeyCheck

open VG VG.RISCV64

theorem stackArgs_ten (s : State) :
    List.map (stackArg s) (List.range 10) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7, stackArg s 8, stackArg s 9] := rfl

theorem stackArgs_eight (s : State) :
    List.map (stackArg s) (List.range 8) = [stackArg s 0, stackArg s 1, stackArg s 2, stackArg s 3,
      stackArg s 4, stackArg s 5, stackArg s 6, stackArg s 7] := rfl

example (s : State) (h : (Spec.Rsa.checkKeyContract RISCV64.abi).pre s) : False := by
  sig_pre [Spec.Rsa.checkKeyContract, Spec.Rsa.checkKeySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_ten, List.append_eq, List.range, List.range.loop] at h
  trace_state
  sorry

example (s : State) (h : (Spec.Rsa.checkCrtKeyContract RISCV64.abi).pre s) : False := by
  sig_pre [Spec.Rsa.checkCrtKeyContract, Spec.Rsa.checkCrtKeySig, RISCV64.abi, RISCV64.argRegs,
    stackArgs_eight, List.append_eq, List.range, List.range.loop] at h
  trace_state
  sorry

end VG.Proof.Rsa.RISCV64.KeyCheck
