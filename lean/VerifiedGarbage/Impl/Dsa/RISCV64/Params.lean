module

public import VerifiedGarbage.Impl.Dsa.RISCV64.Common

/-!
# DSA domain checks on RISC-V

`vg_dsa_check_parameters(params = a0, params_len = a1, p_len = a2,
q_len = a3, scratch = a4, scratch_len = a5)`. As on PPC64LE
(`Impl/Dsa/PPC64LE/Params.lean`): after an entry like verification's, which
saves the callee-saved registers in `scratch`'s header and keeps the domain
p||q||g in `s11` and the lengths in the header, `checkParams`
(`Common.lean`) branches on the domain, all of it public, and leaves 1 or 0.
-/

@[expose] public section

namespace VG.Impl.Dsa.RISCV64.Params

open VG VG.RISCV64 VG.Impl.Dsa.RISCV64

/-- The working space, the registers saved there, the domain into `s11`
(`ra`, which names the signature elsewhere, 0), and the lengths into the
header. -/
def entry : List Instr :=
  [.addi .t2 .a4 0] ++ save .t2 ++
    [.addi .s11 .a0 0, .li .ra 0, .shift .sll .d .t3 .a3 16, .add .t3 .a2 .t3, .store .d .t3 .s6 hLens]

/-- `vg_dsa_check_parameters`. -/
def checkParameters : Prog isa :=
  .seq (.block entry) (.seq (checkParams (.block [.li .a0 1]) (.block [.li .a0 0])) (.block restore))

end VG.Impl.Dsa.RISCV64.Params
