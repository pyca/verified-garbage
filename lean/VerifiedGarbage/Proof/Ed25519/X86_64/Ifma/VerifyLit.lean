import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma

/-! Checked literals for verification's windows with AVX512_IFMA. -/

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma

materialize_code vdbl4Lit := (vdbl4 : Prog isa)
materialize_code vaddBodyA := (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ vrows ++
  esplit ++ vadd) : Prog isa)
materialize_code vaddBodyB := (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 2048 ++ vrows ++
  esplit ++ vadd) : Prog isa)
materialize_code vprepLit := (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload) : Prog isa)
materialize_code vstoreLit := (.block vstore : Prog isa)

end VG.Proof.Ed25519.X86_64.Ifma
