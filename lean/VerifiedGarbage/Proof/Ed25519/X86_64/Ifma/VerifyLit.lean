module

public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.Taint
meta import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
meta import VerifiedGarbage.Proof.Framework.Lit
meta import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit

/-! Checked literals for verification's windows with AVX512_IFMA. -/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Ifma

materialize_code vdblLit := (.block vdbl : Prog isa)
materialize_code vaddBodyA := (.block (([.alu .sub .rbx (.imm 1)] : List Instr) ++ tableAddr 5376 ++ vrows ++
  esplit ++ vadd) : Prog isa)
materialize_code vbaseAdd := (.block (vrows ++ esplit ++ vadd) : Prog isa)
materialize_code vprepLit := (.block (VG.Impl.X25519.X86_64.Ifma.consts ++ vload) : Prog isa)
materialize_code vstoreLit := (.block vstore : Prog isa)

end VG.Proof.Ed25519.X86_64.Ifma
