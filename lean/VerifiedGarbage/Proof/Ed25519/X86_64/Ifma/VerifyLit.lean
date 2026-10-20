module

public import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Mem
meta import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyIfma
import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Impl.Ed25519.X86_64.PointEncode
meta import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Verify
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.TCB.X86_64.Target

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
