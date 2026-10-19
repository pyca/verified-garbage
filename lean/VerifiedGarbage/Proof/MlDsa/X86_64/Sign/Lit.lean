module

public import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
meta import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit
public import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sign.Sign
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.Inst
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Framework.X86_64.Words
meta import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlDsa.Sign.Bounds
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseCCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseDCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseKCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.PhaseOCT
meta import VerifiedGarbage.Proof.MlDsa.X86_64.Sign.SignCT
meta import VerifiedGarbage.Proof.MlKem.PolyW
meta import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
meta import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
meta import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
meta import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
meta import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
meta import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
meta import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
meta import VerifiedGarbage.Proof.MlKem.X86_64.VPack
meta import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
meta import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
meta import VerifiedGarbage.Proof.MlKem.X86_64.Zero
meta import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
meta import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-DSA signing on x86-64: its code without the arithmetic, as literals

The signing function of each parameter set with every function of the
polynomial arithmetic empty (`primsWith .empty`), which the checks that it
never writes `rsp`, uses no stack, calls at most so deep and loads MXCSR only
to restore it evaluate (`sign0_sp`, `sign0_ctlC`, `sign0_noSp`,
`sign0_depth`), as literals (`materialize_code`, `Proof/Framework/Lit.lean`).
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Sign

open VG.X86_64

/-- Signing with ML-DSA-44, without the arithmetic. -/
def sign44 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa44
/-- Signing with ML-DSA-65, without the arithmetic. -/
def sign65 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa65
/-- Signing with ML-DSA-87, without the arithmetic. -/
def sign87 : Prog isa := Impl.MlDsa.X86_64.Sign.sign (primsWith .empty) Spec.MlDsa.mlDsa87

materialize_code sign44
materialize_code sign65
materialize_code sign87

end VG.Proof.MlDsa.X86_64.Sign
