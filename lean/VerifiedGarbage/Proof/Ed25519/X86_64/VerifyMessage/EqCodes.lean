module

import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyCode
public import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyMessage.CT
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyLit
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyLit
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBasePrecomputed
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Decode
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.ScalarBytes
import VerifiedGarbage.Proof.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Proof.Ed25519.X86_64.Bits
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodePowers
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.VerifyCT
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEqual
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.RecoverCTBlocks
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowDigits
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowSlideCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Cold
import VerifiedGarbage.Proof.Framework.EntryBranch
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Bswap
import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
import VerifiedGarbage.Proof.Framework.X86_64.StackScratchWipe
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Hmac.AnyKey
import VerifiedGarbage.Proof.Hmac.Common
import VerifiedGarbage.Proof.Hmac.Generic.Implies
import VerifiedGarbage.Proof.MdStream.OneShot
import VerifiedGarbage.Proof.MdStream.Prefix
import VerifiedGarbage.Proof.MdStream.X86_64.Words
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.AnyKeyEntry
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PadW
import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Words
import VerifiedGarbage.Proof.Pbkdf2.Memory
import VerifiedGarbage.Proof.Pbkdf2.Scratch
import VerifiedGarbage.Proof.Pbkdf2.X86_64.Copy
import VerifiedGarbage.Proof.Sha256.StateMem
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha512.Word64
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Compress
import VerifiedGarbage.Proof.Sha512.X86_64.Shared
import VerifiedGarbage.Proof.Sha512.X86_64.Stream.Init
import VerifiedGarbage.Proof.Weierstrass.X86_64.CallVerified
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Step
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-!
# The equations the verification over SHA-512 calls

`EqCode` of each registered `vg_ed25519_verify_equation`, which
`Generic/MdHash/X86_64/Ed25519.lean` passes to the verification it makes
with each SHA-512 backend.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.VerifyCode

open VG.Impl.Ed25519.X86_64

theorem baseline_eq :
    VerifyMessage.EqCode Impl.X25519.X86_64.baseline (windows Impl.X25519.X86_64.baseline) :=
  ⟨baseline_call, baseline_noSp, by lit_decide, baseline_spSafe⟩

theorem adx_eq : VerifyMessage.EqCode Impl.X25519.X86_64.adx (windows Impl.X25519.X86_64.adx) :=
  ⟨adx_call, adx_noSp, by lit_decide, adx_spSafe⟩

theorem ifma_eq : VerifyMessage.EqCode Impl.X25519.X86_64.adx Ifma.windows :=
  ⟨ifma_call, ifma_noSp, by lit_decide, ifma_spSafe⟩

end VG.Proof.Ed25519.X86_64.VerifyCode
