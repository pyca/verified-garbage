module

public import VerifiedGarbage.Proof.AesOcb.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.StackArgScratch
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Impl.AesCcm.X86_64
public import VerifiedGarbage.Impl.CmacAes.Stream.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64
public import VerifiedGarbage.Impl.Gcm.X86_64.Pclmul
public import VerifiedGarbage.Proof.Aes.X86_64.AesNi.ExpandKey
public import VerifiedGarbage.Proof.Aes.X86_64.Decrypt
public import VerifiedGarbage.Proof.Aes.X86_64.Vaes.Rounds
public import VerifiedGarbage.Proof.Aes.X86_64.VaesBlocks.Dec
public import VerifiedGarbage.Proof.AesCcm.Ctr
public import VerifiedGarbage.Proof.AesCcm.Mac
public import VerifiedGarbage.Proof.AesCcm.X86_64.Bytes
public import VerifiedGarbage.Proof.AesCcm.X86_64.Callee
public import VerifiedGarbage.Proof.AesCcm.X86_64.Contract
public import VerifiedGarbage.Proof.AesCcm.X86_64.Run
public import VerifiedGarbage.Proof.AesGcm.X86_64.Loops
public import VerifiedGarbage.Proof.AesOcb.X86_64.Hash
public import VerifiedGarbage.Proof.AesOcb.X86_64.HashFill
public import VerifiedGarbage.Proof.AesOcb.X86_64.InitCT
public import VerifiedGarbage.Proof.AesOcb.X86_64.NonceBlock
public import VerifiedGarbage.Proof.AesOcb.X86_64.Offset0
public import VerifiedGarbage.Proof.AesOcb.X86_64.PadTo
public import VerifiedGarbage.Proof.AesOcb.X86_64.Run
public import VerifiedGarbage.Proof.AesOcb.X86_64.Seal
public import VerifiedGarbage.Proof.Cmac.Dbl32
public import VerifiedGarbage.Proof.Cmac.Frame
public import VerifiedGarbage.Proof.Cmac.Spec
public import VerifiedGarbage.Proof.Cmac.Stream
public import VerifiedGarbage.Proof.CmacAes.X86_64.Dbl
public import VerifiedGarbage.Proof.CmacAes.X86_64.Finalize
public import VerifiedGarbage.Proof.CmacAes.X86_64.FinalizeCorrect
public import VerifiedGarbage.Proof.CmacAes.X86_64.UpdateCorrect
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.OffsetBelow
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Framework.X86_64.Avx
public import VerifiedGarbage.Proof.Framework.X86_64.Bswap
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
public import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.Sse
public import VerifiedGarbage.Proof.Gcm.Bits
public import VerifiedGarbage.Proof.Gcm.Spec
public import VerifiedGarbage.Proof.Gcm.Stream
public import VerifiedGarbage.Proof.Gcm.X86_64.Bits
public import VerifiedGarbage.Spec.Ccm.Contract
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-OCB (RFC 7253) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesOcb

open VG.Proof.AesOcb.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Ocb.initApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 2568 .rcx (Impl.AesOcb.X86_64.init (callees v))
    stack := 2576
    verified := init_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (init_spSafe v)
    features := v.features },
  Spec.Ocb.sealApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.seal (callees v))
    stack := 3640
    verified := Proof.AesOcb.seal_keyed (seal_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (seal_spSafe v)
    features := v.features },
  Spec.Ocb.openApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratch 3632 4 (Impl.AesOcb.X86_64.open (callees v))
    stack := 3640
    verified := Proof.AesOcb.open_keyed (open_framed v)
    spSafe := X86_64.withStackArgScratch_spSafe (open_spSafe v)
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOcb
