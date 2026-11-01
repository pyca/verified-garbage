module

public import VerifiedGarbage.Proof.TripleDes.X86.Frame
public import VerifiedGarbage.Proof.TripleDes.X86.VerifiedBlock
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.TripleDes.X86.FunctionsLit
public import VerifiedGarbage.Proof.Framework.CallLay
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.X86.Mmx
public import VerifiedGarbage.Proof.Framework.X86.Sse
public import VerifiedGarbage.Proof.Framework.X86.SseDword
public import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
public import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
public import VerifiedGarbage.Proof.Rc2.Select
public import VerifiedGarbage.Proof.Rc2.Select32
public import VerifiedGarbage.Proof.Rc2.Word
public import VerifiedGarbage.Proof.Rc2.Word32
public import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
public import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
public import VerifiedGarbage.Proof.Rc2.X86.KeyIO
public import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
public import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
public import VerifiedGarbage.Proof.TripleDes.Bytes
public import VerifiedGarbage.Proof.TripleDes.EcbMemory
public import VerifiedGarbage.Proof.TripleDes.Permutation
public import VerifiedGarbage.Proof.TripleDes.Round
public import VerifiedGarbage.Proof.TripleDes.Schedule
public import VerifiedGarbage.Proof.TripleDes.Word
public import VerifiedGarbage.Proof.TripleDes.X86.BlockCT
public import VerifiedGarbage.Proof.TripleDes.X86.Bytes
public import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
public import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
public import VerifiedGarbage.Proof.TripleDes.X86.WordStore
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.X86.Mmx
import VerifiedGarbage.Proof.Framework.X86.Sse
import VerifiedGarbage.Proof.Framework.X86.SseDword
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Framework.X86.StackScratchWipe
import VerifiedGarbage.Proof.Rc2.Select
import VerifiedGarbage.Proof.Rc2.Select32
import VerifiedGarbage.Proof.Rc2.Word
import VerifiedGarbage.Proof.Rc2.Word32
import VerifiedGarbage.Proof.Rc2.X86.BlockArgs
import VerifiedGarbage.Proof.Rc2.X86.Cbc.CallFrame
import VerifiedGarbage.Proof.Rc2.X86.KeyIO
import VerifiedGarbage.Proof.Rc2.X86.KeyLookup
import VerifiedGarbage.Proof.Rc2.X86.RoundSteps
import VerifiedGarbage.Proof.TripleDes.Bytes
import VerifiedGarbage.Proof.TripleDes.EcbMemory
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round
import VerifiedGarbage.Proof.TripleDes.Schedule
import VerifiedGarbage.Proof.TripleDes.Word
import VerifiedGarbage.Proof.TripleDes.X86.BlockCT
import VerifiedGarbage.Proof.TripleDes.X86.Bytes
import VerifiedGarbage.Proof.TripleDes.X86.Ecb.Verified
import VerifiedGarbage.Proof.TripleDes.X86.RestoredOutput
import VerifiedGarbage.Proof.TripleDes.X86.WordStore

@[expose] public section

namespace VG.Artifacts.TripleDes.X86

def artifacts : List Artifact := [
  Spec.TripleDes.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 532 3 128 Impl.TripleDes.X86.Key.expandKey
    stack := 532
    verified := Proof.TripleDes.X86.expandKey_framed },
  Spec.TripleDes.ecbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.encrypt
    stack := 1060
    verified := Proof.TripleDes.X86.ecb_framed .encrypt },
  Spec.TripleDes.ecbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1044 3 256 Impl.TripleDes.X86.Ecb.decrypt
    stack := 1060
    verified := Proof.TripleDes.X86.ecb_framed .decrypt }]

end VG.Artifacts.TripleDes.X86
