module

public import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
public import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
public import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Registration
public import VerifiedGarbage.Proof.Framework.AddrArith
public import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Framework.RegSetOrder
public import VerifiedGarbage.Proof.Framework.RegionsSub
public import VerifiedGarbage.Proof.Framework.X86_64.Exec
public import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
public import VerifiedGarbage.Proof.Framework.X86_64.Masked
public import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
public import VerifiedGarbage.Proof.Framework.X86_64.RelCT
public import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
public import VerifiedGarbage.Proof.Poly1305.Stream
public import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall
public import VerifiedGarbage.Proof.Variants.Poly1305Blocks.X86_64

/-! # Poly1305 (RFC 8439 §2.5) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Poly1305.X86_64

def direct : List Artifact := [
  Spec.Poly1305.initApi.artifact X86_64.target {
    code := Impl.Poly1305.X86_64.init
    verified := Proof.Poly1305.X86_64.init_verified },
  Spec.Poly1305.finalizeApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratch 136 .rcx Impl.Poly1305.X86_64.finalize
    stack := 136
    verified := Proof.Poly1305.X86_64.finalize_framed }]

end VG.Artifacts.Poly1305.X86_64

-- Streaming Poly1305 (RFC 8439 §2.5) on x86-64
namespace VG.Artifacts.Poly1305.X86_64.Poly1305Blocks

open VG.Proof.Poly1305.X86_64 (BlocksImpl)

def artifacts (v : BlocksImpl) : List Artifact := [
  Spec.Poly1305.updateApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackScratch 136 .r8
      (Impl.Poly1305.X86_64.update v.name v.code)
    stack := 160
    verified := Proof.Poly1305.X86_64.update_framed v
    spSafe := X86_64.withStackScratch_spSafe_of (Proof.Poly1305.X86_64.update_spSafe v)
    features := v.features }]

end VG.Artifacts.Poly1305.X86_64.Poly1305Blocks

namespace VG.Artifacts.Poly1305.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Poly1305Blocks.X86_64.variants.flatMap fun v => Poly1305Blocks.artifacts v)

end VG.Artifacts.Poly1305.X86_64
