module

public import VerifiedGarbage.TCB.X86_64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Poly1305.Contract
import VerifiedGarbage.Impl.Poly1305.X86_64.Fn
import VerifiedGarbage.Proof.Poly1305.X86_64.Init
import VerifiedGarbage.Proof.Poly1305.X86_64.Scrub
import VerifiedGarbage.Proof.Poly1305.X86_64.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Blocks
import VerifiedGarbage.Proof.Poly1305.X86_64.Frame
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Lit
import VerifiedGarbage.Proof.Poly1305.X86_64.Ifma.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Registration
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.StackScratch
import VerifiedGarbage.Proof.Poly1305.Stream
import VerifiedGarbage.Proof.Poly1305.X86_64.UpdateCall
import VerifiedGarbage.Proof.Variants.Poly1305Blocks.X86_64
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # Poly1305 (RFC 8439 §2.5) on x86-64 -/

namespace VG.Artifacts.Poly1305.X86_64

def direct : List (Artifact X86_64.target) := [
  Spec.Poly1305.initApi.artifact X86_64.target { code := Impl.Poly1305.X86_64.Fn.init, verified := Proof.Poly1305.X86_64.init_scrubbed, spSafe := Proof.Poly1305.X86_64.init_spSafe },
  Spec.Poly1305.finalizeApi.artifact X86_64.target { code := Impl.Poly1305.X86_64.Fn.finalize, verified := Proof.Poly1305.X86_64.finalize_scrubbed, spSafe := Proof.Poly1305.X86_64.finalize_spSafe }]

open VG.Proof.Poly1305.X86_64 (BlocksImpl)

public def artifacts : List (Artifact X86_64.target) :=
  direct ++
  VG.Proof.Variants.Poly1305Blocks.X86_64.variants.map fun (v : BlocksImpl) =>
    Spec.Poly1305.updateApi.artifact X86_64.target {
      suffix := v.suffix
      code := Impl.Poly1305.X86_64.Fn.update v.upd.level v.upd.runs v.name v.code
      verified := Proof.Poly1305.X86_64.update_scrubbed v
      spSafe := Proof.Poly1305.X86_64.updateFn_spSafe v }

spec_apis artifacts

end VG.Artifacts.Poly1305.X86_64
