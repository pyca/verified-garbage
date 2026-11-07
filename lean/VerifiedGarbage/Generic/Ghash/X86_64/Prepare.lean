module

public import VerifiedGarbage.Proof.Gcm.X86_64.PrepareCall
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # The 48 prepared powers of a key context, with calls of `vg_ghash`, on x86-64 -/

@[expose] public section

namespace VG.Generic.Ghash.X86_64.Prepare

open VG.Proof.AesGcm.X86_64 (GhashName)
open VG.Proof.Gcm.X86_64.PrepareCall (Gh)

/-- `vg_aes_gcm_prepare`, calling the implementation `n` of `vg_ghash`
(`Gh.ofName`). -/
def artifacts (n : GhashName) : List Artifact :=
  (Gh.ofName n).toList.map fun G =>
    Spec.Gcm.prepareApi.artifact X86_64.target {
      suffix := G.g.suffix
      code := Impl.Gcm.X86_64.PrepareCall.prepare G.g.fn.name G.g.fn.code
      stack := 8 + (8 + Impl.Gcm.X86_64.PrepareCall.scratchBytes)
      verified := Proof.Gcm.X86_64.PrepareCall.prepare_verified G
      spSafe := Proof.Gcm.X86_64.PrepareCall.prepare_spSafe G
      features := G.g.features }

end VG.Generic.Ghash.X86_64.Prepare
