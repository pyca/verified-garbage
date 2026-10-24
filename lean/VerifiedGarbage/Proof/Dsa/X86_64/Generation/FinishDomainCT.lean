module

public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedValidateCT
public import VerifiedGarbage.Impl.Dsa.X86_64.Generation.SeedSearch
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.PackCT
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.SeedPack
import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FinishDomain
public import VerifiedGarbage.Proof.Dsa.Generation.ParamsEncoding
import VerifiedGarbage.Proof.Dsa.X86_64.Generation.FinishDomain

/-! # Compose domain packing with the final verified parameter check -/

@[expose] public section
namespace VG.Proof.Dsa.X86_64.Generation
open VG VG.X86_64 VG.Proof.Bignum VG.Proof.Bignum.X86_64
open VG.Impl.Dsa.Generation.Layout


variable {checkName : String}

structure DomainFinishPublic where
  context : GenerationContext
  params : Spec.Dsa.Params

def DomainFinishPublic.validation (p : DomainFinishPublic) : ValidationContext :=
  ⟨p.context, Spec.Dsa.encodeParams p.context.geo.pLen p.context.geo.qLen p.params,
    VG.Proof.Dsa.Generation.encodeParams_length _ _ _⟩

def DomainFinishBefore (pLen qLen : Nat) (p : DomainFinishPublic) (s : State) : Prop :=
  GenerationMemoryBefore p.context s ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B VG.Impl.Dsa.Generation.Layout.p) p.context.geo.pLen =
    Spec.Dsa.encodeBE p.context.geo.pLen p.params.p ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B q) p.context.geo.qLen =
    Spec.Dsa.encodeBE p.context.geo.qLen p.params.q ∧
  Spec.Rsa.bytesAt s.mem (off p.context.geo.B g) p.context.geo.pLen =
    Spec.Dsa.encodeBE p.context.geo.pLen p.params.g ∧
  p.context.geo.pLen = pLen ∧ p.context.geo.qLen = qLen

theorem domainFinish_pack {pLen qLen : Nat} {p : DomainFinishPublic} {s : State}
    (h : DomainFinishBefore pLen qLen p s) :
    WP isa (Impl.Dsa.X86_64.Generation.pack pLen qLen) s (SeedValidateBefore pLen qLen p.validation) := by
  obtain ⟨⟨W, hm⟩, bp, bq, bg, hp, hq⟩ := h
  have step := seedPack_ok hm _ _ _ (VG.Proof.Dsa.encodeBE_length _ _)
    (VG.Proof.Dsa.encodeBE_length _ _) (VG.Proof.Dsa.encodeBE_length _ _) bp bq bg
  rw [hp, hq] at step
  refine WP.mono step fun t ⟨ht, bytes, _, _, _⟩ => ⟨⟨W, ht⟩, ?_, hp, hq⟩
  change Spec.Rsa.bytesAt t.mem (off p.context.geo.B packed) (2 * p.context.geo.pLen + p.context.geo.qLen) =
    Spec.Dsa.encodeParams p.context.geo.pLen p.context.geo.qLen p.params
  simpa only [Spec.Dsa.encodeParams, hp, hq] using bytes

theorem finishDomain_ct (M : Mont) (Sq : MontS) (pLen qLen : Nat)
    (sizes : (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)) :
    RelCT isa (Two (DomainFinishBefore pLen qLen))
      (Impl.Dsa.X86_64.Generation.finishDomain (checkName := checkName) Sq.mm M.mm pLen qLen) (fun _ _ => True) := by
  unfold Impl.Dsa.X86_64.Generation.finishDomain
  refine RelCT.seq (two_post
    ((two_map DomainFinishPublic.context (fun _ _ h => h.1) (pack_ct pLen qLen sizes)).mono
      (fun _ _ h => h) (fun _ _ _ => True.intro)) (fun _ _ h => domainFinish_pack h)) ?_
  exact two_map DomainFinishPublic.validation (fun _ _ h => h) (seedValidate_ct (checkName := checkName) M Sq pLen qLen sizes)

end VG.Proof.Dsa.X86_64.Generation
