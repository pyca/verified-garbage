module
public import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState

import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructReadyCT
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeCT
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.OmegaLit
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.RsaKeyGen.Hdr
meta import VerifiedGarbage.Impl.Dsa.AArch64.Generation.PConstruct
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructCTState
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PConstructReadyCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Generation.PShapeCT
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.OmegaLit
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.RsaKeyGen.Hdr

/-! # Constant time of complete p construction at every supported DSA size -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64
open VG.Proof.Pbkdf2.Md.AArch64 VG.Impl.Dsa.AArch64.Generation

theorem pConstruct_ct_of {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) (hq : qLen = 20 ∨ qLen = 32)
    (hc : (8 * pLen - 1) / (8 * qLen) ≤ 11) (hp : pLen ≤ 1024)
    {hc₁ hc₂ : VG.Taint.Hint VG.AArch64.Taint.T}
    (ht₁ : (taint.check (Taint.ofRegs [.x0]) (workspace (pLen / 8)) hc₁).isSome = true)
    (ht₂ : (taint.check (Taint.ofRegs [.x0])
      (.block (headerArguments (candidateArguments pLen qLen))) hc₂).isSome = true) :
    RelCT isa (Two (PConstructBefore H pLen qLen)) (pConstruct G pLen qLen) (fun _ _ => True) := by
  refine RelCT.seq (two_post (two_map PConstructPublic.hash (fun _ _ h => pConstruct_hash h)
    (pBuild_ct hG H hmatch hsize qLen ((8 * pLen - 1) / (8 * qLen)) pLen hq hd hc hp))
    (fun _ _ h => pConstruct_ready hG hmatch hsize hhash hseedsize hd h)) ?_
  exact two_map (fun p => p.workspace H) (fun _ _ h => h) (reduceFromFrame_ct (pLen / 8) pLen qLen ht₁ ht₂)

def GenerationSizes (pLen qLen : Nat) : Prop :=
  (pLen = 128 ∧ qLen = 20) ∨ (pLen = 256 ∧ qLen = 32) ∨ (pLen = 384 ∧ qLen = 32)

theorem pConstruct_ct {G : Impl.Pbkdf2.Md.AArch64.Hash} (hG : Calls.StreamOK G.stream)
    (H : Spec.Mgf1.Hash) (pLen qLen : Nat)
    (sizes : GenerationSizes pLen qLen)
    (hmatch : ∀ x, H.hash x = hG.SH.H.hash x) (hsize : ∀ x, (H.hash x).length = G.D)
    (hhash : ∀ bs, H.hash bs = Spec.Dsa.seedHash (8 * qLen) bs)
    (hseedsize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * qLen) bs).length = 8 * qLen)
    (hd : G.D = qLen) :
    RelCT isa (Two (PConstructBefore H pLen qLen)) (pConstruct G pLen qLen) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals
    exact pConstruct_ct_of hG H _ _ hmatch hsize hhash hseedsize hd
      (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)

end VG.Proof.Dsa.AArch64.Generation
