module
public import VerifiedGarbage.Impl.Rsa.X86_64.Folded
public import VerifiedGarbage.Proof.Bignum.X86_64.PdCode
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Rsa.X86_64.Guarded

import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTCode
import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
public import VerifiedGarbage.Proof.Rsa.Contract

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

/-- `Checked.guarded` of code that is constant time for valid `e`s. -/
theorem guardedPd_ct {code : Prog isa}
    (hcode : ConstantTime isa (fun s => pdContract.pre s ∧ Rsa.X86_64.eValid s = true) pdContract.pub code) :
    ConstantTime isa pdContract.pre pdContract.pub (Checked.guarded code) :=
  guarded_ct hcode (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

theorem checked_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) :=
  guardedPd_ct (code_constantTime M hfinal)

end VG.Proof.Bignum.X86_64.FoldedPublic
