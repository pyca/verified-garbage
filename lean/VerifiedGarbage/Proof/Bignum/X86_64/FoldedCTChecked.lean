module

public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedCTCode
public import VerifiedGarbage.Proof.Bignum.X86_64.FoldedChecked
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

@[expose] public section

namespace VG.Proof.Bignum.X86_64.FoldedPublic
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Rsa.X86_64.Checked
open VG.Proof.Bignum.X86_64 VG.Proof.Rsa.X86_64

theorem checked_ct (M : Mont)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    ConstantTime isa pdContract.pre pdContract.pub (Folded.checked M.mm) :=
  guarded_ct (code_constantTime M hfinal) (fun _ h => pdGeom h) (fun s t hs h => (pdPre_same hs).symm ▸ h)
    (fun _ _ _ _ hp => ⟨fun r hr => hp.1 r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      rcases hr with rfl | rfl | rfl | rfl <;> simp), hp.2.2.2.2.2.2⟩)
    fun _ _ _ _ h₁ h₂ hp => pdPub_same h₁ h₂ hp

/-- `vg_rsa_public_precomputed_checked` with Montgomery multiplication `M`,
given that its code never loads MXCSR (which the registration file
evaluates) and that the last multiplication, by the input, leaks only the
public data (`hfinal`). -/
theorem checked_verified (M : Mont)
    (hmx : (Folded.code M.mm).allInstrs (fun i => !loadsMxcsr i) = true)
    (hfinal : RelCT isa (Two GoodL) (M.mm aY aX aY) (fun _ _ => True)) :
    Verified target (Folded.checked M.mm) (Spec.Rsa.publicPrecomputedCheckedContract abi) :=
  Verified.of_correct (k := pdChkContract) (checked_correct M hmx)
    (checked_ct M hfinal) precomputedChecked_implies

end VG.Proof.Bignum.X86_64.FoldedPublic
