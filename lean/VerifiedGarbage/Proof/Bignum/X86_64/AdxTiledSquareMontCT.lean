import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledSquareRawCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxTiledMontCT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRotate8CT
import VerifiedGarbage.Proof.Bignum.X86_64.AdxCT

namespace VG.Proof.Bignum.X86_64.AdxTiledSquare
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.Bignum.X86_64

open VG.Proof.Bignum.X86_64.AdxTiledProduct (Layout GoodV pins_goodV)

theorem montSquare_ct {ps : List (Nat × Nat)} {co ca o a : Nat} (po : (co, o) ∈ ps) (pa : (ca, a) ∈ ps)
    (ha : a<8) (ha1 : a≠aAcc) (ha2 : a≠aTmp)
    {h₁ h₂ h₃ h₄ : VG.Taint.Hint VG.X86_64.Taint.T}
    (hS : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.setup ca)) h₁).isSome=true)
    (hR : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxRect8.setup ca ca)) h₂).isSome=true)
    (hF : (taint.check (Taint.ofRegs [.rdi]) (.block (Adx.finishBases co)) h₃).isSome=true)
    (hT : (taint.check (Taint.ofRegs [.rdi]) (.block (AdxTri8.setup ca)) h₄).isSome=true) :
    RelCT isa (Two (GoodV ps)) (AdxTiledSquare.montSquare co ca) (fun _ _ => True) :=
  RelCT.seq (two_post (raw_ct pa ha ha1 ha2 hS hR hT) (raw_fw pa ha ha1 ha2))
    (AdxTiledProduct.redcFinish_ct (P := fun _ => ps) (L := id) (O := fun _ => o) (fun _ => po) hF)

end VG.Proof.Bignum.X86_64.AdxTiledSquare
