module

public import VerifiedGarbage.Proof.Bignum.X86.CrtPair
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Proof.Bignum.X86.CrtValue

/-! # Invalid public keys clear a public-length output with a fixed trace -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86 VG.Impl.Bignum.X86 VG.Proof.Dsa.X86

theorem failure_relCT (base : Addr) (bytes len : Nat) (args : Nat → BitVec 32) :
    RelCT isa (Pair base bytes len args) PublicFn.failure (fun _ _ => True) := by
  have Zero : RelCT isa (VG.X86.Taint.Agree loadTaint) (.block [.mov .eax (.imm 0)])
      (VG.X86.Taint.Agree loadTaint) := checkedProgramChange (hint := .block []) rfl rfl
  have Head := VG.RelCT.block_append (VG.RelCT.seq (loadArguments_relCT 0 1 (args 0) (args 1)) Zero)
  have Loop : RelCT isa (VG.X86.Taint.Agree loadTaint) (.loop (.block PublicFn.clearStep) .ne)
      (fun _ _ => True) := by
    apply RelCT.taint (A := taint) loadTaint (fun _ _ h => h)
      (hc := VG.Taint.hintOf taint loadTaint (.loop (.block PublicFn.clearStep) .ne))
    rfl
  apply (VG.RelCT.seq Head Loop).mono
  · intro s t H
    exact ⟨H.agree, (H.left.stack 0 (by decide)).readSrc, (H.right.stack 0 (by decide)).readSrc,
      (H.left.stack 1 (by decide)).readSrc, (H.right.stack 1 (by decide)).readSrc⟩
  · exact fun _ _ h => h

end VG.Proof.Bignum.X86.Crt
