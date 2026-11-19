module

public import VerifiedGarbage.Spec.Poly1305.Contract
public import VerifiedGarbage.Proof.Framework.AArch64.ScrubProved
public import VerifiedGarbage.Proof.Poly1305.AArch64.Init
public import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Frame
public import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Update
import VerifiedGarbage.Proof.Poly1305.AArch64.Radix64.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Vector.Lit
import VerifiedGarbage.Proof.Poly1305.AArch64.Lit
import VerifiedGarbage.Proof.Poly1305.Scratch

/-!
# Poly1305's streaming functions on AArch64, without secret residue

The postconditions of `update` and `finalize` read the memory on return only
within their buffers (`Proof/Poly1305/Scratch.lean`): each returns with every
register it may leave secret cleared and its 128 bytes of stack, the frame of
its scratch space, zeroed (`Impl.Poly1305.AArch64.Fn`, whose theorems are at
the end).
-/

@[expose] public section

namespace VG.Proof.Poly1305.AArch64.Scrub

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Poly1305

theorem updateOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (updateContract abi W) W (updateSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := updateSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Poly1305.updatePostOut_local 64)

theorem finalizeOk (W : Nat) (hW : 0 < W := by decide) :
    ScrubAllOk (finalizeContract abi W) W (finalizeSig.retBits abi.ptrBits) :=
  scrubAllOk_regs (sig := finalizeSig) (Nat.le_of_ble_eq_true rfl) hW (Nat.le_refl _)
    (Proof.Poly1305.finalizePostOut_local 64)

end VG.Proof.Poly1305.AArch64.Scrub

/-! ## The functions

The code that is emitted (`Impl.Poly1305.AArch64.init` and
`Impl.Poly1305.AArch64.Fn`) meets each function's contract in constant time
and returns without secret residue. -/

namespace VG.Proof.Poly1305.AArch64.Fn

open VG.AArch64 VG.AArch64.ScrubAll VG.Spec.Poly1305

theorem init : VerifiedScrubbed target Impl.Poly1305.AArch64.init (initContract abi) 0 :=
  ⟨init_verified, init_noResidue _⟩

theorem update : VerifiedScrubbed target Impl.Poly1305.AArch64.Fn.update (updateContract abi 128) 0 :=
  verifiedScrubbed (api := updateApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Radix64.update,
      verified := Radix64.update_framed }
    _ (Scrub.updateOk 128) (by dsimp only; lit_decide)

theorem updateNeon : VerifiedScrubbed target Impl.Poly1305.AArch64.Fn.updateNeon (updateContract abi 128) 0 :=
  verifiedScrubbed (api := updateApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 128 .x4 Impl.Poly1305.AArch64.Vector.update,
      verified := Vector.update_framed }
    _ (Scrub.updateOk 128) (by dsimp only; lit_decide)

theorem finalize : VerifiedScrubbed target Impl.Poly1305.AArch64.Fn.finalize (finalizeContract abi 128) 0 :=
  verifiedScrubbed (api := finalizeApi)
    { code := Impl.StackScratch.AArch64.withStackScratch 128 .x3 Impl.Poly1305.AArch64.Radix64.finalize,
      verified := Radix64.finalize_framed }
    _ (Scrub.finalizeOk 128) (by dsimp only; lit_decide)

end VG.Proof.Poly1305.AArch64.Fn
