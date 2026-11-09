module

public import VerifiedGarbage.Impl.P256.Booth
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
import VerifiedGarbage.Proof.EcKey.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Impl.P256.Booth
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombMixed
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CombOut
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P256Literals
meta import VerifiedGarbage.Proof.EcKey.AArch64.Lit
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lit
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot

/-! The comb that signing and public keys share is checked once, and their
literals read it.

The comb's forwarded field programs (`CombArithmetic.program`) are the
optimizer's output, which `Forward.CombMixed` and `Forward.CombOut` already
have as literals: the comb's literal is its code with those, by rewriting,
rather than the kernel running the optimizer again. -/

@[expose] public section

namespace VG.Impl.P256.Booth
open VG VG.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64

private theorem program_eq (k : CombArithmetic.Kind) :
    CombArithmetic.program CombArithmetic.K.M (CombArithmetic.operations k) =
      .block (VG.Proof.Weierstrass.AArch64.Forward.CombArithmetic.optimized k) := by
  rw [CombArithmetic.program,
    ite_eq_left ⟨rfl, List.mem_map.mpr ⟨k, by cases k <;> decide, rfl⟩⟩]
  rfl

/-- The comb's mixed addition is its field program's code. -/
theorem program_mixed : CombArithmetic.program CombArithmetic.K.M
    (maddJ CombArithmetic.K.S CombArithmetic.K.A CombArithmetic.K.E CombArithmetic.K.D) = .block mixed :=
  program_eq .mixed

theorem mixed_lit : mixed = VG.Proof.Weierstrass.AArch64.Forward.CombMixed.rightCode.lit :=
  VG.Proof.Weierstrass.AArch64.Forward.CombMixed.optimized_lit

materialize_code sign
materialize_code publicKey

end VG.Impl.P256.Booth
