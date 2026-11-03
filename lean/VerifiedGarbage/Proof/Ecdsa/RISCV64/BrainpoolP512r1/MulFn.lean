module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.GenWide.Sqr
import VerifiedGarbage.Proof.Weierstrass.RISCV64.BrainpoolP512r1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# brainpoolP512r1's field on RISC-V, for `vg_brainpoolp512r1_mul` and its callers

The facts the proofs of `vg_brainpoolp512r1_mul` (`Proof/Ecdsa/RISCV64/BrainpoolP512r1/Window.lean`)
and its callers share: brainpoolP512r1's field functions, those modulo any wide
modulus (`Proof/Weierstrass/RISCV64/GenWide/Field.lean`) for its `p` (`p_ok`), the
product squaring when its operands are the same (`Proof/Weierstrass/RISCV64/GenWide/Sqr.lean`),
meet the contracts by register (`field_ok`), and `R = 2⁵¹²` is a unit modulo `p` (`unit`).
-/

-- `p`, below `2^512`, is evaluated.
set_option exponentiation.threshold 1024

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- brainpoolP512r1. -/
abbrev W : Curve := Spec.BrainpoolP512r1.curve

private theorem p_ok : GenWide.WideOk Impl.Weierstrass.Mont.brainpoolp512r1p := ⟨by decide, by decide, by decide, by decide⟩

theorem field_ok : FieldOk brainpoolp512r1Field :=
  ⟨GenWide.mulSq_rv p_ok, GenWide.add_rv p_ok, GenWide.sub_rv p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFn_noFrames,
    GenWide.mulSqA_rv p_ok, GenWide.addA_rv p_ok, GenWide.subA_rv p_ok,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.mulFnA_noFrames,
    Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.addFnA_noFrames, Impl.Weierstrass.RISCV64.BrainpoolP512r1Field.subFnA_noFrames⟩

instance : NeZero brainpoolp512r1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 8)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (brainpoolp512r1.sl i) 8

end VG.Proof.Ecdsa.RISCV64.BrainpoolP512r1
