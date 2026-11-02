module

public import VerifiedGarbage.Impl.Ecdsa.Secp256k1.RISCV64
public import VerifiedGarbage.Proof.Weierstrass.RISCV64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Weierstrass.MulContract
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Gen4
import VerifiedGarbage.Proof.Weierstrass.RISCV64.Secp256k1Field.Lit
import VerifiedGarbage.Proof.Framework.Omega

/-!
# secp256k1's field on RISC-V, for `vg_secp256k1_mul` and its callers

The facts the proofs of `vg_secp256k1_mul` (`Proof/Ecdsa/RISCV64/Secp256k1/Window.lean`)
and its callers share: secp256k1's field functions meet the contracts by register
(`field_ok`), and `R = 2²⁵⁶` is a unit modulo `p` (`unit`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.RISCV64.Secp256k1

open VG VG.RISCV64 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.RISCV64 VG.Impl.Ecdsa.RISCV64
open VG.Proof.Mont VG.Proof.Weierstrass VG.Proof.Weierstrass.RISCV64
open VG.Spec.Weierstrass (Curve Fe Point)

/-- secp256k1. -/
abbrev W : Curve := Spec.Secp256k1.curve

private theorem p_ok : Gen4.Ok Impl.Weierstrass.Mont.secp256k1p.m := ⟨by decide, by decide, by decide⟩

theorem field_ok : FieldOk secp256k1Field :=
  ⟨Gen4.mul_rv rfl p_ok, Gen4.add_rv rfl p_ok, Gen4.sub_rv rfl p_ok, Impl.Weierstrass.RISCV64.Secp256k1Field.mulFn_noFrames,
    Impl.Weierstrass.RISCV64.Secp256k1Field.addFn_noFrames, Impl.Weierstrass.RISCV64.Secp256k1Field.subFn_noFrames⟩

instance : NeZero secp256k1Field.S.m := ⟨by decide⟩

theorem p_odd : W.p % 2 = 1 := by decide

theorem unit : UnitMod W.p (2 ^ (64 * 4)) := unitMod_pow_two p_odd _

/-- The number at slot `i`. -/
abbrev sv (base : Addr) (s : State) (i : Nat) : Nat := wordsVal s.mem base (secp256k1.sl i) 4

end VG.Proof.Ecdsa.RISCV64.Secp256k1
