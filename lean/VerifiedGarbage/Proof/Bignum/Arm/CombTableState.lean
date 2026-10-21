module

public import VerifiedGarbage.Spec.Rsa.FixedBaseComb
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Framework.Mem

/-! Read-only, densely packed five-tooth comb tables. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont

/-- `table` points to entry zero, after the context metadata and p/R² prefix. -/
structure CombTable (table : BitVec 32) (w p g bits : Nat) (s : State) : Prop where
  positive : 0 < w
  fits : table.toNat + 32 * (8*w) ≤ 2^32
  readable : InRegions (s.rd ++ s.wr) (State.addr table) (32*(8*w))
  values : ∀ digit < 32, val32 s.mem (State.addr table) (8*w*digit) (2*w) =
    Spec.Rsa.powMod g (Spec.Rsa.FixedBaseComb.exponent bits digit) p * 2^(64*w) % p

end VG.Proof.Bignum.Arm
