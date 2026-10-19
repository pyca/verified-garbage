module

public import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Contract
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Lit
meta import VerifiedGarbage.Proof.Ecdsa.Rfc6979.AArch64.Curve
public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
import Mathlib.Tactic.ClearExcept
meta import Mathlib.Tactic.ClearExcept
import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Mont.AArch64.Rounds
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
meta import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP256r1.Config
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Mont.AArch64.Blocks
meta import VerifiedGarbage.Proof.Mont.AArch64.Chain
meta import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
meta import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
meta import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
meta import VerifiedGarbage.Proof.Mont.AArch64.Rounds
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
public import VerifiedGarbage.Impl.Ecdh.BrainpoolP256r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
public import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
public import VerifiedGarbage.Proof.Framework.AArch64.Lit
public import VerifiedGarbage.Proof.Framework.BitByte
public import VerifiedGarbage.Proof.Framework.Range
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P384Mul.Reduce
public import VerifiedGarbage.Proof.Mont.AArch64.P384Sqr.Square
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Function
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Product
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross0
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross1
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross2
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductCross3
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDiag
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductDouble
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductLow
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ProductTop
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Reduction
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionBits
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionCorrect
public import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
public import VerifiedGarbage.Proof.Mont.AArch64.RowInit
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
public import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
public import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
public import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
public import VerifiedGarbage.Proof.Weierstrass.Pow

/-!
# Deterministic ECDSA on AArch64: brainpoolP256r1

brainpoolp256r1 as the proof's curve (`brainpoolp256r1`): scalars of 32 bytes in 4 words, the
order `n` of exactly 256 bits with `2^256 < 2 n`, and `vg_ecdsa_brainpoolp256r1_sign`,
proven correct (given the group law, the inversions' soundness) and constant time against its contract (`coreK` at brainpoolP256r1's sizes,
which is `Proof.Ecdsa.AArch64.BrainpoolP256r1.signAArch64`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Rfc6979.AArch64

open VG VG.AArch64

theorem empty_disjoint (a : Addr) (r : Region) : Region.Disjoint ⟨a, 0⟩ r := by
  intro x hx
  simp only [Region.Contains] at hx
  omega

theorem coreK_brainpoolp256r1 : coreK Impl.Ecdsa.AArch64.brainpoolp256r1 =
    Proof.Ecdsa.AArch64.BrainpoolP256r1.signAArch64 := by
  have fit : (0 : Addr).toNat + 0 ≤ 2 ^ 64 := by decide
  simp only [fit, coreK, tableRegions, tableAddr, TblOk, Impl.Ecdsa.AArch64.brainpoolp256r1,
    Impl.Ecdsa.AArch64.Cfg.combWords, Impl.Weierstrass.tcombWords,
    List.isEmpty_nil, ↓reduceIte, List.flatMap_nil, List.length_nil,
    List.append_nil, Nat.mul_zero, Nat.not_lt_zero, false_implies, implies_true,
    empty_disjoint, and_true, Proof.Ecdsa.AArch64.BrainpoolP256r1.signAArch64]
  rfl

/-- brainpoolp256r1, with the group law `hL`, the inversions' soundness `hI`. -/
def brainpoolp256r1 (hL : Weierstrass.Law Spec.BrainpoolP256r1.curve) (hI : Weierstrass.AArch64.InvSounds) : RfcCurve where
  E := Impl.Ecdsa.AArch64.brainpoolp256r1
  inst := Spec.Ecdsa.BrainpoolP256r1.inst
  curve := rfl
  wide := false
  sizes := ⟨.inl rfl, .inl rfl, Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_nBits, by decide +kernel⟩
  n_lt := by decide +kernel
  sh := 0
  sh_eq := Proof.Ecdsa.AArch64.BrainpoolP256r1.brainpoolp256r1_sh
  coreN := Spec.Ecdsa.BrainpoolP256r1.signApi.name
  coreC := Impl.Ecdsa.AArch64.signBrainpoolP256r1
  coreX := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.sign_a64 hL hI
  coreCT := by rw [coreK_brainpoolp256r1]; exact Proof.Ecdsa.AArch64.BrainpoolP256r1.sign_ct
  coreNoFrames := by lit_decide
  coreKeepsV := by lit_decide
  reduceT := by exact (Function.const _ ⟨_, by taint_decide⟩)
  reduceKeepsV := Function.const _ (by decide +kernel)

end VG.Proof.Ecdsa.Rfc6979.AArch64
