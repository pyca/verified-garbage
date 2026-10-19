module

public import VerifiedGarbage.Impl.Ecdsa.BrainpoolP512r1.AArch64
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontBrainpoolP512r1
import VerifiedGarbage.Proof.BrainpoolP512r1.Point
import VerifiedGarbage.Proof.BrainpoolP512r1.Prime
import VerifiedGarbage.Proof.Weierstrass.AArch64.BrainpoolP512r1Literals
import VerifiedGarbage.Impl.Ecdh.BrainpoolP512r1.AArch64
import VerifiedGarbage.Proof.Ecdsa.AArch64.Flags
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.Blocks
import VerifiedGarbage.Proof.Mont.AArch64.Chain
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Core
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Product
import VerifiedGarbage.Proof.Mont.AArch64.P256Square.Words
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
import VerifiedGarbage.Proof.Mont.AArch64.RowInit
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Comb
import VerifiedGarbage.Proof.Weierstrass.AArch64.CombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Loop
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontVerified
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Unch
import VerifiedGarbage.Proof.Weierstrass.AArch64.Zero
import VerifiedGarbage.Proof.Weierstrass.Pow

/-! # brainpoolP512r1 parameters for the AArch64 arithmetic -/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64.BrainpoolP512r1

open VG VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass.AArch64
open VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64

theorem brainpoolp512r1_nBits : Spec.Ecdsa.nBits brainpoolp512r1.C = 512 := by
  show Spec.BrainpoolP512r1.curve.n.log2 + 1 = 512
  have h1 : 511 ≤ Spec.BrainpoolP512r1.curve.n.log2 :=
    (Nat.le_log2 (by decide +kernel)).mpr (by decide +kernel)
  have h2 : Spec.BrainpoolP512r1.curve.n.log2 < 512 :=
    (Nat.log2_lt (by decide +kernel)).mpr (by decide +kernel)
  omega

/-- No bit of a hash of `64` bytes is dropped. -/
theorem brainpoolp512r1_sh : brainpoolp512r1.sh = 0 := by
  have := brainpoolp512r1_nBits; have : brainpoolp512r1.C.len = 64 := rfl; unfold Cfg.sh; omega

theorem brainpoolp512r1_ok (hI : Weierstrass.AArch64.InvSounds) : BaseCfgOk brainpoolp512r1 where
  n0 := by decide
  n10 := by decide
  onG := Proof.BrainpoolP512r1.onCurve_G
  p_odd := by decide +kernel
  n_odd := by decide +kernel
  p_lt := by decide +kernel
  n_lt := by decide +kernel
  p_ge := by decide +kernel
  n_ge := by decide +kernel
  p_lt_2n := by decide +kernel
  minv_p := by decide +kernel
  minv_n := by decide +kernel
  red_p := by decide +kernel
  red_n := by decide +kernel
  n2 := by decide
  len8 := by decide
  len_lo := by decide
  len_hi := by decide
  sh := by rw [brainpoolp512r1_sh]; decide
  n4 := by decide
  sound_p := hI Proof.BrainpoolP512r1.p_prime
  inv_p := InvOk.ofMod (by decide +kernel) (by decide)
  inv_n := fun _ => ⟨hI Proof.BrainpoolP512r1.n_prime, InvOk.ofMod (by decide +kernel) (by decide)⟩
  chain_n := fun h => absurd h (by decide)
  call_p := by
    intro f m h
    have e : Mont.callOf brainpoolp512r1.MP' = some
        (Spec.Weierstrass.Mont.brainpoolp512r1p.fn "mul", Spec.BrainpoolP512r1.p) := by decide +kernel
    rw [e] at h
    cases h
    exact ⟨rfl, Mont.brainpoolp512r1p_ok⟩
  call_n := by
    intro f m h
    have e : Mont.callOf brainpoolp512r1.MN' = some
        (Spec.Weierstrass.Mont.brainpoolp512r1n.fn "mul", Spec.BrainpoolP512r1.n) := by decide +kernel
    rw [e] at h
    cases h
    exact ⟨rfl, Mont.brainpoolp512r1n_ok⟩
  inv_at := .inr (by decide +kernel)
  inv_fn := fun _ => ⟨by decide, by lit_decide, by lit_decide, by lit_decide, by lit_decide⟩
  padd := fun h => absurd rfl h
  check_fn := fun _ => ⟨by lit_decide, by lit_decide, by lit_decide⟩

end VG.Proof.Ecdsa.AArch64.BrainpoolP512r1
