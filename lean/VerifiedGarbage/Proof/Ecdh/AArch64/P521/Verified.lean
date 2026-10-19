module

import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneCaller

public import VerifiedGarbage.Proof.Ecdh.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Main
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Contract
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Contract
public import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Lit
meta import VerifiedGarbage.Proof.Ecdh.AArch64.P521.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.P521.Verified
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
meta import Mathlib.Data.Finset.Card
meta import Mathlib.Data.Nat.Find
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdh.Exchange
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Call
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Spec.Ecdh.P521
import VerifiedGarbage.Spec.Weierstrass.Mul
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
meta import VerifiedGarbage.Proof.Ecdh.Exchange
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.Sign
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Spec.Ecdh.P521
meta import VerifiedGarbage.Spec.Weierstrass.Mul

/-!
# ECDH over P-521 on AArch64: `Verified`

P-521 is a curve the proof supports (`p521_ok`, given the inversions' soundness `InvSounds`, and `Law` for its group
law, which the registration file supplies: `Proof.P521.law` and `invSound_of_toM`), so `exchange_ok`
gives the contract's postcondition; `x19`–`x25` are restored, and no
instruction writes the other callee-saved registers, `sp` or a SIMD register
(`abiPreserved_of`). Constant time by taint tracking: the only branches are on
loop counters, and every address is an argument plus a constant or a counter,
so not even the peer's key (which the contract would let leak) affects timing.
-/

@[expose] public section

namespace VG.Proof.Ecdh.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdh.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P521

theorem pre_of {s : State} (h : ecdhAArch64.pre s) : EPre p521 s := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3, h6, h7, h8, h9⟩

theorem post_of {s s' : State} (h : EPost p521 s s') : ecdhAArch64.post s s' := by
  unfold EPost at h
  show match ex s.mem (s.gpr .x1) (s.gpr .x2) with
    | some z => (s'.gpr .x0).setWidth 32 = 1 ∧ Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 66 = z
    | none => (s'.gpr .x0).setWidth 32 = 0 ∧
        Spec.EcKey.bytesAt s'.mem (s.gpr .x0) 66 = List.replicate 66 0
  revert h
  generalize hq : ex s.mem (s.gpr .x1) (s.gpr .x2) = q
  rw [show Spec.Ecdh.exchange p521.C (dk p521 s)
      (Spec.Ecdsa.bytesAt s.mem (s.gpr .x2) (1 + 2 * p521.C.len)) = ex s.mem (s.gpr .x1) (s.gpr .x2) from rfl, hq]
  rcases q with _ | z <;> exact id

theorem ecdh_a64 (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds) (s : State) (hs : ecdhAArch64.pre s) :
    ∃ t s', Exec isa exchangeP521 s t s' ∧ abiPreserved s s' ∧ ecdhAArch64.post s s' := by
  -- In steps: elaborated in one term, the unifier would compare P-521's
  -- terms before the literals' facts are known.
  have hn : CallsKeep exchangeP521 := by lit_decide
  have hu : KeepsUntouched exchangeP521 := by lit_decide
  have hv : exchangeP521.allInstrs keepsV = true := by lit_decide
  obtain ⟨t, s', he, hsv, hpost⟩ := exchange_ok (p521_ok hI) hL (pre_of hs)
  exact ⟨t, s', he, abiPreserved_of he hn hu hv hsv, post_of hpost⟩

theorem ecdh_ct : ConstantTime isa ecdhAArch64.pre ecdhAArch64.pub exchangeP521 :=
  LaneTaint.constantTime (Taint.ofRegs [.x0, .x1, .x2, .x3])
    (fun _ _ _ _ ⟨h0, h1, h2, h3, hsp⟩ => ⟨hsp, fun r hr => by
      simp only [Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact h0
      · exact h1
      · exact h2
      · exact h3⟩) (by taint_decide)

theorem ecdh_verified (hL : Weierstrass.Law Spec.P521.curve) (hI : Weierstrass.AArch64.InvSounds) :
    Verified AArch64.target exchangeP521
      (Spec.Ecdh.Instance.exchangeContract Spec.EcKey.P521.inst AArch64.abi) :=
  Verified.of_correct (ecdh_a64 hL hI) ecdh_ct implies

end VG.Proof.Ecdh.AArch64.P521
