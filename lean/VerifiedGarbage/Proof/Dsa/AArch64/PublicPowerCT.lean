module
public import VerifiedGarbage.Proof.Dsa.AArch64.PowerCT
public import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower

import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponentCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponentCT
import VerifiedGarbage.Proof.Dsa.AArch64.PublicPower
meta import VerifiedGarbage.Impl.Dsa.AArch64.PublicPower
import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.AArch64.EncodePower
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
import VerifiedGarbage.Proof.Bignum.AArch64.Copy
import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
import VerifiedGarbage.Proof.Bignum.AArch64.Csub
import VerifiedGarbage.Proof.Bignum.AArch64.Double
import VerifiedGarbage.Proof.Bignum.AArch64.Mont
import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
import VerifiedGarbage.Proof.Bignum.AArch64.Row
import VerifiedGarbage.Proof.Bignum.AArch64.Setup
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import VerifiedGarbage.Proof.Bignum.AArch64.Store
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
import VerifiedGarbage.Proof.Dsa.AArch64.Load
import VerifiedGarbage.Proof.Dsa.AArch64.Power
import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
import VerifiedGarbage.Proof.Dsa.AArch64.Setup
import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.TaintBatch
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcAdd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcColumns
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtRow
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcCtSpill
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcEnd
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcExtend
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcLoop
meta import VerifiedGarbage.Proof.Bignum.AArch64.BlockedRedcSquare
meta import VerifiedGarbage.Proof.Bignum.AArch64.Bytes
meta import VerifiedGarbage.Proof.Bignum.AArch64.Copy
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtCTSetupLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtP
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtSel
meta import VerifiedGarbage.Proof.Bignum.AArch64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.AArch64.Csub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Double
meta import VerifiedGarbage.Proof.Bignum.AArch64.Mont
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcMain
meta import VerifiedGarbage.Proof.Bignum.AArch64.PcVerified
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdExp
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdLoad
meta import VerifiedGarbage.Proof.Bignum.AArch64.PdRest
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCorrect
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightCtRows
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightMath
meta import VerifiedGarbage.Proof.Bignum.AArch64.ProductEightRaw
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubOut
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubR2
meta import VerifiedGarbage.Proof.Bignum.AArch64.PubValid
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dQuot
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dRecip
meta import VerifiedGarbage.Proof.Bignum.AArch64.R2dSub
meta import VerifiedGarbage.Proof.Bignum.AArch64.Reduce
meta import VerifiedGarbage.Proof.Bignum.AArch64.Rounds
meta import VerifiedGarbage.Proof.Bignum.AArch64.Row
meta import VerifiedGarbage.Proof.Bignum.AArch64.Setup
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCall
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareCallMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightGuardCT
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareEightMont
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareGuard
meta import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
meta import VerifiedGarbage.Proof.Bignum.AArch64.Store
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Dsa.AArch64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.AArch64.Load
meta import VerifiedGarbage.Proof.Dsa.AArch64.Power
meta import VerifiedGarbage.Proof.Dsa.AArch64.PowerCallCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Prepare
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicExponent
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicSelect
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindow
meta import VerifiedGarbage.Proof.Dsa.AArch64.PublicWindowCT
meta import VerifiedGarbage.Proof.Dsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Dsa.AArch64.SetupCT
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.LaneSave
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Timing of public exponentiation with secret bases -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.PublicPower
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Proof.Bignum VG.Proof.Bignum.AArch64 VG.Proof.MlKem.AArch64
open VG.Impl.Dsa.AArch64.PublicPower

def EncodedPre (p : PowerPublic × List Byte) (s : State) : Prop :=
  ∃ x : Nat, PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx Crt.aXc) p.1.bytes.x.wx =
      x * 2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aY) p.1.bytes.x.wx =
      2 ^ (64 * p.1.bytes.x.wx) % p.1.modulus

/-- Exponentiation and decoding together have a secret-independent trace. -/
theorem encodedPower_ct (M : Mont) : RelCT isa (Two EncodedPre)
    (VG.Impl.Dsa.AArch64.PublicPower.encodedPower M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.encodedPower
  refine RelCT.seq (two_post (Ψ := fun p s => GoodW p.1.bytes.x.ws s)
    (two_map (fun p : PowerPublic × List Byte => (p.1.bytes, p.2)) ?_ (pubExpLoop_ct M (by taint_decide))) ?_)
    (two_map (fun p : PowerPublic × List Byte => p.1.bytes.x.ws) (fun _ _ h => h)
      (M.ct (by unfold MmUse; decide)))
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, hlen, h1, h2, hs⟩, hx, hy⟩
    refine ⟨p.1.minv, p.1.modulus, x, 1, hc, p.1.lower, p.1.fits, p.1.upper,
      hm.modulus, hm.inverse, p.1.odd, ?_, ?_, ?_, ?_, by decide, by decide,
      hp, hl, hlen, h1, h2, hs⟩
    · rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · rw [hx, Nat.mod_mod]
    · rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · rw [hy, Nat.mod_mod, Nat.one_mul]
  · intro p s ⟨x, ⟨hc, hm, _, hp, hl, _, h1, h2, hs⟩, hx, hy⟩
    refine WP.mono (expLoop_ok M (x := x) hc p.1.lower p.1.fits p.1.upper hm.modulus hm.inverse p.1.odd
      (by rw [hx]; exact Nat.mod_lt _ (by have := p.1.greater; omega))
      (by rw [hx, Nat.mod_mod])
      (by rw [hy]; exact Nat.mod_lt _ (by have := p.1.greater; omega))
      (by rw [hy, Nat.mod_mod]) (by decide) (by decide) hp hl h1 h2 hs)
      fun t ⟨ht, _⟩ => ⟨p.1.minv, ht.good, Nat.le_refl _⟩

/-- Prepared ordinary bases for the complete encode/exponentiate/decode core. -/
def PowerCorePre (p : PowerPublic × List Byte) (s : State) : Prop :=
  PowerInputs p.1 p.2 s ∧
    wv s.mem (off p.1.bytes.x.B p.1.bytes.x.o) (slot p.1.bytes.x.wx aR2) p.1.bytes.x.wx =
      2 ^ (128 * p.1.bytes.x.wx) % p.1.modulus

/-- The whole power core is constant time for secret bases and fixed public exponents. -/
theorem powerCore_ct (M : Mont) : RelCT isa (Two PowerCorePre)
    (VG.Impl.Dsa.AArch64.PublicPower.powerCore M.mm VG.Impl.Dsa.Layout.arg2 VG.Impl.Dsa.Layout.arg2Len)
    (fun _ _ => True) := by
  unfold VG.Impl.Dsa.AArch64.PublicPower.powerCore
  refine RelCT.seq (two_post (Ψ := EncodedPre)
    (two_map (fun p : PowerPublic × List Byte => p.1.product) ?_ (encodePower_ct M)) ?_)
    (encodedPower_ct M)
  · intro p s ⟨⟨_, hm, hone, _⟩, hr2⟩
    refine ⟨hm, ?_⟩
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · dsimp only [PowerPublic.product]
      rw [hr2]; exact Nat.mod_lt _ (by have := p.1.greater; omega)
    · dsimp only [PowerPublic.product]
      rw [hone]; exact p.1.greater
  · intro p s ⟨⟨hc, hm, hone, hp, hl, hlen, h1, h2, hs⟩, hr2⟩
    rw [show 128 * p.1.bytes.x.wx = 64 * p.1.bytes.x.wx + 64 * p.1.bytes.x.wx by omega, Nat.pow_add] at hr2
    refine WP.mono (encodePower_ok M hm (Nat.le_refl _) p.1.lower
      (by have := p.1.fits; have := p.1.upper; omega) p.1.greater p.1.odd rfl hr2 hone)
      fun t ⟨hmt, hx, hy, htone, hf, hk⟩ => ?_
    have hct := arrays_context hc hf (by decide) hk
    have hfw := arrays_work hf (by decide)
    exact ⟨_, ⟨hct, hmt, htone, (work_parent hc hfw (by decide)).trans hp,
      (work_parent hc hfw (by decide)).trans hl, hlen, h1, h2, work_source hc hfw hk hs⟩, hx, hy⟩


end VG.Proof.Dsa.AArch64.PublicPower
