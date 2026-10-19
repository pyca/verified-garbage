module

import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceReadCT
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceStepCT
public import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceByte
public import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
meta import VerifiedGarbage.Proof.Dsa.X86_64.PowerCT
import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtArith
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTGPow
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceRead
import VerifiedGarbage.Proof.Bignum.CrtMath
import VerifiedGarbage.Proof.Bignum.LazyMath
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
import VerifiedGarbage.Proof.Bignum.X86_64.Copy
import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
import VerifiedGarbage.Proof.Bignum.X86_64.Csub
import VerifiedGarbage.Proof.Bignum.X86_64.Double
import VerifiedGarbage.Proof.Bignum.X86_64.Loop
import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
import VerifiedGarbage.Proof.Bignum.X86_64.Row
import VerifiedGarbage.Proof.Bignum.X86_64.Setup
import VerifiedGarbage.Proof.Bignum.X86_64.Store
import VerifiedGarbage.Proof.Bignum.X86_64.Valid
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
import VerifiedGarbage.Proof.Dsa.X86_64.Load
import VerifiedGarbage.Proof.Dsa.X86_64.Power
import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Poly1305.Limbs64
meta import VerifiedGarbage.Proof.Bignum.CrtMath
meta import VerifiedGarbage.Proof.Bignum.LazyMath
meta import VerifiedGarbage.Proof.Bignum.Math
meta import VerifiedGarbage.Proof.Bignum.Octets
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxBlock
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxFused
meta import VerifiedGarbage.Proof.Bignum.X86_64.AdxRow
meta import VerifiedGarbage.Proof.Bignum.X86_64.Bytes
meta import VerifiedGarbage.Proof.Bignum.X86_64.CTMain
meta import VerifiedGarbage.Proof.Bignum.X86_64.Copy
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtCTExp
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChecks
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtChk
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtFix
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtPow
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtQ
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtRows
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtSetup
meta import VerifiedGarbage.Proof.Bignum.X86_64.CrtWs
meta import VerifiedGarbage.Proof.Bignum.X86_64.Csub
meta import VerifiedGarbage.Proof.Bignum.X86_64.Double
meta import VerifiedGarbage.Proof.Bignum.X86_64.Loop
meta import VerifiedGarbage.Proof.Bignum.X86_64.MulAdd
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubEntry
meta import VerifiedGarbage.Proof.Bignum.X86_64.PubFail
meta import VerifiedGarbage.Proof.Bignum.X86_64.Reduce
meta import VerifiedGarbage.Proof.Bignum.X86_64.Rounds
meta import VerifiedGarbage.Proof.Bignum.X86_64.Row
meta import VerifiedGarbage.Proof.Bignum.X86_64.Setup
meta import VerifiedGarbage.Proof.Bignum.X86_64.Store
meta import VerifiedGarbage.Proof.Bignum.X86_64.Valid
meta import VerifiedGarbage.Proof.Dsa.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.Arithmetic
meta import VerifiedGarbage.Proof.Dsa.X86_64.EncodePower
meta import VerifiedGarbage.Proof.Dsa.X86_64.Exponent
meta import VerifiedGarbage.Proof.Dsa.X86_64.Load
meta import VerifiedGarbage.Proof.Dsa.X86_64.Power
meta import VerifiedGarbage.Proof.Dsa.X86_64.Prepare
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceCount
meta import VerifiedGarbage.Proof.Dsa.X86_64.ReduceSetup
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.X86_64.Avx
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
meta import VerifiedGarbage.Proof.Framework.X86_64.RelCT
meta import VerifiedGarbage.Proof.Framework.X86_64.Sse
meta import VerifiedGarbage.Proof.Poly1305.Limbs64

/-! # Constant time of one complete streaming reduction byte -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.X86_64
open VG.Proof.Bignum VG.Proof.Bignum.X86_64 VG.Proof.MlKem.X86_64

structure ReducePublic extends PowerPublic where
  greater255 : 255 < modulus
  lengthBound : bytes.len < 2 ^ 64

/-- Source bytes and the accumulator are secret; only their address and
length appear in the public descriptor. -/
def ReduceBytePre (p : ReducePublic) (s : State) : Prop :=
  ∃ (bs : List Byte) (acc : Nat), bs.length = p.bytes.len ∧ 0 < bs.length ∧
    ReduceState s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx
      p.modulus p.minv p.bytes.ptr bs acc

def ReduceArithmeticPre (p : ReducePublic) (s : State) : Prop :=
  SubCtx s p.bytes.x.B p.bytes.x.Z p.bytes.x.o p.bytes.x.w p.bytes.x.wx p.minv ∧
  ModCtx s (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx 8) p.bytes.x.wx p.minv p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aY) p.bytes.x.wx < p.modulus ∧
  wv s.mem (off p.bytes.x.B p.bytes.x.o) (slot p.bytes.x.wx aX) p.bytes.x.wx < p.modulus

theorem reduceRead_arithmetic {p : ReducePublic} {s : State} (h : ReduceBytePre p s) :
    WP isa (.block Arithmetic.reduceRead) s (ReduceArithmeticPre p) := by
  obtain ⟨bs, acc, hlen, hpos, h⟩ := h
  have hr := h.source.rd 0 hpos
  simp only [BitVec.add_zero] at hr
  refine WP.mono (reduceRead_context h.ctx h.modulus (by have := p.lower; omega)
    h.pointer hr h.high) fun t ⟨hc, hm, hbyte, harr, _⟩ => ?_
  refine ⟨hc, hm, ?_, ?_⟩
  · rw [harr aY (by decide) (by decide), h.value]
    exact h.reduced
  · rw [hbyte]
    have := (s.mem p.bytes.ptr).isLt
    have := p.greater255
    omega

theorem reduceArithmetic_ct (M : Mont) : RelCT isa (Two ReduceArithmeticPre)
    (Arithmetic.reduceStep M.mm) (fun _ _ => True) :=
  two_map (fun p : ReducePublic => p.toPowerPublic.product) (fun _ _ h =>
    ⟨h.2.1, fun j hj => by obtain rfl := List.mem_singleton.mp hj; exact h.2.2.1⟩) (reduceStep_ct M)

/-- Only the header address is needed for the counter block's trace.
The loop proof separately establishes that the resulting flag is public. -/
theorem reduceByte_ct (M : Mont) : RelCT isa (Two ReduceBytePre)
    (Arithmetic.reduceByte M.mm) (fun _ _ => True) := by
  unfold Arithmetic.reduceByte seqs
  refine RelCT.seq (two_post (Ψ := ReduceArithmeticPre)
    (two_map (fun p : ReducePublic =>
      (⟨p.toPowerPublic.product.layout, p.bytes.ptr⟩ : ReduceReadPublic)) ?_ reduceRead_ct)
    (fun _ _ h => reduceRead_arithmetic h)) ?_
  · intro p s ⟨bs, acc, hlen, hpos, h⟩
    refine ⟨⟨h.ctx.good, Nat.le_refl _⟩, h.pointer, ?_⟩
    simpa using h.source.rd 0 hpos
  refine RelCT.seq (two_post (Ψ := fun p s => s.gpr .rdi = off p.bytes.x.B p.bytes.x.o)
    (reduceArithmetic_ct M) ?_) ?_
  · intro p s ⟨hc, hm, hred, hb⟩
    unfold Arithmetic.reduceStep
    refine WP.seq (WP.mono (mont_step M hm (Nat.le_refl _) p.lower
      (by have := p.fits; have := p.upper; omega) (by unfold MmUse; decide) hred)
      fun u ⟨hmu, hlt, _, hf, _⟩ => ?_)
    have hxu := (hf.wv_of_not_mem (show aX < 8 by decide) (by decide) hc.good.scr.nowrap)
    refine WP.mono (addMod_ok hmu.good.scr hmu.good.rdi hmu.good.hdr (Nat.le_refl _)
      p.lower (by have := p.fits; have := p.upper; omega)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hmu.modulus]; exact hlt)
      (by rw [hmu.modulus, hxu]; exact hb)) fun t ⟨_, _, hk⟩ =>
        (hk.gpr (by decide)).trans hmu.good.rdi
  exact two_taint [.rdi] (pins_rdiB (fun p => off p.bytes.x.B p.bytes.x.o) (fun _ _ h => h))
    (by taint_decide)

end VG.Proof.Dsa.X86_64
