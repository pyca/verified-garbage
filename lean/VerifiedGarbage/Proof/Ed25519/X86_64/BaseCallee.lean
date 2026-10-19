module
public import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombLit
public import VerifiedGarbage.Proof.Framework.X86_64.Call
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic.NormNum.Prime
public import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseMain
public import VerifiedGarbage.Proof.Framework.TaintSum
public import VerifiedGarbage.Proof.Framework.X86_64.CallInlineSig
public import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Spec

import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.ScalarBase
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBaseAdx
import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
import VerifiedGarbage.Proof.Ed25519.X86_64.CTSupport
import VerifiedGarbage.Impl.Ed25519.X86_64.BaseOdd
import VerifiedGarbage.Impl.Poly1305.X86_64.Avx2
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.Group.Decode
import VerifiedGarbage.Proof.Ed25519.Recode
import VerifiedGarbage.Proof.Ed25519.Scalar
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.CombLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.CombNeg
import VerifiedGarbage.Proof.Ed25519.X86_64.CombSelectY
import VerifiedGarbage.Proof.Ed25519.X86_64.DecodeBits
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldLazy
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Ifma.CombSelect
import VerifiedGarbage.Proof.Ed25519.X86_64.MulAddMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Ops
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAffine
import VerifiedGarbage.Proof.Ed25519.X86_64.PointEncode
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMul
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCTBatch
import VerifiedGarbage.Proof.Ed25519.X86_64.PointMulCounter
import VerifiedGarbage.Proof.Ed25519.X86_64.PointPowersLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.WindowEntry
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Half
import VerifiedGarbage.Proof.Ed25519.X86_64.Zmm.Keep
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Avx512
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.X86_64.VecKeep
import VerifiedGarbage.Proof.Mont.Read
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Bits
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.ARow
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Main
import VerifiedGarbage.Proof.X25519.X86_64.Divstep.Step
import VerifiedGarbage.Proof.X25519.X86_64.Finish
import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Block
import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Bound
import VerifiedGarbage.Proof.X25519.X86_64.Inv
import VerifiedGarbage.Proof.X25519.X86_64.Invert
import VerifiedGarbage.Proof.X25519.X86_64.Iter
import VerifiedGarbage.Proof.X25519.X86_64.Sqr
import VerifiedGarbage.Spec.EcKey.Generic
import VerifiedGarbage.Spec.Ecdsa.Generic

/-!
# The base-point multiplications the Ed25519 functions call

`EdBase bs`: `bs` is a body of `vg_ed25519_scalar_base`, correct and constant
time for its contract (for states whose buffers are apart from the 8 bytes below
`rsp`, where its call of `vg_gf25519_r64_invert` stores its return address),
and its every instruction keeps `rsp` (the calls need both) in one level of
calls: those of `scalarBase_precomputed` (each field
multiplication), `scalarBase_adx` and `scalarBase_ifma`. Public-key derivation and signing are
proven once for any of them.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

/-- The 8 bytes below `rsp = B + 8`, where a call from it stores its return address. -/
theorem hole_add8 (B : Addr) : hole (B + BitVec.ofNat 64 8) = ⟨B, 8⟩ := by
  simp only [hole]
  rw [show (8 : Addr) = BitVec.ofNat 64 8 from rfl, BitVec.add_sub_cancel]

class EdBase (bs : Prog isa) : Prop where
  ok : ∀ s, scalarBaseLocal.clear.pre s →
    ∃ t s', Exec isa bs s t s' ∧ abiPreserved s s' ∧ scalarBaseLocal.post s s'
  ct : ConstantTime isa scalarBaseLocal.clear.pre scalarBaseLocal.pub bs
  instrs : bs.allInstrs (fun i => !VG.X86_64.Taint.clobbers i .rsp && !isa.writesSp i) = true
  depth : bs.depth ≤ 1

instance {fld : Arith} [EdArith fld] [X25519.X86_64.DivstepInv] : EdBase (scalarBase_precomputed fld) :=
  ⟨scalarBase_precomputed_ok, scalarBase_precomputed_ctC, by fld_lit_decide, by fld_lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_adx :=
  ⟨scalarBase_adx_ok, scalarBase_adx_ct, by lit_decide, by lit_decide⟩

instance [X25519.X86_64.DivstepInv] : EdBase scalarBase_ifma :=
  ⟨Ifma.scalarBase_ifma_ok, Ifma.scalarBase_ifma_ct, by lit_decide, by lit_decide⟩

end VG.Proof.Ed25519.X86_64
