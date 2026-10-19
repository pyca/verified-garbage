module

import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Verified
public import VerifiedGarbage.Proof.Framework.Lit
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.RejNttCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.BallCT
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.Unpack
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintUnpack
public import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Backend
public import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Encode
public import VerifiedGarbage.Impl.MlDsa.X86_64.Verify.Verify
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.PrimsOk
public import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Top
public import VerifiedGarbage.Impl.MlDsa.X86_64.Sample.Ball
public import VerifiedGarbage.Impl.MlDsa.X86_64.Pack.Hint
import Mathlib.Tactic.Conv
import VerifiedGarbage.Proof.MlKem.X86_64.ArithOk
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bitslice.Lanes
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.RelCT
import VerifiedGarbage.Proof.Framework.X86_64.Sse
import VerifiedGarbage.Proof.Framework.X86_64.Words
import VerifiedGarbage.Proof.MlDsa.KeyGen.Mono
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlDsa.Verify.Bounds
import VerifiedGarbage.Proof.MlDsa.Verify.Mem
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.AddSub
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Mul
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Ntt
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.NttInv
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.Same
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VLay21
import VerifiedGarbage.Proof.MlDsa.X86_64.Arith.VMem
import VerifiedGarbage.Proof.MlDsa.X86_64.Pack.HintPack
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.MakeHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.NormLt
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.OneOut
import VerifiedGarbage.Proof.MlDsa.X86_64.Round.UseHint
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.M4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Pro
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4CT
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Scalar
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Sq
import VerifiedGarbage.Proof.MlDsa.X86_64.Sample.Rej4Verified
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTCompute
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTSample
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.CTStages
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Control
import VerifiedGarbage.Proof.MlDsa.X86_64.Verify.Correct
import VerifiedGarbage.Proof.MlKem.PolyW
import VerifiedGarbage.Proof.MlKem.X86_64.Cbd16Avx2
import VerifiedGarbage.Proof.MlKem.X86_64.CompressEncode
import VerifiedGarbage.Proof.MlKem.X86_64.DecMulV
import VerifiedGarbage.Proof.MlKem.X86_64.DecodeDecompress
import VerifiedGarbage.Proof.MlKem.X86_64.EncMulV
import VerifiedGarbage.Proof.MlKem.X86_64.FragPrim
import VerifiedGarbage.Proof.MlKem.X86_64.KgMulV
import VerifiedGarbage.Proof.MlKem.X86_64.NttInv
import VerifiedGarbage.Proof.MlKem.X86_64.S4Tab
import VerifiedGarbage.Proof.MlKem.X86_64.S4Top
import VerifiedGarbage.Proof.MlKem.X86_64.VLay42
import VerifiedGarbage.Proof.MlKem.X86_64.VPack
import VerifiedGarbage.Proof.MlKem.X86_64.WritesOnly
import VerifiedGarbage.Proof.MlKem.X86_64.YNtt
import VerifiedGarbage.Proof.MlKem.X86_64.Zero
import VerifiedGarbage.Proof.Sha3.X86_64.Stream.Pad
import VerifiedGarbage.Proof.Sha3.X86_64.X4R.Loop

/-!
# ML-DSA verification on x86-64: the primitives it calls

The x86-64 implementations of the primitives (`prims`) meet their contracts
with at most 16 bytes of stack, never write the stack pointer or load MXCSR,
and call at most two deep, with any implementation `v` of the polynomial
arithmetic (`prims_okWith`), so `verify (primsWith v.code) p` meets
`verifyContract p`.
-/

@[expose] public section

namespace VG.Proof.MlDsa.X86_64.Verify

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Verify
open VG.Impl.MlDsa.X86_64
open VG.Proof.MlDsa.X86_64 (FnOk ArithImpl)

/-- The x86-64 implementations of the primitives. -/
def prims : Prims where
  ntt := Arith.ntt
  invNtt := Arith.nttInv
  mul := Arith.mul
  mulAdd := Arith.mulAdd
  sub := Arith.sub
  rejNtt := Sample.rejNTT
  ball := Sample.sampleInBall
  useHint := Round.useHint
  simpleBitPack := Pack.simpleBitPack
  bitUnpack := Pack.bitUnpack
  unpackT1 := Pack.unpackT1
  hintUnpack := Pack.hintBitUnpack
  normLt := Round.normLt
  rej4 := Sample.Rej4.rejNTT4

/-- The primitives, with the polynomial arithmetic of `B`. -/
def primsWith (B : Arith.Backend) : Prims :=
  { prims with
    ntt := B.ntt
    invNtt := B.invNtt
    mul := B.mul
    mulAdd := B.mulAdd
    sub := B.sub
    normLt := B.normLt
    useHint := B.useHint
    rej4 := B.rej4
    sfx := B.sfx
    montgomery := B.montgomery }

/-- A function of the polynomial arithmetic satisfies what the proofs of verification need of it. -/
theorem calleeOf {sig : Sig} {pre : Curry (sig.words X86_64.abi.ptrBits) (Mem → Prop)}
    {post : sig.Post X86_64.abi.ptrBits} {wa : Bool} {c : Prog isa}
    (h : FnOk (fun S => sig.contract X86_64.abi pre post wa S none) c) :
    CalleeOk c (sig.contract X86_64.abi pre post wa 16 none) :=
  CalleeOk.of_verified h.ver (by decide) h.nosp (Nat.le_succ_of_le h.depth) h.ctl h.sp

theorem prims_okWith (v : ArithImpl) : PrimsOk (primsWith v.code) where
  ntt := by
    have h := v.ok.ntt
    unfold Spec.MlDsa.nttContract Spec.MlDsa.inPlaceContract at h ⊢
    exact calleeOf h
  invNtt := by
    have h := v.ok.invNtt
    unfold Proof.MlDsa.Arith.Representation.inverseContract Spec.MlDsa.inPlaceContract at h ⊢
    exact calleeOf h
  mul := calleeOf v.ok.mul
  mulAdd := calleeOf v.ok.mulAdd
  sub := calleeOf v.ok.sub
  rejNtt := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.rejNTT_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.rejNtt _)
  ball := (CalleeOk.of_verified Proof.MlDsa.X86_64.Sample.sampleInBall_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.ball _)
  useHint := calleeOf v.ok.useHint
  simpleBitPack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.simpleBitPack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.simpleBitPack _)
  bitUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.bitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.bitUnpack _)
  unpackT1 := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.unpackT1_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.unpackT1 _)
  hintUnpack := (CalleeOk.of_verified Proof.MlDsa.X86_64.Pack.hintBitUnpack_verified (by decide)
    (Proof.MlKem.X86_64.nosp_of (by lit_decide)) (by lit_decide) (by lit_decide)
    (Code.all_of_allInstrs (by lit_decide)) :
    CalleeOk prims.hintUnpack _)
  normLt := calleeOf v.ok.normLt
  rej4 := ⟨v.ok.rej4.ver.1, v.ok.rej4.ver.2.1, v.ok.rej4.nosp, v.ok.rej4.depth, v.ok.rej4.ctl, v.ok.rej4.sp⟩

/-- `vg_mldsa*_verify` for the parameter set `p`, calling the x86-64
primitives, with the polynomial arithmetic of `v`. -/
theorem verify_prims (v : ArithImpl) {p : Spec.MlDsa.Params} (hp : p ∈ params) :
    Verified X86_64.target (verify (primsWith v.code) p) (Spec.MlDsa.verifyContract p X86_64.abi 32) :=
  verify_verified (prims_okWith v) hp

end VG.Proof.MlDsa.X86_64.Verify
