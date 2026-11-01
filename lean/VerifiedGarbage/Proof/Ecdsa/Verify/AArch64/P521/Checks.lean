module

import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintMono
import VerifiedGarbage.Proof.Framework.TaintSum
meta import VerifiedGarbage.Proof.Framework.TaintSum

import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller

public import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.P521Literals
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedTiming
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P521.AArch64
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.ReductionArithmetic
import VerifiedGarbage.Proof.Mont.AArch64.P521Square.Rotate
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.MulContract
meta import VerifiedGarbage.Impl.Ecdh.P521.AArch64
meta import VerifiedGarbage.Proof.EcKey.PublicKey
meta import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
meta import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
meta import VerifiedGarbage.Proof.Ecdsa.Projective
meta import VerifiedGarbage.Proof.Ecdsa.Verify
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P521.PackedMul
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
meta import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.RelCT
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd
meta import VerifiedGarbage.Proof.Framework.AArch64.Simd64
meta import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.BitByte
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafCore
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
meta import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
meta import VerifiedGarbage.Proof.Weierstrass.CoZTable
meta import VerifiedGarbage.Proof.Weierstrass.WinJacMath
meta import VerifiedGarbage.Proof.Weierstrass.MulContract
public import VerifiedGarbage.Impl.Ecdsa.P521.AArch64
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64.PackedNaf

/-!
# ECDSA verification over P-521 on AArch64: what taint tracking checks

Each piece of the verifier whose timing the relational proof
(`packedNafVerify_public_ct`) takes from taint tracking, with the registers it
may branch on or address by: the pointer `x0` for the field arithmetic, and
the loop counters, the digits' and entries' registers and the recoding's
residual elsewhere.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P521

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64

/- The constant-time analyses of the field functions, and of the parts of the
verifier's prefix that `before_checks` and the joint verifier's `before_ct`
share, are done once here (`taint_summary`, `Proof/Framework/TaintSum.lean`),
rather than in every check that calls them. The functions start from the
pointer `x0` and the offsets `x1`–`x3` public, and keep public `x0` and the
counters `x19` and `x20` that they do not write. -/

taint_summary mulPSum : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "mul")
    (Impl.Weierstrass.AArch64.Mont.mulFn 9 Impl.Weierstrass.Mont.p521p.m))
  keeping (VectorTaint.ofRegs [.x0, .x19, .x20])
taint_summary mulNSum : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
  (.call (Impl.Weierstrass.Mont.p521n.fn "mul")
    (Impl.Weierstrass.AArch64.Mont.mulFn 9 Impl.Weierstrass.Mont.p521n.m))
  keeping (VectorTaint.ofRegs [.x0, .x19, .x20])
taint_summary sqrPSum : VectorTaint.taint (VectorTaint.ofRegs [.x0, .x1, .x2, .x3])
  (.call (Impl.Weierstrass.Mont.p521p.fn "sqr") Impl.Weierstrass.AArch64.Mont.sqrFn521)
  keeping (VectorTaint.ofRegs [.x0])

taint_summary validateSum : VectorTaint.taint (VectorTaint.ofRegs [.x0])
  (Impl.Ecdh.AArch64.Cfg.validate p521)
  keeping (VectorTaint.ofRegs [.x0, .x19, .x20])
  using mulPSum mulNSum sqrPSum
taint_summary scalarsSum : VectorTaint.taint (VectorTaint.ofRegs [.x0])
  (Impl.Ecdsa.Verify.AArch64.Cfg.scalars p521)
  keeping (VectorTaint.ofRegs [.x0, .x19, .x20])
  using mulPSum mulNSum sqrPSum
taint_summary nPowSum : VectorTaint.taint (VectorTaint.ofRegs [.x0])
  p521.nPow
  keeping (VectorTaint.ofRegs [.x0, .x20])
  using mulPSum mulNSum sqrPSum
taint_summary uvSum : VectorTaint.taint (VectorTaint.ofRegs [.x0])
  (Impl.Ecdsa.Verify.AArch64.Cfg.uv p521)
  keeping (VectorTaint.ofRegs [.x0, .x19, .x20])
  using mulPSum mulNSum sqrPSum

/-- Constant time for the registers `rs`, by taint tracking, with the field
functions' summaries. -/
macro "reg_ct" rs:term : tactic => `(tactic|
  exact VG.Taint.constantTime_of_exists (A := VectorTaint.taint) (Taint.ofRegs $rs, RegSet.empty)
    (fun _ _ _ _ h => VectorTaint.agree_initial h) (by taint_decide_sum [mulPSum, mulNSum, sqrPSum]))

/-- The window method's slots, which the public NAF uses. -/
abbrev Kq := packedQ p521

theorem add_checks : AddCChecks Kq Kq.D Kq.E Kq.R := {
    zero := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> reg_ct [.x0]
    copyP := by reg_ct [.x0]
    copyQ := by reg_ct [.x0]
    head := by reg_ct [.x0]
    tail := by reg_ct [.x0]
    double := by reg_ct [.x0]
    infinity := by reg_ct [.x0] }

theorem keep_of {c : Prog isa}
    (h : (instrs c).all (fun i => decide (clobbers i .x19 = false ∧ clobbers i .x20 = false)) = true) :
    ∀ r ∈ [Reg.x19, .x20], ∀ i ∈ instrs c, clobbers i r = false := by
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

theorem dblu_keep : ∀ r ∈ [Reg.x19, .x20], ∀ {s t tr},
    Exec isa (fprogB Kq.M (PubNaf.dbluOps Kq)) s tr t → t.gpr r = s.gpr r := by
  -- Both registers in one evaluation of the code.
  have h : ([Reg.x19, .x20].all fun r => topAll (keepsReg r) (fprogB Kq.M (PubNaf.dbluOps Kq)) &&
      ((fprogB Kq.M (PubNaf.dbluOps Kq)).calls.all fun nb =>
        (straight nb.2).any (restores r) || nb.2.allInstrs (keepsReg r))) = true := by decide +kernel
  intro r hr s t tr he
  have hh := List.all_eq_true.mp h r hr
  rw [Bool.and_eq_true] at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact gpr_top (by decide) he hh.1 hh.2

theorem zaddu_keep : ∀ r ∈ [Reg.x19, .x20], ∀ {s t tr},
    Exec isa (fprogB Kq.M (PubNaf.zadduOps Kq)) s tr t → t.gpr r = s.gpr r := by
  -- Both registers in one evaluation of the code.
  have h : ([Reg.x19, .x20].all fun r => topAll (keepsReg r) (fprogB Kq.M (PubNaf.zadduOps Kq)) &&
      ((fprogB Kq.M (PubNaf.zadduOps Kq)).calls.all fun nb =>
        (straight nb.2).any (restores r) || nb.2.allInstrs (keepsReg r))) = true := by decide +kernel
  intro r hr s t tr he
  have hh := List.all_eq_true.mp h r hr
  rw [Bool.and_eq_true] at hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl <;> exact gpr_top (by decide) he hh.1 hh.2

theorem window_checks : PubNaf.WindowChecks Kq where
  table := {
    copyP := by reg_ct [.x0]
    ptr := by reg_ct [.x0]
    store := by reg_ct [.x0, .x20]
    set := by reg_ct [.x0, .x20]
    dblu := by reg_ct [.x0]
    zaddu := by reg_ct [.x0]
    bump := by reg_ct [.x0, .x19, .x20]
    keepD := dblu_keep
    keep := zaddu_keep }
  cache := by reg_ct [.x0]
  infinity := by reg_ct [.x0]
  counter := by reg_ct [.x0]
  step := {
    dec := by reg_ct [.x0, .x19]
    dbl := by reg_ct [.x0]
    digit := {
      read := by reg_ct [.x0, .x19]
      lookup := by reg_ct [.x0, .x2]
      sign := by reg_ct [.x0, .x19]
      neg := by reg_ct [.x0]
      add := add_checks
      copy := by reg_ct [.x0] } }
  finish := by reg_ct [.x0]

theorem prep_checks : PubNaf.PrepChecks Kq (p521.sl V) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic Kq.M.n)


/-- Everything up to the public comb, with the summaries of its parts. -/
theorem before_checks : ConstantTime isa (fun _ => True)
    (AArch64.Taint.Agree (Taint.ofRegs [.x0, .x1, .x2, .x3])) (verifyPrefix p521) :=
  VG.Taint.constantTime_of_exists (A := VectorTaint.taint) (Taint.ofRegs [.x0, .x1, .x2, .x3], RegSet.empty)
    (fun _ _ _ _ h => VectorTaint.agree_initial h)
    (by taint_decide_sum [mulPSum, mulNSum, sqrPSum, validateSum, scalarsSum, nPowSum, uvSum])

/-- The public comb's iterations, and the code before and after the multiplications. -/
theorem packed_verify_checks : PackedNafVerifyChecks p521 where
  before := before_checks
  comb := {
    init := by reg_ct [.x0]
    head := by reg_ct [.x0, .x19]
    tail := by reg_ct [.x0, .x19, .x16] }
  save := by reg_ct [.x0]
  prep := prep_checks
  window := window_checks
  tail := by reg_ct [.x0]

end VG.Proof.Ecdsa.Verify.AArch64.P521
