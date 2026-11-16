module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
meta import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafTiming
import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
meta import VerifiedGarbage.Impl.Ecdsa.Verify.P384.AArch64
import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Framework.TaintBatch
meta import VerifiedGarbage.Proof.Framework.AArch64.TaintSym
import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
meta import VerifiedGarbage.Proof.Ed25519.AArch64.RowAcc
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.PubNafMul
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.RelCTAssoc
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
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Add
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddC
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.AddTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.CacheBuild
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Table
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.TableCoZ
import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.CoZTable
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Proof.Weierstrass.MulContract
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
public import VerifiedGarbage.Impl.AArch64Instrs
public import VerifiedGarbage.Impl.Ecdsa.P384.AArch64.Cfg
public import VerifiedGarbage.Impl.Ecdsa.Verify.AArch64
public import VerifiedGarbage.Impl.Weierstrass.AArch64.Joint
public import VerifiedGarbage.Impl.Weierstrass.AArch64.PubNaf
public import VerifiedGarbage.Proof.Ecdh.AArch64.Window
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Front
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.PrepTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.PubNaf.WindowTiming
public import VerifiedGarbage.Proof.Weierstrass.AArch64.TComb

/-!
# ECDSA verification over P-384 on AArch64: what taint tracking checks

Each piece of the public NAF of `v` whose timing the relational proof of the joint loop
(`Joint.verify_public_ct`) takes from taint tracking, with the registers it may branch on or
address by: the pointer `x0` for the field arithmetic, and the loop counters, the digits' and
entries' registers and the recoding's residual elsewhere.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.AArch64.P384

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64 VG.Proof.Weierstrass.AArch64
open VG.Impl.Weierstrass.AArch64

/-- Constant time for the registers `rs`, by taint tracking. -/
macro "reg_ct" rs:term : tactic => `(tactic|
  exact VG.Taint.constantTime (A := taint) (Taint.ofRegs $rs) (fun _ _ _ _ h => h) (by taint_decide))

/-- The window method's slots, which the public NAF uses. -/
abbrev Kq := winQ p384

/-- `reg_ct`'s proof, with the check left as a goal: for `taint_decide_all`. -/
local macro "reg_ct% " rs:term : term =>
  `(VG.Taint.constantTime (A := taint) (Taint.ofRegs $rs) (fun _ _ _ _ h => h) (hc := ?_) ?_)

theorem keep_of {c : Prog isa}
    (h : (instrs c).all (fun i => decide (clobbers i .x19 = false ∧ clobbers i .x20 = false)) = true) :
    ∀ r ∈ [Reg.x19, .x20], ∀ i ∈ instrs c, clobbers i r = false := by
  intro r hr i hi
  have hh := of_decide_eq_true (List.all_eq_true.mp h i hi)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hh.1
  · exact hh.2

/-- The checks of the window method and of its additions (`add_checks`) are one kernel
evaluation (`taint_decide_all`): each piece is field arithmetic analysed from the same taint,
the pointer `x0` public, which the kernel then finds again. So are the two checks that the
table's doubling and addition keep `x19` and `x20` (`hk`), of code two of the taint checks
have built. -/
theorem window_checks : PubNaf.WindowChecks Kq := by
  refine (fun (hk :
      (fprogB Kq.M (PubNaf.dbluOps Kq)).allInstrs
          (fun i => decide (clobbers i .x19 = false ∧ clobbers i .x20 = false)) = true ∧
        (fprogB Kq.M (PubNaf.zadduOps Kq)).allInstrs
          (fun i => decide (clobbers i .x19 = false ∧ clobbers i .x20 = false)) = true) => ?_) ⟨?_, ?_⟩
  refine {
    table := {
      copyP := reg_ct% [.x0]
      ptr := reg_ct% [.x0]
      store := reg_ct% [.x0, .x20]
      set := reg_ct% [.x0, .x20]
      dblu := reg_ct% [.x0]
      zaddu := reg_ct% [.x0]
      bump := reg_ct% [.x0, .x19, .x20]
      keepD := ?keepD
      keep := ?keep }
    cache := reg_ct% [.x0]
    infinity := reg_ct% [.x0]
    counter := reg_ct% [.x0]
    step := {
      dec := reg_ct% [.x0, .x19]
      dbl := reg_ct% [.x0]
      digit := {
        read := reg_ct% [.x0, .x19]
        lookup := reg_ct% [.x0, .x2]
        sign := reg_ct% [.x0, .x19]
        neg := reg_ct% [.x0]
        add := {
          zero := ?zero
          copyP := reg_ct% [.x0]
          copyQ := reg_ct% [.x0]
          head := reg_ct% [.x0]
          tail := reg_ct% [.x0]
          double := reg_ct% [.x0]
          infinity := reg_ct% [.x0] }
        copy := reg_ct% [.x0] } }
    finish := reg_ct% [.x0] }
  case keepD =>
    intro r hr s t tr he
    exact Exec.gpr (keep_of (by rw [← Code.allInstrs_eq]; exact hk.1) r hr) he (Or.inr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> decide))
  case keep =>
    intro r hr s t tr he
    exact Exec.gpr (keep_of (by rw [← Code.allInstrs_eq]; exact hk.2) r hr) he (Or.inr (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> decide))
  case zero =>
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> reg_ct [.x0]
  taint_decide_all

theorem add_checks : AddCChecks Kq Kq.D Kq.E Kq.R := window_checks.step.digit.add

theorem prep_checks : PubNaf.PrepChecks Kq (p384.sl V) where
  init := by reg_ct [.x0]
  step := by reg_ct (PubNaf.prepPublic Kq.M.n)

end VG.Proof.Ecdsa.Verify.AArch64.P384
