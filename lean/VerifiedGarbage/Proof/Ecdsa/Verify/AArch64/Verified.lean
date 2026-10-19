module

import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafMain
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Contract
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Lit
import VerifiedGarbage.Proof.Ecdsa.AArch64.Verified
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointLit
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPrefix
public import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedLit
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Abi
public import VerifiedGarbage.Proof.P256.EcdhDouble.Certificate
public import VerifiedGarbage.Proof.P256.Linear.WeakCertificate
public import VerifiedGarbage.Proof.P256.VerifyAllocated.CachedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.JacTail
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedHead
public import VerifiedGarbage.Proof.P256.VerifyAllocated.MixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticCachedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticJacTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticMixedTail
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticRR
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableHead
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticTableTail
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacContract
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPointsTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.CachedChecks
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Find
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Impl.Ecdh.P256.AArch64
import VerifiedGarbage.Impl.P256.EcdhJac
import VerifiedGarbage.Proof.EcKey.PublicKey
import VerifiedGarbage.Proof.Ecdh.AArch64.Peer
import VerifiedGarbage.Proof.Ecdsa.AArch64.Finish
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Main
import VerifiedGarbage.Proof.Ecdsa.AArch64.Middle
import VerifiedGarbage.Proof.Ecdsa.AArch64.Padd
import VerifiedGarbage.Proof.Ecdsa.AArch64.Scalar
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps
import VerifiedGarbage.Proof.Ecdsa.Projective
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.Verify
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedCached
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedFixedDigitTiming
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.AllocatedPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacChecks
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JacPoints
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.JointCache
import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafPoints
import VerifiedGarbage.Proof.Ed25519.AArch64.SqrRows
import VerifiedGarbage.Proof.Framework.AArch64.RelCT
import VerifiedGarbage.Proof.Framework.AArch64.Simd
import VerifiedGarbage.Proof.Framework.AArch64.Simd64
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.BitByte
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Pratt
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
import VerifiedGarbage.Proof.P256.EcdhDouble.Field
import VerifiedGarbage.Proof.P256.EcdhDouble.LinearField
import VerifiedGarbage.Proof.P256.EcdhDouble.Verified
import VerifiedGarbage.Proof.P256.EcdhJac.StoreWords
import VerifiedGarbage.Proof.P256.Linear.WeakAdd
import VerifiedGarbage.Proof.P256.Prime
import VerifiedGarbage.Proof.P256.VerifyAllocated.Timing
import VerifiedGarbage.Proof.P256.VerifyTable.Env
import VerifiedGarbage.Proof.P256.VerifyTable.Store
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedJointDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.AllocatedState
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticAdd
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.ArithmeticTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Blocks
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bytes
import VerifiedGarbage.Proof.Weierstrass.AArch64.BytesLen
import VerifiedGarbage.Proof.Weierstrass.AArch64.CachedLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafArith
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafDigits
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafExec
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.FastNafPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ArithmeticProduction
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.CT
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.DeadOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Double
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.FoldOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.ForwardOk
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Refine
import VerifiedGarbage.Proof.Weierstrass.AArch64.Forward.Snapshot
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTree
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacTreeStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowDouble
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowState
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowSumTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedDigitTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointFixedLookupTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoad
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointPrep
import VerifiedGarbage.Proof.Weierstrass.AArch64.JointSignTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall521
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontFn384
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafArithmeticTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafChoose
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafCore
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinish
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafFinishTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoop
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafLoopTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTable
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableCopy
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableInit
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableStep
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafTableTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.NafWindow
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombDigit
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelect
import VerifiedGarbage.Proof.Weierstrass.AArch64.TCombSelectV
import VerifiedGarbage.Proof.Weierstrass.AArch64.Window
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowEntry
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowQuad
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowSum
import VerifiedGarbage.Proof.Weierstrass.AArch64.WindowTable
import VerifiedGarbage.Proof.Weierstrass.BytesLen
import VerifiedGarbage.Proof.Weierstrass.JacInplace
import VerifiedGarbage.Proof.Weierstrass.WinJacMath
import VerifiedGarbage.Spec.Ecdsa.Verify.P256
import VerifiedGarbage.Spec.Weierstrass.Mul

/-! ## `JacAbi` -/

@[expose] public section

section

/-! Production P-256 Jacobian verification preserves the existing ABI and result contract. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jacPre_of {s : State} (h : verifyAArch64.pre s) : VPre p256 s := by
  obtain ⟨h1,h2,h3,h4,h5,h6,held,fit,hdw⟩ := h
  exact ⟨h1,h2,h3,h4,h5,h6,⟨by rw [h1]; simp,held,fit,hdw _ (by simp)⟩⟩

theorem jacVerify_callsKeep : CallsKeep verifyP256 := by lit_decide

theorem jacVerify_untouched : KeepsUntouched verifyP256 := by lit_decide

theorem jacVerify_keepsV : verifyP256.allInstrs keepsV=true := by lit_decide

theorem jacVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s', Exec isa verifyP256 s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := nafVerify_ok (p256_ok hI) (by decide) hL hT (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jacVerify_callsKeep jacVerify_untouched jacVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointAbi` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_callsKeep : CallsKeep P256Joint.verify := by lit_decide

theorem jointVerify_untouched : KeepsUntouched P256Joint.verify := by lit_decide

theorem jointVerify_keepsV : P256Joint.verify.allInstrs keepsV=true := by lit_decide

theorem jointVerify_a64_of_wp
    (correct : ∀ s,VPre p256 s → WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' := by
  obtain ⟨t,s',he,hsv,hpost⟩ := correct s (jacPre_of hs)
  exact ⟨t,s',he,abiPreserved_of he jointVerify_callsKeep jointVerify_untouched jointVerify_keepsV hsv,hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `AllocatedAbi` -/

section

/-! The allocated verifier temporarily uses x26–x28 and x30. Its ABI proof
uses the actual save/restore contracts, rather than declaring those registers
syntactically untouched by the optimized arithmetic. -/
namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64 VG.Proof.Weierstrass.AArch64

private structure OldSafe (c : Prog isa) : Prop where
  untouched : KeepsUntouched c
  callsKeep : CallsKeep c

private theorem callsKeep_seq {a b : Prog isa} : CallsKeep (.seq a b) ↔ CallsKeep a ∧ CallsKeep b := by
  simp only [CallsKeep, Code.calls, List.all_append, Bool.and_eq_true]

private theorem OldSafe.left {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe a :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).1,(callsKeep_seq.mp h.callsKeep).1⟩

private theorem OldSafe.right {a b : Prog isa} (h : OldSafe (.seq a b)) : OldSafe b :=
  ⟨(Bool.and_eq_true_iff.mp h.untouched).2,(callsKeep_seq.mp h.callsKeep).2⟩

private theorem OldSafe.seq {a b : Prog isa} (ha : OldSafe a) (hb : OldSafe b) : OldSafe (.seq a b) :=
  ⟨Bool.and_eq_true_iff.mpr ⟨ha.untouched,hb.untouched⟩,callsKeep_seq.mpr ⟨ha.callsKeep,hb.callsKeep⟩⟩

private theorem oldSafe : OldSafe P256Joint.verify := ⟨jointVerify_untouched,jointVerify_callsKeep⟩

private theorem before_safe : OldSafe (beforeInverse p256) := by
  have h := oldSafe
  exact h.left.seq (h.right.left.seq (h.right.right.left.seq (h.right.right.right.left.seq
    (h.right.right.right.right.left.seq (h.right.right.right.right.right.left.seq ⟨rfl,rfl⟩)))))

private theorem uv_safe : OldSafe (Cfg.uv p256) := oldSafe.right.right.right.right.right.right.right.left

private theorem tail_safe : OldSafe (Cfg.tail p256) := oldSafe.right.right.right.right.right.right.right.right.right

private theorem OldSafe.keeps {c : Prog isa} {s t : State} {tr : List Leak} (h : OldSafe c)
    (he : Exec isa c s tr t) : ∀ r∈VG.Proof.Ecdsa.AArch64.untouched,t.gpr r=s.gpr r :=
  untouched_keep he h.callsKeep h.untouched

 theorem allocatedVerify_keepsV : P256Allocated.verify.allInstrs keepsV=true := by lit_decide

/-- Actual restoration, together with the existing saved-register result, suffices for the ABI. -/
theorem allocated_abiPreserved_of {s t : State} {tr : List Leak}
    (he : Exec isa P256Allocated.verify s tr t)
    (hsv : ∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r)
    (hu : ∀ r∈untouched,t.gpr r=s.gpr r) : abiPreserved s t := by
  refine ⟨fun r hr => ?_,Exec.sp he,Exec.preservedV he allocatedVerify_keepsV⟩
  by_cases hh : r∈untouched
  · exact hu r hh
  · apply hsv r
    revert hh
    revert r
    decide

/-- Compose the two restored arithmetic stages with the unchanged surrounding code. -/
theorem allocatedVerify_extra_preserved (hc : CfgOk p256)
    (hprefix : ∀ s,VPre p256 s → WP isa allocatedPrefix s fun t => ∃ g,Mid p256 s (s.gpr .x3) g t)
    (hinverse : ∀ s₀ s,InverseInput p256 s₀ (s₀.gpr .x3) s →
      WP isa P256Allocated.inverse s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    (hpoints : ∀ s₀ g s,VPre p256 s₀ → Mid p256 s₀ (s₀.gpr .x3) g s →
      WP isa P256Allocated.points s fun t => ∀ r∈untouched,t.gpr r=s.gpr r)
    {s s' : State} {tr : List Leak} (hp : VPre p256 s)
    (he : Exec isa P256Allocated.verify s tr s') : ∀ r∈untouched,s'.gpr r=s.gpr r := by
  obtain ⟨a,b,tp,tq,tt,ep,eq,et,_⟩ := allocatedVerify_cut he
  obtain ⟨i,j,ti,tj,tu,ei,ej,eu,_⟩ := allocatedPrefix_cut ep
  obtain ⟨_,_,ebi,ib⟩ := beforeInverse_ok hc hp
  obtain ⟨_,rfl⟩ := ei.det ebi
  obtain ⟨_,_,einv,ki⟩ := hinverse s i ib
  obtain ⟨_,rfl⟩ := ej.det einv
  obtain ⟨_,_,em,g,hm⟩ := hprefix s hp
  obtain ⟨_,rfl⟩ := ep.det em
  obtain ⟨_,_,ept,kp⟩ := hpoints s g a hp hm
  obtain ⟨_,rfl⟩ := eq.det ept
  intro r hr
  exact (tail_safe.keeps et r hr).trans ((kp r hr).trans ((uv_safe.keeps eu r hr).trans
    ((ki r hr).trans (before_safe.keeps ei r hr))))

 theorem allocatedVerify_a64_of_wp
    (correct : ∀ s,VPre p256 s → WP isa P256Allocated.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t)
    (restored : ∀ {s t : State} {tr : List Leak},VPre p256 s →
      Exec isa P256Allocated.verify s tr t → ∀ r∈untouched,t.gpr r=s.gpr r)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ tr t,Exec isa P256Allocated.verify s tr t ∧ abiPreserved s t ∧ verifyAArch64.post s t := by
  have hp := jacPre_of hs
  obtain ⟨tr,t,he,hsv,hpost⟩ := correct s hp
  exact ⟨tr,t,he,allocated_abiPreserved_of he hsv (restored hp he),hpost⟩

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointCorrect` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

theorem jointVerify_ok (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    {s : State} (h : VPre p256 s) :
    WP isa P256Joint.verify s fun t =>
      (∀ r∈Cfg.saved.map Prod.fst,t.gpr r=s.gpr r) ∧ VPost p256 s t :=
  verify_of_joint (p256_ok hI) hL P256Joint.points P256Joint.verify rfl
    (by
      intro s₀ base g s hm ht P hp hr
      exact jointPoints_ok (p256_ok hI) hL hT hm ht hp hr) h

theorem jointVerify_a64 (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    (s : State) (hs : verifyAArch64.pre s) :
    ∃ t s',Exec isa P256Joint.verify s t s' ∧ abiPreserved s s' ∧ verifyAArch64.post s s' :=
  jointVerify_a64_of_wp (fun _ hp => jointVerify_ok hL hI hT hp) s hs

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `JointVerified` -/

section

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Joint verification satisfies the existing correctness, ABI, and public-input contract. -/
theorem jointVerify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start)
    :
    Verified AArch64.target P256Joint.verify
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_,?_,implies.sat⟩
  · obtain ⟨t,s',he,ha,hp⟩ := jointVerify_a64 hL hI hT s (implies.pre _ hs)
    exact ⟨t,s',he,ha,implies.post s s' hs hp⟩
  · intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
    exact jointVerify_ct_of_points (p256_ok hI) jointPrefix_ct
      (fun _ _ ps pt => jointPoints_relCT (p256_ok hI) hL hT ps pt) jointTail_ct
      _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂))
      (jacPublic_of_spec pub) e₁ e₂

end VG.Proof.Ecdsa.Verify.AArch64

end

/-! ## `Verified` -/

section

/-!
# Verified Jacobian P-256 verification on AArch64

The Jacobian comb and sparse signed-window multiplications satisfy the existing
verification contract. Table addresses and exceptional-point branches depend
only on the public key, digest and signature declared public by that contract.
-/

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Ecdsa.Verify.AArch64
open VG.Proof.Ecdsa.AArch64

/-- Use the public inputs declared by the shared specification directly. -/
theorem verify_ct (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    ConstantTime isa
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pre
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)).pub verifyP256 := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' pre₁ pre₂ pub e₁ e₂
  apply nafVerify_public_ct (p256_ok hI) (by decide) hL hT nafVerify_checks
    _ _ _ _ _ _ (jacPre_of (implies.pre _ pre₁)) (jacPre_of (implies.pre _ pre₂)) (jacPublic_of_spec pub) e₁ e₂

theorem verify_verified (hL : Weierstrass.Law Spec.P256.curve) (hI : Weierstrass.AArch64.InvSounds)
    (hT : Weierstrass.CombOkW Spec.P256.curve 7 37 Impl.P256.p256Comb7 Impl.P256.p256Comb7Start) :
    Verified AArch64.target verifyP256
      (Spec.Ecdsa.P256.inst.verifyContract (AArch64.abi.withConsts p256.combConsts)) := by
  refine ⟨fun s hs => ?_, verify_ct hL hI hT, implies.sat⟩
  obtain ⟨t, s', he, ha, hp⟩ := jacVerify_a64 hL hI hT s (implies.pre _ hs)
  exact ⟨t, s', he, ha, implies.post s s' hs hp⟩

end VG.Proof.Ecdsa.Verify.AArch64

end
