module

public import VerifiedGarbage.TCB.X86_64.Target
public import Mathlib.Logic.Function.Basic
public import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
public import VerifiedGarbage.Proof.Framework.Contract
meta import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
import VerifiedGarbage.Impl.Mont.Mod
import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
import VerifiedGarbage.Proof.Ed25519.X86_64.Points
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegSetOrder
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Lit
import VerifiedGarbage.Proof.Framework.X86_64.Masked
import VerifiedGarbage.Proof.Framework.X86_64.Spill
import VerifiedGarbage.Proof.X25519.Invert
import VerifiedGarbage.Proof.X25519.X86_64.AddSub
import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
import VerifiedGarbage.Proof.X25519.X86_64.Sqr
meta import VerifiedGarbage.Impl.Ed25519.X86_64.PointMul
meta import VerifiedGarbage.Impl.Mont.Mod
meta import VerifiedGarbage.Proof.Ed25519.X86_64.CachedPoint
meta import VerifiedGarbage.Proof.Ed25519.X86_64.FieldMemory
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointAccumulateLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.PointLoop
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Points
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegSetOrder
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.X86_64.Exec
meta import VerifiedGarbage.Proof.Framework.X86_64.Inline
meta import VerifiedGarbage.Proof.Framework.X86_64.Lit
meta import VerifiedGarbage.Proof.Framework.X86_64.Masked
meta import VerifiedGarbage.Proof.Framework.X86_64.Spill
meta import VerifiedGarbage.Proof.X25519.Invert
meta import VerifiedGarbage.Proof.X25519.X86_64.AddSub
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.A24
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Mul
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.Sqr
meta import VerifiedGarbage.Proof.X25519.X86_64.Adx.SqrProd
meta import VerifiedGarbage.Proof.X25519.X86_64.Sqr

/-!
# Ed25519's point doubling and cached additions, in radix `2^64`, on x86-64: the functions' proofs

`Verified` for the doubling and the additions with the baseline's and with
BMI2 and ADX's multiplications, from their correctness (`Verified.lean`) and
constant time, for `Artifacts/Ed25519R64/X86_64.lean`.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64.Point64
open VG.Impl.X25519.X86_64 (baseline adx)
open VG.Spec.Ed25519.Point64 (doubleExtApi addCachedExtApi addCachedProjApi addAffineExtApi doubleContract
  addCachedContract addAffineContract)

theorem addAffine_verified : Verified X86_64.target (addAffineFn baseline)
    (addAffineContract X86_64.abi true) :=
  Verified.of_correct (addAffine_correct addAffineFn_keeps (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    addAffK_implies

theorem addAffineAdx_verified : Verified X86_64.target (addAffineFn adx)
    (addAffineContract X86_64.abi true) :=
  Verified.of_correct (addAffine_correct addAffineFn_keeps (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    addAffK_implies

theorem doubleExt_verified : Verified X86_64.target (doubleFn baseline true)
    (doubleContract X86_64.abi true) :=
  Verified.of_correct (double_correct true (doubleFn_keeps true) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (doubleK_implies true)

theorem addExt_verified : Verified X86_64.target (addFn baseline true)
    (addCachedContract X86_64.abi true) :=
  Verified.of_correct (add_correct true (addFn_keeps true) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies true)

theorem addProj_verified : Verified X86_64.target (addFn baseline false)
    (addCachedContract X86_64.abi false) :=
  Verified.of_correct (add_correct false (addFn_keeps false) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies false)

theorem doubleExtAdx_verified : Verified X86_64.target (doubleFn adx true)
    (doubleContract X86_64.abi true) :=
  Verified.of_correct (double_correct true (doubleFn_keeps true) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (doubleK_implies true)

theorem addExtAdx_verified : Verified X86_64.target (addFn adx true)
    (addCachedContract X86_64.abi true) :=
  Verified.of_correct (add_correct true (addFn_keeps true) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies true)

theorem addProjAdx_verified : Verified X86_64.target (addFn adx false)
    (addCachedContract X86_64.abi false) :=
  Verified.of_correct (add_correct false (addFn_keeps false) (by lit_decide))
    (VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsp]) (fun _ _ _ _ hp => fnPub_agree hp)
      (by taint_decide))
    (addK_implies false)

end VG.Proof.Ed25519.X86_64.Point64
