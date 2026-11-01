module

public import VerifiedGarbage.Proof.Ed25519.Point64Contract
public import VerifiedGarbage.TCB.X86_64.Target
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Verified
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
public import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
public import VerifiedGarbage.Impl.X25519.X86_64.Adx
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.TCB.X86_64.Target
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Verified
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Keeps
meta import VerifiedGarbage.Proof.Ed25519.X86_64.Point64.Lit
meta import VerifiedGarbage.Impl.Ed25519.X86_64.Point64
meta import VerifiedGarbage.Impl.X25519.X86_64.Adx
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub

/-!
# Ed25519's point doubling and cached additions, in radix `2^64`, on x86-64: the functions' proofs

`Verified` for the doubling and the additions with the baseline's and with
BMI2 and ADX's multiplications, from their correctness (`Verified.lean`) and
constant time, for their callers.
-/

@[expose] public section

namespace VG.Proof.Ed25519.X86_64.Point64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Impl.Ed25519.X86_64.Point64 VG.Proof.Ed25519.X86_64.Point64
open VG.Impl.X25519.X86_64 (baseline adx)
open VG.Proof.Ed25519.Point64 (doubleContract addCachedContract addAffineContract)

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
