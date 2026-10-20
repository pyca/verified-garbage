module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.EncapsTop
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.EncapsTop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms

/-!
# The 16-bit `vg_mlkem768_encaps` and `vg_mlkem1024_encaps`

The instances of `using_correctHW` and `encapsHW_ct` for ML-KEM-768 and
ML-KEM-1024, with the taint analyses of the rest of the code decided on
each, and their contract, as `Hybrid/Final.lean` (`encapsHW768_verified`,
`encapsHW1024_verified`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Hybrid

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole prfW prfW_valid enG768_correct enG1024_correct symSums)
open VG.Proof.MlKem

theorem restHW768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
    (.seq (Impl.MlKem.AArch64.Hybrid.tailH (fixedHash c)) (Impl.MlKem.AArch64.Kem16.enRest (prfW c) lay768)) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem restHW1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃h,((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
    (.seq (Impl.MlKem.AArch64.Hybrid.tailH (fixedHash c))
      (Impl.MlKem.AArch64.Kem16.enRest (prfW c) Impl.MlKem1024.AArch64.lay1024)) h).isSome=true := by
  taint_decide_generic c := hole using hS

theorem matrixHW768_depth : (Impl.MlKem.AArch64.Hybrid.matrixH lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768) true).aarch64Depth ≤ 8 := by
  decide +kernel
theorem matrixHW1024_depth :
    (Impl.MlKem.AArch64.Hybrid.matrixH Impl.MlKem1024.AArch64.lay1024
      (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024) true).aarch64Depth ≤ 8 := by
  decide +kernel

/-! ## ML-KEM-768 -/

theorem encapsHW768_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S lay768)).pre (entryContractS (encapsAArch64S lay768)).pub
      (Impl.MlKem.AArch64.Kem16.encaps (fixedHash v.callee) (prfW v.callee) lay768) :=
  encapsHW_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem.AArch64.KeyGen.wf768 srcOk768 hashOk768 habs768
    startH768_taint (restHW768_taint v.callee (symSums v))

theorem encapsHW768_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Impl.MlKem.AArch64.Kem16.encaps (fixedHash v.callee) (prfW v.callee) lay768)
      encapsH768Contract := by
  refine Verified.of_correct (T:=AArch64.target) (k:=entryContractS (encapsAArch64S lay768)) ?_
    (encapsHW768_ct v) ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctHW (fixedHash v.callee) (prfW_valid v) (enG768_correct v)
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1)) ⟨ss.2.sp, ss.2.args⟩ srcOk768 hashOk768
      Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 ts.1 ts.2 matrixHW768_depth (tailH_depth v)
  · exact ⟨fun _ h=>encapsH768_entry h,fun _ _ h hp=>encapsH768_post h hp,
      fun _ _ hs ht hp=>encapsH768_pub hs ht hp,encapsH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem encapsHW1024_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Kem16.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) :=
  encapsHW_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 srcOk1024 hashOk1024 habs1024
    startH1024_taint (restHW1024_taint v.callee (symSums v))

theorem encapsHW1024_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target
      (Impl.MlKem.AArch64.Kem16.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
      encapsH1024Contract := by
  refine Verified.of_correct (T:=AArch64.target)
    (k:=entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)) ?_ (encapsHW1024_ct v) ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctHW (fixedHash v.callee) (prfW_valid v) (enG1024_correct v)
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1)) ⟨ss.2.sp, ss.2.args⟩
      srcOk1024 hashOk1024 Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 ts.1 ts.2 matrixHW1024_depth
      (tailH_depth v)
  · exact ⟨fun _ h=>encapsH1024_entry h,fun _ _ h hp=>encapsH1024_post h hp,
      fun _ _ hs ht hp=>encapsH1024_pub hs ht hp,encapsH1024_sat⟩

end VG.Proof.MlKem.AArch64.Hybrid
