module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.EncapsTop
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
import VerifiedGarbage.Proof.Framework.KernelRfl
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.EncapsTop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Verified
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.Framework.AArch64.DepthFill
meta import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.TCB.Axioms
import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encaps
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.Encaps

/-!
# `vg_mlkem768_encaps` and `vg_mlkem1024_encaps` computing PRF outputs in the matrix

The instances of `using_correctP` and `encapsP_ct` for ML-KEM-768 and
ML-KEM-1024, with the taint analyses of `G` and of the rest of the code
decided on each, and their contract (`Hybrid/Final.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (encapsAArch64S entryContractS preS entryS_tables srcOk768 srcOk1024
  hashOk768 hashOk1024 habs768 habs1024 startH768_taint startH1024_taint encapsH768Contract encapsH1024Contract
  encapsH768_entry encapsH768_post encapsH768_pub encapsH768_sat encapsH1024_entry encapsH1024_post
  encapsH1024_pub encapsH1024_sat)
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole prfW prfW_valid enG768_correct enG1024_correct symSums)
open VG.Proof.MlKem

theorem g_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash c)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem restP768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP (prfW c) lay768
        (Impl.MlKem.AArch64.Kem16P.placed lay768 (Impl.MlKem.AArch64.Hybrid.hashPairs
          (Impl.MlKem.AArch64.Hybrid.ekSrc lay768))) .x25 0 .x28 KEM.MB .x27 0)
        (.block lay768.kemEpilogue)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem restP1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (.seq (Impl.MlKem.AArch64.Kem16P.encryptRestP (prfW c) Impl.MlKem1024.AArch64.lay1024
        (Impl.MlKem.AArch64.Kem16P.placed Impl.MlKem1024.AArch64.lay1024 (Impl.MlKem.AArch64.Hybrid.hashPairs
          (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024))) .x25 0 .x28 KEM.MB .x27 0)
        (.block Impl.MlKem1024.AArch64.lay1024.kemEpilogue)) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem matrixP768_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Kem16P.matrixP lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash v.callee))).aarch64Depth ≤ 8 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.matrixP lay768 (Impl.MlKem.AArch64.Hybrid.ekSrc lay768)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

theorem matrixP1024_depth (v : Proof.Sha3.AArch64.Permutation) :
    (Impl.MlKem.AArch64.Kem16P.matrixP Impl.MlKem1024.AArch64.lay1024
      (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash v.callee))).aarch64Depth ≤ 8 :=
  Code.aarch64Depth_le_of_fillHoles (n := v.callee.name)
    (e := Impl.MlKem.AArch64.Kem16P.matrixP Impl.MlKem1024.AArch64.lay1024
      (Impl.MlKem.AArch64.Hybrid.ekSrc Impl.MlKem1024.AArch64.lay1024)
      (Impl.MlKem.AArch64.Kem16P.gAt (fixedHash hole)))
    (by kernel_rfl) (Proof.Sha3.AArch64.fdepth_of_noFrames v.noFrames) (by decide +kernel)

/-! ## ML-KEM-768 -/

theorem encapsP768_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S lay768)).pre (entryContractS (encapsAArch64S lay768)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) lay768) :=
  encapsP_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem.AArch64.KeyGen.wf768 (enG768_correct v)
    srcOk768 hashOk768 habs768 startH768_taint (g_taint v.callee (symSums v))
    (restP768_taint v.callee (symSums v))

theorem encapsP768_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) lay768)
      encapsH768Contract := by
  refine Verified.of_correct (T := AArch64.target) (k := entryContractS (encapsAArch64S lay768)) ?_
    (encapsP768_ct v) ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctP (fixedHash v.callee) (prfW_valid v) (enG768_correct v)
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1)) ⟨ss.2.sp, ss.2.args⟩ srcOk768
      hashOk768 Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 ts.1 ts.2 (by decide) (by decide)
      (matrixP768_depth v)
  · exact ⟨fun _ h => encapsH768_entry h, fun _ _ h hp => encapsH768_post h hp,
      fun _ _ hs ht hp => encapsH768_pub hs ht hp, encapsH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem encapsP1024_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) :=
  encapsP_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 (enG1024_correct v)
    srcOk1024 hashOk1024 habs1024 startH1024_taint (g_taint v.callee (symSums v))
    (restP1024_taint v.callee (symSums v))

theorem encapsP1024_verified (v : Proof.Sha3.AArch64.Permutation) :
    Verified AArch64.target
      (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
      encapsH1024Contract := by
  refine Verified.of_correct (T := AArch64.target)
    (k := entryContractS (encapsAArch64S Impl.MlKem1024.AArch64.lay1024)) ?_ (encapsP1024_ct v) ?_
  · intro s h
    have ss := preS h.1
    have ts := entryS_tables h
    exact using_correctP (fixedHash v.callee) (prfW_valid v) (enG1024_correct v)
      (kem_unstrip (Encaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1)) ⟨ss.2.sp, ss.2.args⟩
      srcOk1024 hashOk1024 Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 ts.1 ts.2 (by decide)
      (by decide) (matrixP1024_depth v)
  · exact ⟨fun _ h => encapsH1024_entry h, fun _ _ h hp => encapsH1024_post h hp,
      fun _ _ hs ht hp => encapsH1024_pub hs ht hp, encapsH1024_sat⟩

end VG.Proof.MlKem.AArch64.Kem16P
