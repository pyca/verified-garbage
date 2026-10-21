module

import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.DecapsTop
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DecapsFinal
public import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.DecapsTop
meta import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.DecapsFinal
meta import VerifiedGarbage.Impl.MlKem.AArch64.Kem16P
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Hole
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Prf
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbolsMono
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.ShapesCorrect
meta import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenChecks
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Entry
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
meta import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
meta import VerifiedGarbage.TCB.Axioms

/-!
# `vg_mlkem768_decaps` and `vg_mlkem1024_decaps` computing PRF outputs in the matrix

The instances of `using_correctDP` and `decapsP_ct` for ML-KEM-768 and
ML-KEM-1024, with the taint analyses of `J(z ‖ c)` and of the rest of the code
decided on each, and their contract (`Kem16/DecapsFinal.lean`).
-/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Kem16P

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Proof.MlKem.AArch64
open VG.Proof.MlKem.AArch64.Kem
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (decapsAArch64S entryContractS preSD entryS_tables srcOkJ768 srcOkJ1024
  hashOkJ768 hashOkJ1024 habsJ768 habsJ1024 startJ768_taint startJ1024_taint decapsH768Contract
  decapsH1024Contract decapsH768_entry decapsH768_post decapsH768_pub decapsH768_sat decapsH1024_entry
  decapsH1024_post decapsH1024_pub decapsH1024_sat)
open VG.Proof.MlKem.AArch64.FixedHash (fixedHash hole prfW prfW_valid deG768_correct deG1024_correct symSums
  deStart768_depth deStart1024_depth)
open VG.Proof.MlKem

theorem tailJ_taint : ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
    (.block Impl.MlKem.AArch64.Kem16.tailJ) h).isSome = true :=
  ⟨_, by taint_decide⟩

theorem deRestP768_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.deRestP (prfW c) lay768 (Impl.MlKem.AArch64.Kem16P.placed lay768
        (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc lay768)))) h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem deRestP1024_taint (c : Impl.Sha3.AArch64.Callee)
    (hS : Taint.AllOk (VectorSymbols.analysis restSymbols) (Proof.Sha3.AArch64.Callers.sums c)) :
    ∃ h, ((VectorSymbols.analysis restSymbols).check (VectorTaint.ofRegs [.x25,.x26,.x27,.x28])
      (Impl.MlKem.AArch64.Kem16P.deRestP (prfW c) Impl.MlKem1024.AArch64.lay1024
        (Impl.MlKem.AArch64.Kem16P.placed Impl.MlKem1024.AArch64.lay1024
          (Impl.MlKem.AArch64.Hybrid.hashPairs (Impl.MlKem.AArch64.Kem16.jSrc Impl.MlKem1024.AArch64.lay1024))))
      h).isSome = true := by
  taint_decide_generic c := hole using hS

theorem matrixPJ768_depth :
    (Impl.MlKem.AArch64.Kem16P.matrixP lay768 (Impl.MlKem.AArch64.Kem16.jSrc lay768)
      (.block Impl.MlKem.AArch64.Kem16.tailJ)).aarch64Depth ≤ 8 := by
  decide +kernel

theorem matrixPJ1024_depth :
    (Impl.MlKem.AArch64.Kem16P.matrixP Impl.MlKem1024.AArch64.lay1024
      (Impl.MlKem.AArch64.Kem16.jSrc Impl.MlKem1024.AArch64.lay1024)
      (.block Impl.MlKem.AArch64.Kem16.tailJ)).aarch64Depth ≤ 8 := by
  decide +kernel

/-! ## ML-KEM-768 -/

theorem decapsP768_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (decapsAArch64S lay768)).pre (entryContractS (decapsAArch64S lay768)).pub
      (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) lay768) :=
  decapsP_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem.AArch64.KeyGen.wf768 (deG768_correct v)
    VG.Proof.MlKem.AArch64.Encaps.calls768 (by decide) srcOkJ768 hashOkJ768 (deStart768_depth v) habsJ768
    (startJ768_taint v.callee (symSums v)) tailJ_taint (deRestP768_taint v.callee (symSums v))

theorem decapsP768_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
    (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) lay768) decapsH768Contract := by
  refine Verified.of_correct (T := AArch64.target) (k := entryContractS (decapsAArch64S lay768)) ?_
    (decapsP768_ct v) ?_
  · intro s h
    have ss := preSD h.1
    have ts := entryS_tables h
    exact using_correctDP (fixedHash v.callee) (prfW_valid v) (deG768_correct v)
      (kem_unstrip (Decaps.pre_of VG.Proof.MlKem.AArch64.KeyGen.wf768 ss.1)) ⟨ss.2.sp, ss.2.args⟩
      srcOkJ768 hashOkJ768 (by decide) Noise.room768 VG.Proof.MlKem.AArch64.Encaps.calls768 ts.1 ts.2
      (by decide) (by decide) (deStart768_depth v) matrixPJ768_depth
  · exact ⟨fun _ h => decapsH768_entry h, fun _ _ h hp => decapsH768_post h hp,
      fun _ _ hs ht hp => decapsH768_pub hs ht hp, decapsH768_sat⟩

/-! ## ML-KEM-1024 -/

theorem decapsP1024_ct (v : Proof.Sha3.AArch64.Permutation) :
    ConstantTime isa (entryContractS (decapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pre
      (entryContractS (decapsAArch64S Impl.MlKem1024.AArch64.lay1024)).pub
      (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024) :=
  decapsP_ct (fixedHash v.callee) (prfW v.callee) VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 (deG1024_correct v)
    VG.Proof.MlKem1024.AArch64.Encaps.calls1024 (by decide) srcOkJ1024 hashOkJ1024 (deStart1024_depth v) habsJ1024
    (startJ1024_taint v.callee (symSums v)) tailJ_taint (deRestP1024_taint v.callee (symSums v))

theorem decapsP1024_verified (v : Proof.Sha3.AArch64.Permutation) : Verified AArch64.target
    (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    decapsH1024Contract := by
  refine Verified.of_correct (T := AArch64.target)
    (k := entryContractS (decapsAArch64S Impl.MlKem1024.AArch64.lay1024)) ?_ (decapsP1024_ct v) ?_
  · intro s h
    have ss := preSD h.1
    have ts := entryS_tables h
    exact using_correctDP (fixedHash v.callee) (prfW_valid v) (deG1024_correct v)
      (kem_unstrip (Decaps.pre_of VG.Proof.MlKem1024.AArch64.KeyGen.wf1024 ss.1)) ⟨ss.2.sp, ss.2.args⟩
      srcOkJ1024 hashOkJ1024 (by decide) Noise.room1024 VG.Proof.MlKem1024.AArch64.Encaps.calls1024 ts.1 ts.2
      (by decide) (by decide) (deStart1024_depth v) matrixPJ1024_depth
  · exact ⟨fun _ h => decapsH1024_entry h, fun _ _ h hp => decapsH1024_post h hp,
      fun _ _ hs ht hp => decapsH1024_pub hs ht hp, decapsH1024_sat⟩

end VG.Proof.MlKem.AArch64.Kem16P
