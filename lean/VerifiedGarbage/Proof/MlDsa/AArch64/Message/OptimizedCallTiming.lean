module

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedPre

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots signRootConsts)

abbrev rootsAt (s : State) : Addr × Addr :=
  (s.syms "VG_MLDSA_NTT_EXPANDED",s.syms "VG_MLDSA_INV_FOLDED")
abbrev rootPairRegions (tab : Addr × Addr) : List Region := [⟨tab.1,3904⟩,⟨tab.2,3904⟩]
theorem rootsAt_syms {s t : State} (h : t.syms=s.syms) : rootsAt t=rootsAt s := by simp only [rootsAt,h]

variable {p : Params}
end VG.Proof.MlDsa.AArch64.Message.Optimized
