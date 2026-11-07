module

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message.Paired
open VG.Proof.MlDsa.AArch64.Message.Optimized (call_tr MovedS)
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlDsa.AArch64.Sign (StaticRoots PairedRoots pairedSignRootConsts)

abbrev rootsAt (s : State) : Addr × Addr × Addr :=
  (s.syms "VG_MLDSA_NTT_EXPANDED",s.syms "VG_MLDSA_INV_FOLDED",s.syms "VG_MLDSA_INV_PAIR")
abbrev rootPairRegions (tab : Addr × Addr × Addr) : List Region := [⟨tab.1,3904⟩,⟨tab.2.1,3904⟩,⟨tab.2.2,4096⟩]
theorem rootsAt_syms {s t : State} (h : t.syms=s.syms) : rootsAt t=rootsAt s := by simp only [rootsAt,h]

variable {p : Params}
end VG.Proof.MlDsa.AArch64.Message.Paired
