module

import VerifiedGarbage.Proof.MlDsa.AArch64.Message.OptimizedRel
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRoots
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCT
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsEntry
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Neon.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Pre
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
public import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.Samp
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Lit
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.ResidentLit
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedTableMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseTableWords
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.TableWords
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.SignCall
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRoots
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.StaticRootsFrame
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Hash
import VerifiedGarbage.Proof.Framework.AArch64.Syms

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
