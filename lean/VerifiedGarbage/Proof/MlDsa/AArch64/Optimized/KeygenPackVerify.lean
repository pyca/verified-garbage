module
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.KeygenPack
public import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Contracts

import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.BitPack
import Mathlib.Tactic.SplitIfs
meta import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.Lit
import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.SimpleBitPack
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Bswap
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackDispatch
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoads
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
import VerifiedGarbage.Proof.MlDsa.Arith.Mem
import VerifiedGarbage.Proof.MlDsa.Pack.Arith
import VerifiedGarbage.Proof.MlDsa.Pack.Stream
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Bswap
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.Range
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Framework.WriteBytes
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Butterfly
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.HighPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackDispatch
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackLoads
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackVec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWidth
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.KeygenPackWritten
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Residue
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Vec
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Basic
meta import VerifiedGarbage.Proof.MlDsa.Arith.Mem
meta import VerifiedGarbage.Proof.MlDsa.Pack.Arith
meta import VerifiedGarbage.Proof.MlDsa.Pack.Stream
meta import VerifiedGarbage.Proof.MlKem.AArch64.Reduce

/-! ## From `KeygenPackTiming.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Pack
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (agree_of)

theorem simple_ct : ConstantTime isa simpleBitPackK.pre simpleBitPackK.pub simple :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x2,.x3])
    (fun _ _ _ _ ⟨h0,h2,h3,hsp⟩=>agree_of hsp (by simp [h0,h2,h3])) (by taint_decide)

theorem signed_ct : ConstantTime isa bitPackK.pre bitPackK.pub signed :=
  VG.Taint.constantTime (A:=taint) (Taint.ofRegs [.x0,.x3,.x4])
    (fun _ _ _ _ ⟨h0,h3,h4,hsp⟩=>agree_of hsp (by simp [h0,h3,h4])) (by taint_decide)

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end

/-! ## From `KeygenPackVerify.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.KeygenPack
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.AArch64.Pack
open VG.Impl.MlDsa.AArch64.Optimized.KeygenPack
open VG.Proof.MlKem.AArch64 (abi_of)

theorem simple_verified_of_wp
    (hwp : ∀{s:State},simpleBitPackK.pre s → WP isa simple s (fun t=>simpleBitPackK.post s t)) :
    Verified AArch64.target simple (simpleBitPackContract AArch64.abi) := by
  have hcorrect : ∀s,simpleBitPackK.pre s → ∃tr t,Exec isa simple s tr t ∧ abiPreserved s t ∧ simpleBitPackK.post s t := by
    intro s hs
    obtain ⟨tr,t,he,hp⟩ := hwp hs
    exact ⟨tr,t,he,abi_of rfl (by lit_decide) he,hp⟩
  exact Verified.of_correct hcorrect simple_ct
    { pre := by sig_implies_pre [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      post := by sig_implies_post [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      pub := by sig_implies_pub [simpleBitPackContract,simpleBitPackSig,simpleBitPackK,AArch64.abi,AArch64.argRegs]
      sat := VG.Proof.MlDsa.AArch64.Pack.simpleBitPack_verified.2.2 }

theorem signed_verified_of_wp
    (hwp : ∀{s:State},bitPackK.pre s → WP isa signed s (fun t=>bitPackK.post s t)) :
    Verified AArch64.target signed (bitPackContract AArch64.abi) := by
  have hcorrect : ∀s,bitPackK.pre s → ∃tr t,Exec isa signed s tr t ∧ abiPreserved s t ∧ bitPackK.post s t := by
    intro s hs
    obtain ⟨tr,t,he,hp⟩ := hwp hs
    exact ⟨tr,t,he,abi_of rfl (by lit_decide) he,hp⟩
  exact Verified.of_correct hcorrect signed_ct
    { pre := by sig_implies_pre [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      post := by sig_implies_post [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      pub := by sig_implies_pub [bitPackContract,bitPackSig,bitPackK,AArch64.abi,AArch64.argRegs]
      sat := VG.Proof.MlDsa.AArch64.Pack.bitPack_verified.2.2 }

end VG.Proof.MlDsa.AArch64.Optimized.KeygenPack

end
