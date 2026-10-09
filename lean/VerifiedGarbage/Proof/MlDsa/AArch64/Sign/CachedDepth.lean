import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedArtifactDepth
import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.CachedLoop

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem cachedCommit_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.commit (Sign.primsWith v.callee) p) := by
  have C := Sign.prims_okWith (keccak := v)
  have hm := DLe.of_fd C.expandMask.fd
  have hm2 := DLe.of_fd C.expandMaskPair.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.outNtt := ⟨by decide +kernel⟩
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel⟩
  have hh : DLe 1 ((Sign.primsWith v.callee).highPack p.γ₂) := by
    dsimp only [Sign.primsWith,Impl.MlDsa.AArch64.Optimized.HighPack.code]
    dle_tac
  have hc : DLe 1 (Impl.MlDsa.AArch64.Sign.CommitTail.code (p.k*Impl.MlDsa.AArch64.Sign.w1Len p)
      (Impl.MlDsa.AArch64.Sign.cLen p)) := by
    rcases hp3 with rfl|rfl <;> exact ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.commit
  dle_tac

theorem cachedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87)
    {checks : Prog isa} (hchecks : DLe 1 checks) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p checks) := by
  have C := Sign.prims_okWith (keccak := v)
  have hc := cachedCommit_dle v hp3
  have hi := pairedInitialization_dle v p
  have hb := pairedBall_dle v p
  have hr := DLe.of_fd C.rejNTT.fd
  have hr4 := DLe.of_fd C.rej4.fd
  have hrtwo : DLe 1 Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code := ⟨by decide +kernel⟩
  have hp := DLe.of_fd C.bitPack.fd
  have hh := DLe.of_fd C.hintBitPack.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize := ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Cached.signWith
  unfold Impl.MlDsa.AArch64.Sign.CachedMatrix.expandA
  split <;> dle_tac

theorem cachedPairedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp : p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Cached.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) :=
  cachedSignWith_dle v hp (pairedChecks_dle p)

end VG.Proof.MlDsa.AArch64.Message
