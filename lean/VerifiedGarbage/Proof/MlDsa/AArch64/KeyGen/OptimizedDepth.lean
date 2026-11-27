module

import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
public import VerifiedGarbage.Impl.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecretCall

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Message
variable (v : Proof.Sha3.AArch64.Permutation)

theorem packSecret_dle (p : Spec.MlDsa.Params) (j : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret (primitives v.callee) p j) := by
  have hb := DLe.of_fd (primitives_ok (keccak := v)).bitPack.fd (primitives_ok (keccak := v)).bitPack.nd
  dle_tac

theorem row_dle {p : Spec.MlDsa.Params}
    (hp : p=Spec.MlDsa.mlDsa44∨p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) (i : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.row (primitives v.callee) p i) := by
  have C := primitives_ok (keccak := v)
  have ha := DLe.of_fd C.add.fd C.add.nd
  have hr := DLe.of_fd C.power2Round.fd C.power2Round.nd
  have hs := DLe.of_fd C.simpleBitPack.fd C.simpleBitPack.nd
  have hb := DLe.of_fd C.bitPack.fd C.bitPack.nd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp with rfl|rfl|rfl <;> exact ⟨by decide +kernel, by lit_decide⟩
  dle_tac

theorem prefix_dle {p : Spec.MlDsa.Params} (hF : PFacts p) :
    DLe 1 (prefixWith v.callee (primitives v.callee) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p) := by
  have C := primitives_ok (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hn := DLe.of_fd C.rejNtt.fd C.rejNtt.nd
  have h4 := DLe.of_fd C.rej4.fd C.rej4.nd
  have h2 := DLe.of_fd two_callee.fd two_callee.nd
  have hb := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_callee 16 v.callee.pairedSha3
    (hF.eta.imp And.left And.left)).fd (VG.Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_callee 16
    v.callee.pairedSha3 (hF.eta.imp And.left And.left)).nd
  unfold prefixWith matrixWith secretsWith
  split <;> split <;> dle_tac

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
