import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPrims
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedSecrets
import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.KeyGen.Optimized
open VG.Proof.MlDsa.AArch64.Message
variable (v : Proof.Sha3.AArch64.Permutation)

theorem packSecret_dle (p : Spec.MlDsa.Params) (j : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret (primitives v.callee) p j) := by
  have hb := DLe.of_fd (primitives_ok (keccak := v)).bitPack.fd
  dle_tac

theorem row_dle {p : Spec.MlDsa.Params}
    (hp : p=Spec.MlDsa.mlDsa44∨p=Spec.MlDsa.mlDsa65∨p=Spec.MlDsa.mlDsa87) (i : Nat) :
    DLe 1 (Impl.MlDsa.AArch64.KeyGen.Optimized.row (primitives v.callee) p i) := by
  have C := primitives_ok (keccak := v)
  have ha := DLe.of_fd C.add.fd
  have hr := DLe.of_fd C.power2Round.fd
  have hs := DLe.of_fd C.simpleBitPack.fd
  have hb := DLe.of_fd C.bitPack.fd
  have hd : DLe 1 (Impl.MlDsa.AArch64.Optimized.DotInverse.staticCode p.ℓ) := by
    rcases hp with rfl|rfl|rfl <;> exact ⟨by decide +kernel⟩
  dle_tac

theorem prefix_dle {p : Spec.MlDsa.Params} (hF : PFacts p) :
    DLe 1 (prefixWith v.callee (primitives v.callee) Impl.MlDsa.AArch64.Optimized.ResidentRej.Two.code p) := by
  have C := primitives_ok (keccak := v)
  obtain ⟨ha,hp,hs⟩ := keccak_dle v
  have hn := DLe.of_fd C.rejNtt.fd
  have h4 := DLe.of_fd C.rej4.fd
  have h2 := DLe.of_fd two_callee.fd
  have hb := DLe.of_fd (VG.Proof.MlDsa.AArch64.Optimized.BoundedFour.sampler_callee 16 v.callee.pairedSha3
    (hF.eta.imp And.left And.left)).fd
  unfold prefixWith matrixWith secretsWith
  split <;> split <;> dle_tac

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
