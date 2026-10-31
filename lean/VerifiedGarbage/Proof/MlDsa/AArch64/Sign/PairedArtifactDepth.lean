module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Depth
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedChecks
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedRest
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.Inv
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedDepth

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Message
open VG VG.AArch64

theorem earlySeq_dle {f : Nat→Prog isa} (h:∀k,DLe 1 (f k)) :
    ∀n a,DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.seqOk f a n)
  |0,_=>DLe.block []
  |n+1,a=>DLe.seq (h a) (DLe.ite (earlySeq_dle h n (a+1)) (DLe.block []))

theorem pairedChecks_dle (p : Spec.MlDsa.Params) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p) := by
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt := ⟨by decide +kernel⟩
  have hm : DLe 1 (Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true) := ⟨by decide +kernel⟩
  have hz : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.addNorm := ⟨by decide +kernel⟩
  have hl : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.subLowNorm := ⟨by decide +kernel⟩
  have pz : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .z) := ⟨by decide +kernel⟩
  have pr : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .r0) := ⟨by decide +kernel⟩
  have ph : DLe 1 (Impl.MlDsa.AArch64.Optimized.Paired.selected .h) := ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks
  dle_tac
  · apply earlySeq_dle
    intro r
    unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
    dle_tac
  · apply earlySeq_dle
    intro r
    unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
    dle_tac

theorem pairedSignWith_dle (v : Proof.Sha3.AArch64.Permutation)
    {p : Spec.MlDsa.Params} (hp3 : Sign.Ok3 p) :
    DLe 1 (Impl.MlDsa.AArch64.Sign.Optimized.signWith v.callee (Sign.primsWith v.callee) p
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedChecks p)) := by
  have C := Sign.prims_okWith (keccak:=v)
  have hinit := pairedInitialization_dle v p
  have hcommit := pairedCommit_dle v hp3
  have hb := pairedBall_dle v p
  have hc := pairedChecks_dle p
  have hr := DLe.of_fd C.rejNTT.fd
  have hr4 := DLe.of_fd C.rej4.fd
  have hbp := DLe.of_fd C.bitPack.fd
  have hhp := DLe.of_fd C.hintBitPack.fd
  have hn : DLe 1 Impl.MlDsa.AArch64.Optimized.Response.canonicalize := ⟨by decide +kernel⟩
  unfold Impl.MlDsa.AArch64.Sign.Optimized.signWith
  dle_tac

end VG.Proof.MlDsa.AArch64.Message
