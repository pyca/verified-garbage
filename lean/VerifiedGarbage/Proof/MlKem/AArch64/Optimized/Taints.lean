module

public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
public import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
meta import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.VectorSymbols
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
meta import VerifiedGarbage.Impl.MlKem.AArch64.Optimized
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Framework.AArch64.Lit
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
import VerifiedGarbage.Proof.Framework.AddrArith
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
import VerifiedGarbage.TCB.Axioms
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Ball
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejBounded
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.RejNtt
meta import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
meta import VerifiedGarbage.Proof.Framework.AArch64.Call
meta import VerifiedGarbage.Proof.Framework.AArch64.Exec
meta import VerifiedGarbage.Proof.Framework.AArch64.Lit
meta import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
meta import VerifiedGarbage.Proof.Framework.AArch64.VectorCaller
meta import VerifiedGarbage.Proof.Framework.AddrArith
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Load
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Round
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Rounds
meta import VerifiedGarbage.TCB.Axioms

/-! # Public-address checks for the optimized code surrounding matrix generation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Callers

theorem deStart768_taint :
    ∃h,((VectorSymbols.analysis ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM_INTT16_ZETAS"]).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee lay768) h).isSome=true := by
  exact ⟨_, by taint_decide⟩

theorem deStart1024_taint :
    ∃h,((VectorSymbols.analysis ["VG_MLKEM_GAMMA","VG_MLKEM_NTT16_ZETAS","VG_MLKEM_INTT16_ZETAS"]).check (VectorTaint.ofRegs [.x0,.x1,.x2,.x3])
      (Impl.MlKem.AArch64.Optimized.deStart Sha3.AArch64.Sha3.callee Impl.MlKem1024.AArch64.lay1024) h).isSome=true := by
  exact ⟨_, by taint_decide⟩

end VG.Proof.MlKem.AArch64.Optimized
