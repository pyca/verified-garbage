module

public import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
public import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
public import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
meta import VerifiedGarbage.Impl.MlKem.AArch64.FixedHash
meta import VerifiedGarbage.Impl.MlKem.AArch64.Decaps
meta import VerifiedGarbage.Impl.MlKem1024.AArch64.Decaps
meta import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Backend
import all Init.Data.Array.Basic
import all Init.Data.Array.DecidableEq
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.Vector.Basic

/-! # Public-address checks for every fixed hash shape used by optimized ML-KEM -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
abbrev hashRegs : List Reg := [.x25,.x26,.x27,.x28]

theorem kgG768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem kgH768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem prf768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem enH768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem enG768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem deG768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem deJ768_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,2368,32⟩,⟨.x26,0,lay768.ctLen⟩] [⟨.x28,KEM.JB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem kgG1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem kgH1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem prf1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem enH1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem enG1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem deG1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

theorem deJ1024_taint :
    ∃h,(VectorTaint.taint.check (VectorTaint.ofRegs hashRegs)
      (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,3136,32⟩,⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ctLen⟩] [⟨.x28,KEM.JB,32⟩]) h).isSome=true := ⟨_,by taint_decide⟩

end VG.Proof.MlKem.AArch64.FixedHash
