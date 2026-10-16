module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Compiled
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Timing
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64
deriving instance DecidableEq for Code

theorem kgG768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem kgH768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem prf768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem enH768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem enG768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem deG768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem deJ768_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,2368,32⟩,⟨.x26,0,lay768.ctLen⟩] [⟨.x28,KEM.JB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,2368,32⟩,⟨.x26,0,lay768.ctLen⟩] [⟨.x28,KEM.JB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem kgG1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem kgH1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem prf1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem enH1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem enG1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem deG1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel

theorem deJ1024_compiled : Fusion.Same
 (compiled Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,3136,32⟩,⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ctLen⟩] [⟨.x28,KEM.JB,32⟩])
 (Impl.MlKem.AArch64.FixedHash.code Sha3.AArch64.Sha3.callee .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x25,3136,32⟩,⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ctLen⟩] [⟨.x28,KEM.JB,32⟩]) := by
 apply Fusion.of_normalize_eq
 decide +kernel
end VG.Proof.MlKem.AArch64.FixedHash
