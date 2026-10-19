module
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Correct
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Interface
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.CompiledShapes
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Schedules
@[expose] public section
namespace VG.Proof.MlKem.AArch64.FixedHash
open VG VG.AArch64 VG.Impl.MlKem.AArch64

/-! The fixed hash's shapes are correct for any permutation `v`. -/

theorem kgG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG768_compiled v.callee)

theorem kgH768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,lay768.ekLen⟩] [⟨.x27,2336,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgH768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgH768_compiled v.callee)

theorem prf768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound prf768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (prf768_compiled v.callee)

theorem enH768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,lay768.ekLen⟩] [⟨.x28,KEM.HB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enH768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enH768_compiled v.callee)

theorem enG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG768_compiled v.callee)

theorem deG768_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,2336,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG768_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG768_compiled v.callee)

theorem kgG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 72 6
        [⟨.x25,0,32⟩,⟨.x28,KG.BK,1⟩] [⟨.x28,KG.SB,32⟩,⟨.x28,KG.SG,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgG1024_compiled v.callee)

theorem kgH1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KG.ST KG.WK 136 6
        [⟨.x26,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x27,3104,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound kgH1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (kgH1024_compiled v.callee)

theorem prf1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 0x1f
        [⟨.x28,KEM.RB,33⟩] [⟨.x28,KEM.PB,128⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound prf1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (prf1024_compiled v.callee)

theorem enH1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 136 6
        [⟨.x25,0,Impl.MlKem1024.AArch64.lay1024.ekLen⟩] [⟨.x28,KEM.HB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enH1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enH1024_compiled v.callee)

theorem enG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x28,KEM.HB,32⟩] [⟨.x26,0,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound enG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (enG1024_compiled v.callee)

theorem deG1024_correct (v : Proof.Sha3.AArch64.Permutation) :
 HashCorrect (fixedHash v.callee) .x28 KEM.ST KEM.WK 72 6
        [⟨.x28,KEM.MB,32⟩,⟨.x25,3104,32⟩] [⟨.x28,KEM.KP,32⟩,⟨.x28,KEM.RB,32⟩] := by
 intro s hs _ _ hi ho hp
 apply code_ok v hs (by decide) (by decide) (by decide) hi
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (certified_sound deG1024_schedule) ho hp
   (by intro p h; simp at h; first | (subst p; decide) | (rcases h with rfl|rfl <;> decide))
   (by decide) (deG1024_compiled v.callee)

end VG.Proof.MlKem.AArch64.FixedHash
