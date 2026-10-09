import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowInput
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_vop wp_strq vword_mapWords3)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

/-- Subtract the decomposed high part and reduce, using the selected schedule. -/
def lowMls (a t h : VReg) : List Instr :=
 ([.vop (.mls a h .v15)] : List Instr) ++ reduceRegs a t

theorem lowMls_ok {a t h : VReg} (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    {s : State} {rest : List Instr} {Q : State → Prop}
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,VChg [a,t] s u →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) → WP isa (.block rest) u Q) :
    WP isa (.block (lowMls a t h++rest)) s Q := by
  simp only [lowMls,List.cons_append,List.nil_append]
  refine wp_vop (d := a) rfl fun u hu => ?_
  refine reduceRegs_ok hat htq
    (by intro e he; rw [hu.get .v31 (Ne.symm haq)]; exact hq e he)
    (by intro e he; rw [hu.get .v8 (Ne.symm hac)]; exact hc e he)
    fun v hv hw => k v ((hu.chg.trans hv).mono (by
      intro r hr; simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at *; grind only)) ?_
  intro e he
  rw [hw e he,hu.v,vword_mapWords3 _ _ _ _ he]

/-- Store the exact reduced low vector and accumulate its norm mask. -/
def lowStoreNorm (a t : VReg) (off : Nat) : List Instr :=
 ([.strq a .x16 off] : List Instr) ++ normRegs a t

theorem lowStoreNorm_ok {a t : VReg} {off : Nat} (htw : t≠.v10) (htf : t≠.v30)
    (hpres : ∀r∈preservedV,r∉[t,.v30])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x16+BitVec.ofNat 64 off) 16)
    (k : ∀u,StepKeep [t,.v30] s u →
      u.mem=s.mem.write (s.gpr .x16+BitVec.ofNat 64 off) 16 (s.v a) →
      (∀e<4,vword (u.v .v30) e=vword (s.v .v30) e |||
        Response.normMask (vword (s.v a) e) (vword (s.v .v9) e) (vword (s.v .v10) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreNorm a t off++rest)) s Q := by
  simp only [lowStoreNorm,List.cons_append,List.nil_append]
  refine wp_strq ho rfl hr fun u hu => normRegs_ok htw htf fun v hv hf => k v ?_ ?_ ?_
  · exact ((StepKeep.ofMem hu).trans (StepKeep.ofChg hv hpres)).mono (by simp)
  · exact hv.mem.trans hu.mem
  · simpa only [hu.v] using hf
end VG.Proof.MlDsa.AArch64.Optimized.Paired
