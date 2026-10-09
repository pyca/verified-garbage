import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedLowDecompose

namespace VG.Proof.MlDsa.AArch64.Optimized.Paired
open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (VChg wp_strq)
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def lowStoreMls (a t h : VReg) (off : Nat) : List Instr :=
 ([.strq h .x15 off] : List Instr) ++ lowMls a t h

/-- Preserve the measured high-store-before-low-reduction schedule. -/
theorem lowStoreMls_ok {a t h : VReg} {off : Nat}
    (hat : a≠t) (haq : a≠.v31) (hac : a≠.v8) (htq : t≠.v31)
    (hpres : ∀r∈preservedV,r∉[a,t])
    {s : State} {rest : List Instr} {Q : State → Prop}
    (ho : off%16=0 ∧ off<65536)
    (hr : InRegions s.wr (s.gpr .x15+BitVec.ofNat 64 off) 16)
    (hq : ∀e<4,vword (s.v .v31) e=8380417#32)
    (hc : ∀e<4,vword (s.v .v8) e=4194304#32)
    (k : ∀u,StepKeep [a,t] s u →
      u.mem=s.mem.write (s.gpr .x15+BitVec.ofNat 64 off) 16 (s.v h) →
      (∀e<4,vword (u.v a) e=Response.reduceWord
        (vword (s.v a) e-vword (s.v h) e*vword (s.v .v15) e)) →
      WP isa (.block rest) u Q) :
    WP isa (.block (lowStoreMls a t h off++rest)) s Q := by
  simp only [lowStoreMls,List.cons_append,List.nil_append]
  refine wp_strq ho rfl hr fun u hu => ?_
  refine lowMls_ok hat haq hac htq
    (by simpa only [hu.v] using hq) (by simpa only [hu.v] using hc)
    fun v hv hw => k v ?_ (hv.mem.trans hu.mem) ?_
  · exact ((StepKeep.ofMem hu).trans (StepKeep.ofChg hv hpres)).mono (by simp)
  · simpa only [hu.v] using hw

/-- The complete lane consists of the input, high extraction, high store and low reduction,
then the low store and norm test; this is instruction-list equality, not a rescheduling. -/
theorem r0Lane_blocks (g : Nat) (raw a t h other : VReg) (off : Nat) :
    VG.Impl.MlDsa.AArch64.Optimized.Paired.r0Lane g raw a t h other off =
      lowInput raw a t other off ++ lowHb g h a t ++
      lowStoreMls a t h off ++ lowStoreNorm a t off := by
  rw [r0Lane_partition]
  simp only [lowInput,lowStoreMls,lowStoreNorm,lowMls,List.append_assoc,
    List.cons_append,List.nil_append]
end VG.Proof.MlDsa.AArch64.Optimized.Paired
