import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

/-- Internal call contract for the same verified kernel. Its execution never
accesses the unused scratch argument of the separately emitted public helper. -/
theorem inverseSingle_callee (S : Nat) : CalleeOk S staticCode inverseK :=
  ⟨inverse_correct,inverse_ct,Nat.zero_le _⟩

abbrev inverseSingleArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]

structure InverseSingleReady (f : Ptr) (s : State) : Prop where
  held : InverseTable.Artifact s.mem (s.syms "VG_MLDSA_INV_FOLDED")
  apart : (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (pa s f))
  reduced : Reduced s.mem (pa s f)
  readable : Covers [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] (s.rd++s.wr)
  writable : Covers [outputRegion (pa s f)] s.wr

theorem inverseSingle_pre {s s1 : State} {f : Ptr}
    (h : InverseSingleReady f s) (h1 : Args (inverseSingleArgs f) s s1)
    (hy : s1.syms=s.syms) :
    inverseK.pre (s1.callEntry.withRegions [tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
      [outputRegion (pa s f)]) := by
  change tableRegion (s1.syms "VG_MLDSA_INV_FOLDED") ∈
      [tableRegion (s.syms "VG_MLDSA_INV_FOLDED"),outputRegion (pa s f)] ∧
    outputRegion (s1.callEntry.gpr .x0) ∈ [outputRegion (pa s f)] ∧
    (tableRegion (s1.syms "VG_MLDSA_INV_FOLDED")).Disjoint (outputRegion (s1.callEntry.gpr .x0)) ∧
    InverseTable.Artifact s1.mem (s1.syms "VG_MLDSA_INV_FOLDED") ∧
    Reduced s1.mem (s1.callEntry.gpr .x0)
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1,hy]
  exact ⟨by simp,by exact List.mem_singleton.mpr rfl,h.apart,h.held,h.reduced⟩

theorem inverseSingleArgs_ok {f : Ptr} (hf : (Arg.ptr f).Ok) :
    ∀x∈inverseSingleArgs f,x.2.Ok ∧ x.1∈argRegs := by
  intro x hx
  have he : x=(.x0,.ptr f) := by simpa only [inverseSingleArgs,List.mem_singleton] using hx
  subst x
  exact ⟨hf,by simp⟩

theorem inverseSingleAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hf : (Arg.ptr f).Ok) (h : InverseSingleReady f s) :
    WP isa (callAt nm staticCode (inverseSingleArgs f)) s fun t =>
      Post S s t [outputRegion (pa s f)] ∧
      PolyIs t.mem (pa s f) (montgomeryNttInv (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAtSyms_ok hS (inverseSingle_callee S) (inverseSingleArgs_ok hf) (by simp)
    (fun s1 h1 hy=>inverseSingle_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  change PolyIs t.mem (s1.callEntry.gpr .x0)
    (montgomeryNttInv (polyAt s1.mem (s1.callEntry.gpr .x0))) at hq
  rw [show s1.callEntry.gpr .x0=s1.gpr .x0 from rfl,Args.r0 h1,Args.mem h1] at hq
  exact hq
end VG.Proof.MlDsa.AArch64.Optimized.Inverse
