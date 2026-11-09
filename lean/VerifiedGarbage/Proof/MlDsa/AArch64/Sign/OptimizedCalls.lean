module

public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Arith
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.Representation
public import VerifiedGarbage.Proof.MlDsa.MontgomeryContract
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseStaticCore
public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.InverseTable
public import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Call
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry

@[expose] public section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- Static roots are readable independently of the register-based data layout.
The caller must establish their contents and separation from writable slots. -/
structure ForwardRoots (s : State) (p : Addr) : Prop extends NttTableAt s p where
  readable : Covers [expandedRegion
    (s.syms "VG_MLDSA_NTT_EXPANDED")] (s.rd++s.wr)

/-- Bridge the positive NTT into the signing layout while retaining the
ordinary frame invariant used to preserve all other polynomial slots. -/
theorem positiveNttAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {f : Ptr}
    (hr : inB (rbs++wbs) f 1024=true) (hw : inB wbs f 1024=true)
    (ht : ForwardRoots s (pa s f)) (hf : Reduced s.mem (pa s f)) :
    WP isa (callAt "vg_mldsa_ntt_positive" VG.Impl.MlDsa.AArch64.Optimized.Ntt.staticNtt
      (positiveNttArgs f)) s fun t =>
      PPostB S s t [(f,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      PosPolyIs t.mem (pa s f) (ntt (polyAt s.mem (pa s f))) := by
  refine WP.mono (positiveNttAt_ok L.s64 (ptr_ok (L.ptrBs hr)) (L.nwp hr)
    ht.toNttTableAt hf (Covers.cons ht.readable (L.cR hr)) (L.cW hw))
    fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),⟨hv.1,hv.2⟩⟩

/-- Transform directly from the sampled mask into its NTT slot, eliminating
an otherwise redundant 1024-byte copy. The source remains canonical. -/
theorem positiveNttOutAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out f : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (hf : inB (rbs++wbs) f 1024=true)
    (hw : inB wbs out 1024=true) (hsep : sepB rbs wbs out 1024 f 1024=true)
    (ht : ForwardRoots s (pa s out)) (hr : Reduced s.mem (pa s f)) :
    WP isa (callAt "vg_mldsa_ntt_positive_from" VG.Impl.MlDsa.AArch64.Optimized.Ntt.outNtt
      (positiveNttOutArgs out f)) s fun t =>
      PPostB S s t [(out,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      PosPolyIs t.mem (pa s out) (ntt (polyAt s.mem (pa s f))) := by
  refine WP.mono (positiveNttOutAt_ok L.s64 (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs hf))
    (L.nwp ho) (L.nwp hf) ht.toNttTableAt hr (L.disj hsep)
    (Covers.cons (L.cR hf) (Covers.cons ht.readable (L.cR ho))) (L.cW hw))
    fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),⟨hv.1,hv.2⟩⟩

end VG.Proof.MlDsa.AArch64.Sign
