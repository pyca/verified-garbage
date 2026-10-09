import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.LazyInv
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseCall

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

/-- The inverse uses the existing two-buffer layout check. Its static table
conditions are explicit, including separation from the scratch argument. -/
theorem inverseReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {f scratch : Ptr} (hc : ipChk rbs wbs f scratch=true)
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=
      VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈[Inverse.outputRegion (pa s f),Inverse.outputRegion (pa s scratch)],
      (Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r)
    (ht : Covers [Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] (s.rd++s.wr))
    (hf : Reduced s.mem (pa s f)) : Inverse.InverseCallReady f scratch s := by
  have hcov := ip_cov L hc
  simp only [ipChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨hsepbuf,hfread⟩,hsread⟩,_⟩,_⟩ := hc
  exact ⟨L.nwp hfread,L.nwp hsread,held,hfit,hsep,L.disj hsepbuf,hf,
    Covers.cons ht hcov.1,hcov.2⟩

theorem inverseAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {f scratch : Ptr}
    (hf : inB (rbs++wbs) f 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.InverseCallReady f scratch s) :
    WP isa (callAt "vg_mldsa_montgomery_inv_ntt"
      VG.Impl.MlDsa.AArch64.Optimized.Inverse.staticCode (Inverse.inverseArgs f scratch)) s fun t =>
      PPostB S s t [(f,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      PolyIs t.mem (pa s f) (montgomeryNttInv (polyAt s.mem (pa s f))) := by
  refine WP.mono (Inverse.inverseAt_ok L.s64 (ptr_ok (L.ptrBs hf)) (ptr_ok (L.ptrBs hs)) h)
    fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

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
