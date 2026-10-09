import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCalls
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductCallTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Proof.MlDsa.AArch64.Optimized

/-- The response-product call uses two positive NTT inputs and writes only
its result and the existing scratch slot. Static roots stay explicit. -/
theorem productReady_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (hwo : inB wbs out 1024=true) (hws : inB wbs scratch 1024=true)
    (hoa : sepB rbs wbs out 1024 a 1024=true)
    (hob : sepB rbs wbs out 1024 b 1024=true)
    (hos : sepB rbs wbs out 1024 scratch 1024=true)
    (has : sepB rbs wbs a 1024 scratch 1024=true)
    (hbs : sepB rbs wbs b 1024 scratch 1024=true)
    (held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=
      VG.Impl.MlDsa.AArch64.Optimized.Inverse.expandedWords.getD i 0)
    (hfit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64)
    (hsep : ∀ r∈[Inverse.outputRegion (pa s out),Inverse.outputRegion (pa s scratch)],
      (Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r)
    (ht : Covers [Inverse.tableRegion (s.syms "VG_MLDSA_INV_FOLDED")] (s.rd++s.wr))
    (hpa : PositiveReduced s.mem (pa s a)) (hpb : PositiveReduced s.mem (pa s b)) :
    Inverse.ProductCallReady out a b scratch s := by
  refine ⟨L.nwp ho,L.nwp ha,L.nwp hb,L.nwp hs,held,hfit,hsep,
    L.disj hoa,L.disj hob,L.disj hos,L.disj has,L.disj hbs,hpa,hpb,?_,?_⟩
  · exact Covers.cons (L.cR ha) (Covers.cons (L.cR hb)
      (Covers.cons ht (Covers.cons (L.cR ho) (L.cR hs))))
  · exact Covers.cons (L.cW hwo) (L.cW hws)

/-- Fused challenge multiplication and inverse transform for z/r0/h. The
signed result is intentionally not coerced to the canonical PolyIs contract. -/
theorem productAt_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b)))) := by
  refine WP.mono (Inverse.productAt_ok L.s64 (ptr_ok (L.ptrBs ho)) (ptr_ok (L.ptrBs ha))
    (ptr_ok (L.ptrBs hb)) (ptr_ok (L.ptrBs hs)) h) fun t ⟨hp,hv⟩ => ?_
  exact ⟨hp.b,hp.cs .x24 (by decide) (by decide),hv⟩

/-- Field-valued response boundary for a transformed challenge and secret. -/
theorem productAt_field_layout {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {out a b scratch : Ptr} {f g : Poly}
    (ho : inB (rbs++wbs) out 1024=true) (ha : inB (rbs++wbs) a 1024=true)
    (hb : inB (rbs++wbs) b 1024=true) (hs : inB (rbs++wbs) scratch 1024=true)
    (h : Inverse.ProductCallReady out a b scratch s)
    (hf : PosPolyIs s.mem (pa s a) f) (hg : PosPolyIs s.mem (pa s b) g) :
    WP isa (callAt "vg_mldsa_multiply_inverse_raw"
      (VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse.staticCode true)
      (Inverse.productArgs out a b scratch)) s fun t =>
      PPostB S s t [(out,1024),(scratch,1024)] ∧ t.gpr .x24=s.gpr .x24 ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT f g)) := by
  refine WP.mono (productAt_layout L ho ha hb hs h) fun t ⟨hp,h24,hv⟩ => ?_
  exact ⟨hp,h24,by simpa only [hf.value,hg.value] using hv⟩

end VG.Proof.MlDsa.AArch64.Sign
