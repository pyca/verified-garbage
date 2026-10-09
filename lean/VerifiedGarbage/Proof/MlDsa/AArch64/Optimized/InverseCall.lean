import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.InverseVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.Inverse

theorem inverse_callee (S : Nat) :
    CalleeOk S staticCode (montgomeryNttInvContract (abi.withConsts inverseConsts)) := by
  refine ⟨inverse_verified.1,inverse_verified.2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

abbrev inverseArgs (f scratch : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr f),(.x1,.ptr scratch)]

structure InverseCallReady (f scratch : Ptr) (s : State) : Prop where
  fit : (pa s f).toNat+1024≤2^64
  scratchFit : (pa s scratch).toNat+1024≤2^64
  held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=
    expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64
  tableApart : ∀ r∈[outputRegion (pa s f),outputRegion (pa s scratch)],
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r
  apart : (outputRegion (pa s f)).Disjoint (outputRegion (pa s scratch))
  reduced : Reduced s.mem (pa s f)
  readable : Covers ([tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]++
    [outputRegion (pa s f),outputRegion (pa s scratch)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s f),outputRegion (pa s scratch)] s.wr

theorem inverseAt_pre {s s1 : State} {f scratch : Ptr}
    (h : InverseCallReady f scratch s) (h1 : Args (inverseArgs f scratch) s s1)
    (hy : s1.syms=s.syms) :
    (montgomeryNttInvContract (abi.withConsts inverseConsts)).pre
      (s1.callEntry.withRegions [tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
        [outputRegion (pa s f),outputRegion (pa s scratch)]) := by
  apply inverse_spec_pre
  · simp [State.withRegions,State.callEntry,hy,tableRegion]
  · simp [State.withRegions,State.callEntry,Args.r0 h1,Args.r1 h1,Arg.val,outputRegion]
  · simpa [State.withRegions,State.callEntry,hy,Args.mem h1] using h.held
  · simpa [State.withRegions,State.callEntry,hy] using h.tableFit
  · simpa [State.withRegions,State.callEntry,hy,tableRegion] using h.tableApart
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Args.r1 h1,Arg.val,outputRegion] using h.apart
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Arg.val] using h.fit
  · simpa [State.withRegions,State.callEntry,Args.r1 h1,Arg.val] using h.scratchFit
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Args.mem h1,Arg.val] using h.reduced

theorem inverseArgs_ok {f scratch : Ptr} (hf : (Arg.ptr f).Ok) (hs : (Arg.ptr scratch).Ok) :
    ∀ a∈inverseArgs f scratch,a.2.Ok ∧ a.1∈argRegs := by
  simp only [inverseArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl | rfl
  · exact ⟨hf,by simp⟩
  · exact ⟨hs,by simp⟩

theorem inverseAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f scratch : Ptr}
    (hf : (Arg.ptr f).Ok) (hs : (Arg.ptr scratch).Ok) (h : InverseCallReady f scratch s) :
    WP isa (callAt nm staticCode (inverseArgs f scratch)) s fun t =>
      Post S s t [outputRegion (pa s f),outputRegion (pa s scratch)] ∧
      PolyIs t.mem (pa s f) (montgomeryNttInv (polyAt s.mem (pa s f))) := by
  refine WP.mono (callAtSyms_ok hS (inverse_callee S) (inverseArgs_ok hf hs) (by simp)
    (fun s1 h1 hy => inverseAt_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at hq
  rw [Args.r0 h1,Args.mem h1] at hq
  exact hq

/-- Coefficient values remain secret; only pointers, stack, and table address
are needed to relate the two call traces. -/
theorem inverseAt_tr {S : Nat} {nm : String} {f scratch : Ptr}
    (hf : (Arg.ptr f).Ok) (hs : (Arg.ptr scratch).Ok) {Q : State → State → Prop}
    (hQ : ∀ x y,Q x y → InverseCallReady f scratch x ∧ InverseCallReady f scratch y ∧
      pa x f=pa y f ∧ pa x scratch=pa y scratch ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (callAt nm staticCode (inverseArgs f scratch)) fun _ _ => True := by
  refine callAtSyms_tr (inverse_callee S) (inverseArgs_ok hf hs) (by simp)
    fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ef,es,esp,et⟩ := hQ x y hp
  refine ⟨[tableRegion (x.syms "VG_MLDSA_INV_FOLDED")],
    [outputRegion (pa x f),outputRegion (pa x scratch)],inverseAt_pre rx h1 hy1,
    ?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ef,es,et]
    exact inverseAt_pre ry h2 hy2
  · sig_pub [montgomeryNttInvContract,inPlaceContract,inPlaceSig,abi,argRegs,Abi.withConsts,inverseConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ef,es⟩
  · rw [ef,es,et]; exact ry.readable
  · rw [ef,es]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
