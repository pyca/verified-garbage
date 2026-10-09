import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallee
import VerifiedGarbage.Proof.Framework.AArch64.Syms

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt glue)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

/-- Calls through immutable-table contracts also retain the symbol map while
moving their arguments. `Args` alone intentionally does not record that map. -/
theorem callAtSyms_ok {S : Nat} (hS : S<2^64) {nm : String} {cd : Prog isa} {k : Contract isa}
    (C : CalleeOk S cd k) {as : List (Reg × Arg)}
    (hok : ∀ a∈as,a.2.Ok ∧ a.1∈argRegs) (hnd : (as.map (·.1)).Nodup)
    {s : State} {rd wr : List Region}
    (hpre : ∀ s1,Args as s s1 → s1.syms=s.syms → k.pre (s1.callEntry.withRegions rd wr))
    (hc : Covers (rd++wr) (s.rd++s.wr)) (hw : Covers wr s.wr) :
    WP isa (callAt nm cd as) s fun t => Post S s t wr ∧
      ∃ s1,Args as s s1 ∧ k.post (s1.callEntry.withRegions rd wr) (t.withRegions rd wr) := by
  refine WP.seq (WP.mono_syms (glue_ok hok hnd s) fun s1 h1 hy => ?_)
  have k1 := h1.2
  refine WP.callFV C.correct (hpre s1 h1 hy) (by rw [k1.rd,k1.wr]; exact hc)
    (by rw [k1.wr]; exact hw)
    (fun t hrd hwr hsp hf hcs hvcs hpost => ?_) (by have := C.fd; omega)
  refine ⟨⟨hrd.trans k1.rd,hwr.trans k1.wr,hsp.trans k1.sp,
    fun r hr h30 => by rw [hcs r hr h30,k1.gpr r (argRegs_pres r hr)],?_,
    fun r hr => (hvcs r hr).trans (k1.vcs r hr)⟩,s1,h1,hpost⟩
  rw [h1.1.2,k1.sp] at hf
  exact Frame.below_mono hf C.fd hS

/-- Public immutable-table conditions, separate from the coefficient value. -/
structure NttTableAt (s : State) (p : Addr) : Prop where
  held : ∀ i<488,s.mem.readW (s.syms "VG_MLDSA_NTT_EXPANDED"+BitVec.ofNat 64 (8*i)) 64=
    staticNttWords.getD i 0
  fit : (s.syms "VG_MLDSA_NTT_EXPANDED").toNat+3904≤2^64
  apart : (expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")).Disjoint (outputRegion p)

abbrev positiveNttArgs (f : Ptr) : List (Reg × Arg) := [(.x0,.ptr f)]
abbrev positiveNttOutArgs (out f : Ptr) : List (Reg × Arg) := [(.x0,.ptr out),(.x1,.ptr f)]

theorem positiveNttAt_pre {s s1 : State} {f : Ptr}
    (hfit : (pa s f).toNat+1024≤2^64) (ht : NttTableAt s (pa s f))
    (hf : Reduced s.mem (pa s f)) (h1 : Args (positiveNttArgs f) s s1)
    (hy : s1.syms=s.syms) :
    (positiveNttContract (abi.withConsts nttConsts)).pre
      (s1.callEntry.withRegions [expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]
        [outputRegion (pa s f)]) := by
  apply positiveNtt_spec_pre
  · simp [State.withRegions,State.callEntry,hy]
  · simp [State.withRegions,State.callEntry,Args.r0 h1,Arg.val]
  · simpa [State.withRegions,State.callEntry,hy,Args.mem h1] using ht.held
  · simpa [State.withRegions,State.callEntry,hy] using ht.fit
  · simpa [State.withRegions,State.callEntry,hy,Args.r0 h1,Arg.val] using ht.apart
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Arg.val] using hfit
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Args.mem h1,Arg.val] using hf

theorem positiveNttAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {f : Ptr}
    (hfok : (Arg.ptr f).Ok) (hfit : (pa s f).toNat+1024≤2^64)
    (ht : NttTableAt s (pa s f)) (hf : Reduced s.mem (pa s f))
    (hc : Covers ([expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]++[outputRegion (pa s f)])
      (s.rd++s.wr)) (hw : Covers [outputRegion (pa s f)] s.wr) :
    WP isa (callAt nm staticNtt (positiveNttArgs f)) s fun t =>
      Post S s t [outputRegion (pa s f)] ∧
      PositivePolyIs t.mem (pa s f) (ntt (polyAt s.mem (pa s f))) := by
  have hok : ∀ a∈positiveNttArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [positiveNttArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine WP.mono (callAtSyms_ok hS (positiveNtt_callee S) hok (by simp)
    (fun s1 h1 hy => ?_) hc hw) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  · exact positiveNttAt_pre hfit ht hf h1 hy
  · sig_post [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at hq
    rw [Args.r0 h1,Args.mem h1] at hq
    exact hq


theorem positiveNttOutAt_pre {s s1 : State} {out f : Ptr}
    (hofit : (pa s out).toNat+1024≤2^64) (hfit : (pa s f).toNat+1024≤2^64)
    (ht : NttTableAt s (pa s out)) (hf : Reduced s.mem (pa s f))
    (hio : (outputRegion (pa s out)).Disjoint (outputRegion (pa s f)))
    (h1 : Args (positiveNttOutArgs out f) s s1) (hy : s1.syms=s.syms) :
    (positiveNttOutContract (abi.withConsts nttConsts)).pre
      (s1.callEntry.withRegions [outputRegion (pa s f),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]
        [outputRegion (pa s out)]) := by
  apply positiveNttOut_spec_pre
  · simp [State.withRegions,State.callEntry,hy,Args.r1 h1,Arg.val]
  · simp [State.withRegions,State.callEntry,Args.r0 h1,Arg.val]
  · simpa [State.withRegions,State.callEntry,hy,Args.mem h1] using ht.held
  · simpa [State.withRegions,State.callEntry,hy] using ht.fit
  · simpa [State.withRegions,State.callEntry,hy,Args.r0 h1,Arg.val] using ht.apart
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Args.r1 h1,Arg.val] using hio
  · simpa [State.withRegions,State.callEntry,Args.r0 h1,Arg.val] using hofit
  · simpa [State.withRegions,State.callEntry,Args.r1 h1,Arg.val] using hfit
  · simpa [State.withRegions,State.callEntry,Args.r1 h1,Args.mem h1,Arg.val] using hf

theorem positiveNttOutAt_ok {S : Nat} (hS : S<2^64) {nm : String} {s : State} {out f : Ptr}
    (hook : (Arg.ptr out).Ok) (hfok : (Arg.ptr f).Ok)
    (hofit : (pa s out).toNat+1024≤2^64) (hfit : (pa s f).toNat+1024≤2^64)
    (ht : NttTableAt s (pa s out)) (hf : Reduced s.mem (pa s f))
    (hio : (outputRegion (pa s out)).Disjoint (outputRegion (pa s f)))
    (hc : Covers ([outputRegion (pa s f),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]++
      [outputRegion (pa s out)]) (s.rd++s.wr)) (hw : Covers [outputRegion (pa s out)] s.wr) :
    WP isa (callAt nm outNtt (positiveNttOutArgs out f)) s fun t =>
      Post S s t [outputRegion (pa s out)] ∧
      PositivePolyIs t.mem (pa s out) (ntt (polyAt s.mem (pa s f))) := by
  have hok : ∀ a∈positiveNttOutArgs out f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [positiveNttOutArgs,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨hook,by simp⟩
    · exact ⟨hfok,by simp⟩
  refine WP.mono (callAtSyms_ok hS (positiveNttOut_callee S) hok (by simp)
    (fun s1 h1 hy => ?_) hc hw) fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  · exact positiveNttOutAt_pre hofit hfit ht hf hio h1 hy
  · sig_post [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq] at hq
    rw [Args.r0 h1,Args.r1 h1,Args.mem h1] at hq
    exact hq

end VG.Proof.MlDsa.AArch64.Optimized
