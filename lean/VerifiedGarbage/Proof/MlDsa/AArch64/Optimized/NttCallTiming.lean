import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCall

namespace VG.Proof.MlDsa.AArch64.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt glue)
open VG.Impl.MlDsa.AArch64.Optimized.Ntt

theorem glueSyms_ok {as : List (Reg × Arg)}
    (hok : ∀ a∈as,a.2.Ok ∧ a.1∈argRegs) (hnd : (as.map (·.1)).Nodup) (s : State) :
    WP isa (.block (glue as)) s fun t => Args as s t ∧ t.syms=s.syms :=
  WP.mono_syms (glue_ok hok hnd s) fun _ h hy => ⟨h,hy⟩

theorem callAtSyms_tr {S : Nat} {n : String} {c : Prog isa} {k : Contract isa} (C : CalleeOk S c k)
    {as : List (Reg × Arg)} (hok : ∀ a ∈ as, a.2.Ok ∧ a.1 ∈ argRegs) (hnd : (as.map (·.1)).Nodup)
    {P : State → State → Prop}
    (hP : ∀ x y x1 y1, P x y → Args as x x1 → Args as y y1 → x1.syms=x.syms → y1.syms=y.syms → ∃ rd wr : List Region,
      k.pre (x1.callEntry.withRegions rd wr) ∧ k.pre (y1.callEntry.withRegions rd wr) ∧
      k.pub (x1.callEntry.withRegions rd wr) (y1.callEntry.withRegions rd wr) ∧
      Covers (rd ++ wr) (x.rd ++ x.wr) ∧ Covers wr x.wr ∧
      Covers (rd ++ wr) (y.rd ++ y.wr) ∧ Covers wr y.wr) :
    RelCT isa P (callAt n c as) fun _ _ => True :=
  RelCT.seq (RelCT.postDep (Q := fun x1 y1 => ∃ x y, P x y ∧ Args as x x1 ∧ Args as y y1 ∧ x1.syms=x.syms ∧ y1.syms=y.syms)
      (block_nomem_tr (glue_nomem as)) (fun x y _ => ⟨glueSyms_ok hok hnd x,
        glueSyms_ok hok hnd y⟩)
      fun x y _ _ hp h1 h2 => ⟨x, y, hp, h1.1, h2.1, h1.2, h2.2⟩)
    (RelCT.mono (RelCT.exists_ (P := fun (a : List Region × List Region) (x1 y1 : State) =>
        k.pre (x1.callEntry.withRegions a.1 a.2) ∧ k.pre (y1.callEntry.withRegions a.1 a.2) ∧
        k.pub (x1.callEntry.withRegions a.1 a.2) (y1.callEntry.withRegions a.1 a.2) ∧
        Covers (a.1 ++ a.2) (x1.rd ++ x1.wr) ∧ Covers a.2 x1.wr ∧
        Covers (a.1 ++ a.2) (y1.rd ++ y1.wr) ∧ Covers a.2 y1.wr)
      fun a => RelCT.call C.correct C.ct a.1 a.2 fun _ _ h => h)
      (fun x1 y1 ⟨x, y, hp, h1, h2, hy1, hy2⟩ => by
        obtain ⟨rd, wr, p₁, p₂, pub, c₁, w₁, c₂, w₂⟩ := hP x y x1 y1 hp h1 h2 hy1 hy2
        exact ⟨(rd, wr), p₁, p₂, pub, by rw [h1.2.rd, h1.2.wr]; exact c₁, by rw [h1.2.wr]; exact w₁,
          by rw [h2.2.rd, h2.2.wr]; exact c₂, by rw [h2.2.wr]; exact w₂⟩)
      fun _ _ h => h)


structure NttCallReady (f : Ptr) (s : State) : Prop where
  fit : (pa s f).toNat+1024≤2^64
  table : NttTableAt s (pa s f)
  reduced : Reduced s.mem (pa s f)
  readable : Covers ([expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]++[outputRegion (pa s f)])
    (s.rd++s.wr)
  writable : Covers [outputRegion (pa s f)] s.wr

/-- The call reveals only the output address, stack pointer, and immutable
root-table address. The transform's coefficient values remain secret. -/
theorem positiveNttAt_tr {S : Nat} {nm : String} {f : Ptr} (hfok : (Arg.ptr f).Ok)
    {Q : State → State → Prop}
    (hQ : ∀ x y,Q x y → NttCallReady f x ∧ NttCallReady f y ∧ pa x f=pa y f ∧
      x.sp=y.sp ∧ x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED") :
    RelCT isa Q (callAt nm staticNtt (positiveNttArgs f)) fun _ _ => True := by
  have hok : ∀ a∈positiveNttArgs f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [positiveNttArgs,List.mem_singleton]
    intro a ha; subst a; exact ⟨hfok,by change Reg.x0∈argRegs; decide⟩
  refine callAtSyms_tr (positiveNtt_callee S) hok (by simp) fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,ep,esp,et⟩ := hQ x y hp
  refine ⟨[expandedRegion (x.syms "VG_MLDSA_NTT_EXPANDED")],[outputRegion (pa x f)],
    positiveNttAt_pre rx.fit rx.table rx.reduced h1 hy1,?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [ep,et]
    exact positiveNttAt_pre ry.fit ry.table ry.reduced h2 hy2
  · sig_pub [positiveNttContract,positiveNttSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,ep⟩
  · rw [ep,et]; exact ry.readable
  · rw [ep]; exact ry.writable


structure NttOutCallReady (out f : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  fit : (pa s f).toNat+1024≤2^64
  table : NttTableAt s (pa s out)
  reduced : Reduced s.mem (pa s f)
  apart : (outputRegion (pa s out)).Disjoint (outputRegion (pa s f))
  readable : Covers ([outputRegion (pa s f),expandedRegion (s.syms "VG_MLDSA_NTT_EXPANDED")]++
    [outputRegion (pa s out)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s out)] s.wr

theorem positiveNttOutAt_tr {S : Nat} {nm : String} {out f : Ptr}
    (hook : (Arg.ptr out).Ok) (hfok : (Arg.ptr f).Ok) {Q : State → State → Prop}
    (hQ : ∀ x y,Q x y → NttOutCallReady out f x ∧ NttOutCallReady out f y ∧
      pa x out=pa y out ∧ pa x f=pa y f ∧ x.sp=y.sp ∧
      x.syms "VG_MLDSA_NTT_EXPANDED"=y.syms "VG_MLDSA_NTT_EXPANDED") :
    RelCT isa Q (callAt nm outNtt (positiveNttOutArgs out f)) fun _ _ => True := by
  have hok : ∀ a∈positiveNttOutArgs out f,a.2.Ok ∧ a.1∈argRegs := by
    simp only [positiveNttOutArgs,List.mem_cons,List.not_mem_nil,or_false]
    intro a ha
    rcases ha with rfl | rfl
    · exact ⟨hook,by simp⟩
    · exact ⟨hfok,by simp⟩
  refine callAtSyms_tr (positiveNttOut_callee S) hok (by simp) fun x y x1 y1 hp h1 h2 hy1 hy2 => ?_
  obtain ⟨rx,ry,eo,ep,esp,et⟩ := hQ x y hp
  refine ⟨[outputRegion (pa x f),expandedRegion (x.syms "VG_MLDSA_NTT_EXPANDED")],
    [outputRegion (pa x out)],
    positiveNttOutAt_pre rx.outFit rx.fit rx.table rx.reduced rx.apart h1 hy1,
    ?_,?_,rx.readable,rx.writable,?_,?_⟩
  · rw [eo,ep,et]
    exact positiveNttOutAt_pre ry.outFit ry.fit ry.table ry.reduced ry.apart h2 hy2
  · sig_pub [positiveNttOutContract,positiveNttOutSig,abi,argRegs,Abi.withConsts,nttConsts_eq]
    rw [hy1,hy2,Args.r0 h1,Args.r0 h2,Args.r1 h1,Args.r1 h2,Args.sp h1,Args.sp h2]
    exact ⟨esp,et,eo,ep⟩
  · rw [eo,ep,et]; exact ry.readable
  · rw [eo]; exact ry.writable

end VG.Proof.MlDsa.AArch64.Optimized
