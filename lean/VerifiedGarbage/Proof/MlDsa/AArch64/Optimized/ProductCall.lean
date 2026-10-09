import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ProductVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.MultiplyInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts expandedWords)

theorem productRaw_callee (S : Nat) :
    CalleeOk S (staticCode true) (multiplyInverseRawContract (abi.withConsts inverseConsts)) := by
  refine ⟨(productRaw_verified).1,(productRaw_verified).2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

abbrev productArgs (out a b scratch : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.ptr scratch)]

structure ProductCallReady (out a b scratch : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024≤2^64
  bFit : (pa s b).toNat+1024≤2^64
  scratchFit : (pa s scratch).toNat+1024≤2^64
  held : ∀i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64
  tableApart : ∀r∈[outputRegion (pa s out),outputRegion (pa s scratch)],
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r
  outA : (outputRegion (pa s out)).Disjoint (outputRegion (pa s a))
  outB : (outputRegion (pa s out)).Disjoint (outputRegion (pa s b))
  outScratch : (outputRegion (pa s out)).Disjoint (outputRegion (pa s scratch))
  aScratch : (outputRegion (pa s a)).Disjoint (outputRegion (pa s scratch))
  bScratch : (outputRegion (pa s b)).Disjoint (outputRegion (pa s scratch))
  positiveA : PositiveReduced s.mem (pa s a)
  positiveB : PositiveReduced s.mem (pa s b)
  readable : Covers ([outputRegion (pa s a),outputRegion (pa s b),
    tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]++[outputRegion (pa s out),outputRegion (pa s scratch)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s out),outputRegion (pa s scratch)] s.wr

theorem productAt_pre {s s1 : State} {out a b scratch : Ptr}
    (h : ProductCallReady out a b scratch s) (h1 : Args (productArgs out a b scratch) s s1)
    (hy : s1.syms=s.syms) :
    (multiplyInverseRawContract (abi.withConsts inverseConsts)).pre
      (s1.callEntry.withRegions [outputRegion (pa s a),outputRegion (pa s b),
        tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
        [outputRegion (pa s out),outputRegion (pa s scratch)]) := by
  sig_pre [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
    Args.mem h1,Arg.val]
  exact ⟨rfl,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),rfl,rfl,h.outA,h.outB,h.outScratch,h.aScratch,
    h.bScratch,h.outFit,h.aFit,h.bFit,h.scratchFit,h.positiveA,h.positiveB⟩

theorem productArgs_ok {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok) :
    ∀x∈productArgs out a b scratch,x.2.Ok ∧ x.1∈argRegs := by
  simp only [productArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨hs,by simp⟩

theorem productAt_ok {S : Nat} (hS : S<2^64)
    {nm : String} {s : State} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    (h : ProductCallReady out a b scratch s) :
    WP isa (callAt nm (staticCode true) (productArgs out a b scratch)) s fun t =>
      Post S s t [outputRegion (pa s out),outputRegion (pa s scratch)] ∧
      RawPolyIs t.mem (pa s out) (nttInv (multiplyNTT
        (polyAt s.mem (pa s a)) (polyAt s.mem (pa s b)))) := by
  refine WP.mono (callAtSyms_ok hS (productRaw_callee S) (productArgs_ok ho ha hb hs) (by simp)
    (fun s1 h1 hy => productAt_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [multiplyInverseRawContract,multiplyInverseRawSig,multiplyInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
