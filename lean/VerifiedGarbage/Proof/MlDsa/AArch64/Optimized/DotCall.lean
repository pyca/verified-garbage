import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.DotVerified
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.NttCallTiming

namespace VG.Proof.MlDsa.AArch64.Optimized.Inverse
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Call (Ptr Arg callAt)
open VG.Impl.MlDsa.AArch64.Optimized.DotInverse
open VG.Impl.MlDsa.AArch64.Optimized.Inverse (inverseConsts expandedWords)

theorem dot_callee (S : Nat) {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7) :
    CalleeOk S (staticCode count) (dotInverseContract count (abi.withConsts inverseConsts)) := by
  refine ⟨(dot_verified hc).1,(dot_verified hc).2.1,?_⟩
  change 0≤S
  exact Nat.zero_le _

abbrev dotArgs (out a b scratch : Ptr) : List (Reg × Arg) :=
  [(.x0,.ptr out),(.x1,.ptr a),(.x2,.ptr b),(.x3,.ptr scratch)]

structure DotCallReady (count : Nat) (out a b scratch : Ptr) (s : State) : Prop where
  outFit : (pa s out).toNat+1024≤2^64
  aFit : (pa s a).toNat+1024*count≤2^64
  bFit : (pa s b).toNat+1024*count≤2^64
  scratchFit : (pa s scratch).toNat+1024≤2^64
  held : ∀i<488,s.mem.readW (s.syms "VG_MLDSA_INV_FOLDED"+BitVec.ofNat 64 (8*i)) 64=expandedWords.getD i 0
  tableFit : (s.syms "VG_MLDSA_INV_FOLDED").toNat+3904≤2^64
  tableApart : ∀r∈[outputRegion (pa s out),outputRegion (pa s scratch)],
    (tableRegion (s.syms "VG_MLDSA_INV_FOLDED")).Disjoint r
  outA : (outputRegion (pa s out)).Disjoint (dotFamilyRegion (pa s a) count)
  outB : (outputRegion (pa s out)).Disjoint (dotFamilyRegion (pa s b) count)
  outScratch : (outputRegion (pa s out)).Disjoint (outputRegion (pa s scratch))
  aScratch : (dotFamilyRegion (pa s a) count).Disjoint (outputRegion (pa s scratch))
  bScratch : (dotFamilyRegion (pa s b) count).Disjoint (outputRegion (pa s scratch))
  positiveA : ∀j<count,PositiveReduced s.mem (pa s a+BitVec.ofNat 64 (1024*j))
  positiveB : ∀j<count,PositiveReduced s.mem (pa s b+BitVec.ofNat 64 (1024*j))
  readable : Covers ([dotFamilyRegion (pa s a) count,dotFamilyRegion (pa s b) count,
    tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]++[outputRegion (pa s out),outputRegion (pa s scratch)]) (s.rd++s.wr)
  writable : Covers [outputRegion (pa s out),outputRegion (pa s scratch)] s.wr

theorem dotAt_pre {s s1 : State} {count : Nat} {out a b scratch : Ptr}
    (h : DotCallReady count out a b scratch s) (h1 : Args (dotArgs out a b scratch) s s1)
    (hy : s1.syms=s.syms) :
    (dotInverseContract count (abi.withConsts inverseConsts)).pre
      (s1.callEntry.withRegions [dotFamilyRegion (pa s a) count,dotFamilyRegion (pa s b) count,
        tableRegion (s.syms "VG_MLDSA_INV_FOLDED")]
        [outputRegion (pa s out),outputRegion (pa s scratch)]) := by
  sig_pre [dotInverseContract,dotInverseSig,abi,argRegs,inverseConsts_eq,Abi.withConsts,
    Abi.constRegions,Abi.constsHeld,InverseTable.expandedWords_length,stackBelow]
  simp only [hy,Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.r3 h1,
    Args.mem h1,Arg.val]
  have he : count*256*4=1024*count := by omega
  rw [he]
  exact ⟨rfl,h.held,h.tableFit,h.tableApart _ (by simp),h.tableApart _ (by simp),rfl,rfl,h.outA,h.outB,h.outScratch,h.aScratch,
    h.bScratch,h.outFit,h.aFit,h.bFit,h.scratchFit,h.positiveA,h.positiveB⟩

theorem dotArgs_ok {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok) :
    ∀x∈dotArgs out a b scratch,x.2.Ok ∧ x.1∈argRegs := by
  simp only [dotArgs,List.mem_cons,List.not_mem_nil,or_false]
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨ho,by simp⟩
  · exact ⟨ha,by simp⟩
  · exact ⟨hb,by simp⟩
  · exact ⟨hs,by simp⟩

theorem dotAt_ok {S : Nat} (hS : S<2^64) {count : Nat} (hc : count=4 ∨ count=5 ∨ count=7)
    {nm : String} {s : State} {out a b scratch : Ptr}
    (ho : (Arg.ptr out).Ok) (ha : (Arg.ptr a).Ok) (hb : (Arg.ptr b).Ok) (hs : (Arg.ptr scratch).Ok)
    (h : DotCallReady count out a b scratch s) :
    WP isa (callAt nm (staticCode count) (dotArgs out a b scratch)) s fun t =>
      Post S s t [outputRegion (pa s out),outputRegion (pa s scratch)] ∧
      PolyIs t.mem (pa s out) (nttInv (dotNTT
        (fun j => polyAt s.mem (pa s a+BitVec.ofNat 64 (1024*j)))
        (fun j => polyAt s.mem (pa s b+BitVec.ofNat 64 (1024*j))) count)) := by
  refine WP.mono (callAtSyms_ok hS (dot_callee S hc) (dotArgs_ok ho ha hb hs) (by simp)
    (fun s1 h1 hy => dotAt_pre h h1 hy) h.readable h.writable)
    fun t ⟨hP,s1,h1,hq⟩ => ⟨hP,?_⟩
  sig_post [dotInverseContract,dotInverseSig,abi,argRegs,Abi.withConsts,inverseConsts_eq] at hq
  rw [Args.r0 h1,Args.r1 h1,Args.r2 h1,Args.mem h1] at hq
  exact hq

end VG.Proof.MlDsa.AArch64.Optimized.Inverse
