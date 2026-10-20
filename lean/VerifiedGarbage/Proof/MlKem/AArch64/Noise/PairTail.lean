module
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Spec.MlKem.Poly
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutCall
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Rc4.AArch64.Vec

/-! # Paired PRF call, both polynomial outputs and register restoration -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

def pairWrites (p f g w : Addr) : List Region :=
 [savedR p,pairR p,rateR (p+400),rateR (p+528),X2.callR (p+1536),⟨f,1024⟩,⟨g,1024⟩,⟨w,1024⟩]
def sampled (m : Mem) (a : Addr) (n : Nat) (tr : Bool) : Poly :=
 let f := samplePolyCBD 2 (prf 2 (bytesAt m a 32) (BitVec.ofNat 8 n))
 if tr then ntt f else f

def outCode (off ns buf : Nat) (tr : Bool) : Prog isa :=
 seqs [.block ([.addImm .x .x0 .x19 buf] ++ ptrTo .x1 .x28 off),.call "vg_mlkem_cbd2" cbd2,
  if tr then .seq (.block (ptrTo .x0 .x28 off ++ ptrTo .x1 .x28 ns))
   (.call "vg_mlkem_ntt" Ntt16.ntt) else .block []]

structure TailSetup (s : State) (p f g w : Addr) : Prop where
  pair : ∀i<25, InRegions (s.rd++s.wr) (wordAddr p i) 16
  rateA : ∀i<16, InRegions s.wr (outAddr (p+400) i) 8
  rateB : ∀i<16, InRegions s.wr (outAddr (p+528) i) 8
  call : Covers [pairR p,X2.callR (p+1536)] s.wr
  saved : ∀i<6, InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (1800+8*i)) 8
  cbdA : Covers [⟨p+400,128⟩,⟨f,1024⟩] (s.rd++s.wr)
  cbdB : Covers [⟨p+528,128⟩,⟨g,1024⟩] (s.rd++s.wr)
  nttA : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr
  nttB : Covers [⟨g,1024⟩,⟨w,1024⟩] s.wr
  bufA : (Region.mk (p+400) 128).Disjoint ⟨f,1024⟩
  bufB : (Region.mk (p+528) 128).Disjoint ⟨g,1024⟩
  next : ∀ r ∈ [Region.mk f 1024,⟨w,1024⟩], (Region.mk (p+528) 128).Disjoint r
  fg : (Region.mk f 1024).Disjoint ⟨g,1024⟩
  fw : (Region.mk f 1024).Disjoint ⟨w,1024⟩
  gw : (Region.mk g 1024).Disjoint ⟨w,1024⟩
  savedFar : ∀r∈[Region.mk f 1024,⟨g,1024⟩,⟨w,1024⟩], (savedR p).Disjoint r

theorem pair_tail_ok {initial s : State} {p a f g w : Addr} {off0 off1 ns n : Nat}
    (tr0 tr1 : Bool) (hn : n+1<256) (h0 : off0<65536) (h1 : off1<65536) (hns : ns<65536)
    (hk : Partial (pairWrites p f g w) initial s) (sv : Saved p initial s.mem)
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=p+400) (hb : s.gpr .x21=p+528)
    (hf : s.gpr .x28+BitVec.ofNat 64 off0=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 off1=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (hs : TailSetup s p f g w)
    (hpair : PairAt s.mem p (seedState initial.mem a n) (seedState initial.mem a (n+1))) :
    WP isa (seqs [Impl.MlKem.AArch64.Noise.squeezePair,outCode off0 ns 400 tr0,outCode off1 ns 528 tr1,
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))]) s fun t =>
      Kept (pairWrites p f g w) initial t ∧
      PolyIs t.mem f (sampled initial.mem a n tr0) ∧
      PolyIs t.mem g (sampled initial.mem a (n+1) tr1) := by
  simp only [seqs]
  refine WP.seq (WP.mono (squeezePair_ok hp ha hb (by rw [hp])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hpair hs.pair hs.rateA hs.rateB
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide)) hs.call) fun u ⟨ku,_,ra,rb,fu,vu⟩ => ?_)
  have pu : Partial (pairWrites p f g w) initial u := hk.trans
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,vu,fu.mono (by simp [pairWrites])⟩
  have svu : Saved p initial u.mem := sv.frame fu (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide))
  have r0 := output_prf (by omega : n<256) ra
  have r1 := output_prf hn rb
  refine WP.seq (WP.mono (out_ok tr0 h0 hns (by decide)
    (by rw [ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    hs.bufA hs.fw (by rw [ku.rd,ku.wr]; exact hs.cbdA)
    (by rw [ku.wr]; exact hs.nttA)) fun v ⟨kv,pv⟩ => ?_)
  have pvv : PolyIs v.mem f (sampled initial.mem a n tr0) := by simpa only [r0,sampled] using pv
  have pkeep : Partial (pairWrites p f g w) initial v := pu.trans ((Partial.of_kept kv).mono (by simp [pairWrites]))
  have svv : Saved p initial v.mem := svu.frame kv.frame (by
    intro r hr; apply hs.savedFar r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h))
  have r1v : bytesAt v.mem (p+528) 128 = prf 2 (bytesAt initial.mem a 32) (BitVec.ofNat 8 (n+1)) :=
    (Proof.MlKem.bytesAt_frame kv.frame hs.next (by decide)).trans r1
  refine WP.seq (WP.mono (out_ok tr1 h1 hns (by decide)
    (by rw [kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hg)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hw)
    hs.bufB hs.gw (by rw [kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.cbdB)
    (by rw [kv.wr,ku.wr]; exact hs.nttB)) fun z ⟨kz,pz⟩ => ?_)
  have pzz : PolyIs z.mem g (sampled initial.mem a (n+1) tr1) := by simpa only [r1v,sampled] using pz
  have pfz : PolyIs z.mem f (sampled initial.mem a n tr0) :=
    Proof.MlKem.polyIs_frame kz.frame (by simpa using And.intro hs.fg hs.fw) pvv
  have pkeepz := pkeep.trans ((Partial.of_kept kz).mono (by simp [pairWrites]))
  have svz : Saved p initial z.mem := svv.frame kz.frame (by
    intro r hr; apply hs.savedFar r; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact Or.inr hr)
  refine WP.mono (restores_ok (by
    rw [kz.cs .x19 (by decide) (by decide),kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]) svz
    (fun i hi => by rw [kz.rd,kz.wr,kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.saved i hi)) fun t ⟨ot,rt⟩ => ?_
  exact ⟨pkeepz.restore ot rt,by rw [ot.mem]; exact pfz,by rw [ot.mem]; exact pzz⟩

end VG.Proof.MlKem.AArch64.Noise
