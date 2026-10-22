module

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.ReadonlyOut
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.PairTail
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.OutWith
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.Call
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Readonly.At
import VerifiedGarbage.Proof.MlKem.CoeffW
import VerifiedGarbage.Proof.Framework.Offset

/-! # Paired PRF call, both polynomial outputs and register restoration -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

theorem readonly_pair_tail_ok {initial s : State} {p a f g w : Addr} {off0 off1 ns n : Nat}
    (tr0 tr1 : Bool) (hn : n+1<256) (h0 : off0<65536) (h1 : off1<65536) (hns : ns<65536)
    (hk : Partial (pairWrites p f g w) initial s) (sv : Saved p initial s.mem)
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=p+400) (hb : s.gpr .x21=p+528)
    (hf : s.gpr .x28+BitVec.ofNat 64 off0=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 off1=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
    (hs : TailSetup s p f g w)
    (hpair : PairAt s.mem p (seedState initial.mem a n) (seedState initial.mem a (n+1)))
    (ht0 : NttR.FastReady s f w)
    (ht1 : NttR.FastReady s g w)
    (hfar : ∀r∈pairWrites p f g w,(NttR.fastRegion s).Disjoint r) :
    WP isa (seqs [Impl.MlKem.AArch64.Noise.squeezePair,outCodeWith Ntt16.Readonly.nttAtWithW off0 ns 400 tr0,outCodeWith Ntt16.Readonly.nttAtWithW off1 ns 528 tr1,
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))]) s fun t =>
      Kept (pairWrites p f g w) initial t ∧
      PolyIsW (cw true) t.mem f (sampled initial.mem a n tr0) ∧
      PolyIsW (cw true) t.mem g (sampled initial.mem a (n+1) tr1) := by
  simp only [seqs]
  refine WP.seq (WP.mono_syms (squeezePair_ok hp ha hb (by rw [hp])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) hpair hs.pair hs.rateA hs.rateB
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide)) hs.call) fun u ⟨ku,_,ra,rb,fu,vu⟩ su => ?_)
  have pu : Partial (pairWrites p f g w) initial u := hk.trans
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,vu,fu.mono (by simp [pairWrites])⟩
  have svu : Saved p initial u.mem := sv.frame fu (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide))
  have tab0 := ht0.frame su ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  have tab1 := ht1.frame su ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  have r0 := output_prf (by omega : n<256) ra
  have r1 := output_prf hn rb
  refine WP.seq (WP.mono_syms (readonly_out_okW tr0 h0 hns (by decide)
    (by rw [ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    hs.bufA hs.fw (by rw [ku.rd,ku.wr]; exact hs.cbdA)
    (by rw [ku.wr]; exact hs.nttA) tab0) fun v ⟨kv,pv⟩ vuSym => ?_)
  have pvv : PolyIsW (cw true) v.mem f (sampled initial.mem a n tr0) := by simpa only [r0,sampled] using pv
  have pkeep : Partial (pairWrites p f g w) initial v := pu.trans ((Partial.of_kept kv).mono (by simp [pairWrites]))
  have svv : Saved p initial v.mem := svu.frame kv.frame (by
    intro r hr; apply hs.savedFar r
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢
    rcases hr with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h))
  have r1v : bytesAt v.mem (p+528) 128 = prf 2 (bytesAt initial.mem a 32) (BitVec.ofNat 8 (n+1)) :=
    (Proof.MlKem.bytesAt_frame kv.frame hs.next (by decide)).trans r1
  have tab1v := tab1.frame vuSym kv.rd kv.wr kv.frame (by
    intro r hr
    simp only [NttR.sRegion, su]
    exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  refine WP.seq (WP.mono (readonly_out_okW tr1 h1 hns (by decide)
    (by rw [kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]; rfl)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hg)
    (by rw [kv.cs .x28 (by decide) (by decide),ku.gpr .x28 (by decide)]; exact hw)
    hs.bufB hs.gw (by rw [kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.cbdB)
    (by rw [kv.wr,ku.wr]; exact hs.nttB) tab1v) fun z ⟨kz,pz⟩ => ?_)
  have pzz : PolyIsW (cw true) z.mem g (sampled initial.mem a (n+1) tr1) := by simpa only [r1v,sampled] using pz
  have pfz : PolyIsW (cw true) z.mem f (sampled initial.mem a n tr0) :=
    Proof.MlKem.polyIsW_frame_poly kz.frame (by simpa using And.intro hs.fg hs.fw) pvv
  have pkeepz := pkeep.trans ((Partial.of_kept kz).mono (by simp [pairWrites]))
  have svz : Saved p initial z.mem := svv.frame kz.frame (by
    intro r hr; apply hs.savedFar r; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; exact Or.inr hr)
  refine WP.mono (restores_ok (by
    rw [kz.cs .x19 (by decide) (by decide),kv.cs .x19 (by decide) (by decide),ku.gpr .x19 (by decide),hp]) svz
    (fun i hi => by rw [kz.rd,kz.wr,kv.rd,kv.wr,ku.rd,ku.wr]; exact hs.saved i hi)) fun t ⟨ot,rt⟩ => ?_
  exact ⟨pkeepz.restore ot rt,by rw [ot.mem]; exact pfz,by rw [ot.mem]; exact pzz⟩

end VG.Proof.MlKem.AArch64.Noise
