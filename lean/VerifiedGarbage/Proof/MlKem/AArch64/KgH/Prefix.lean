module

public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Inv
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.First
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgCommon
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16.KgRows
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.TransformTables
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cbd16Call
public import VerifiedGarbage.Proof.MlKem.AArch64.NttR.FastTable
public import VerifiedGarbage.Impl.MlKem.AArch64.NoiseWith
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16.ReadonlyCalls
public import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.PairTail
public import VerifiedGarbage.Proof.MlKem.Mem16
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.CoeffW
import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.W.Call
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitCall
import VerifiedGarbage.Proof.Framework.Omega

/-! ### `MlKem.AArch64.KgH.NoiseK`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.Writes`, which only this module used -/

section

/-! # Exact paired-noise footprints and separated retained outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def writes (L : KemLay) (kg : Bool) (B : Addr) (n : Nat) : List Region :=
 pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
   (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
   (B+BitVec.ofNat 64 (nttOff kg))

theorem writes_apart {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n off len : Nat} (hn : n+1<2*L.k) (hfit : off+len≤L.scl)
    (hss : off+len≤scratchOff kg ∨ scratchOff kg+2048≤off)
    (hns : off+len≤nttOff kg ∨ nttOff kg+1024≤off)
    (hf : off+len≤outOff L kg n ∨ outOff L kg n+1024≤off)
    (hg : off+len≤outOff L kg (n+1) ∨ outOff L kg (n+1)+1024≤off) :
    ∀r∈writes L kg B n, (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint r := by
  have lim := layout_limits wf kg
  have f0 := outOff_fits wf room kg (by omega_using [hn] : n<2*L.k)
  have f1 := outOff_fits wf room kg hn
  have sep {o k : Nat} (h : off+len≤o ∨ o+k≤off) (fit : o+k≤L.scl) :=
    Offset.disjoint B h (by omega_using [hfit, lim] : off+len≤2^64) (by omega_using [lim, fit] : o+k≤2^64)
  intro r hr
  simp only [writes,pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega_using [hss]) (by omega_using [lim])
  · exact sep hf f0
  · exact sep hg f1
  · exact sep hns lim.2.2.1

theorem writes_old_far {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n j : Nat} (hn : n+1<2*L.k) (hj : j<n) :
    ∀r∈writes L kg B n, (polyRegion (B+BitVec.ofNat 64 (outOff L kg j))).Disjoint r := by
  have lim := layout_limits wf kg
  have lo := outOff_low wf room kg j
  change nttOff kg+1024≤_ at lo
  have f := outOff_fits wf room kg (by omega_using [hn, hj] : j<2*L.k)
  exact writes_apart wf room kg B hn f (Or.inr (by omega_using [lim, lo])) (Or.inr lo)
    (Or.inl (outOff_order wf room kg hj)) (Or.inl (outOff_order wf room kg (by omega_using [hj])))

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! ### `MlKem.AArch64.Noise.ReadonlyLayoutPair`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.ReadonlyPairTail`, which only this module used -/

section

/-! ### `MlKem.AArch64.Noise.OutWith`, which only this module used -/

section

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

def outCodeWith (nttAt : Nat→Nat→Prog isa) (off ns buf : Nat) (tr : Bool) :
    Prog isa :=
 seqs [.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off),
   Impl.MlKem.AArch64.Noise.cbdCall,if tr then nttAt off ns else .block []]

theorem out_okWith {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (nttAt : Nat→Nat→Prog isa) (hoff : off<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩)
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (hn : ∀v, Kept [⟨f,1024⟩,⟨w,1024⟩] s v → v.syms=s.syms →
   PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) →
   WP isa (nttAt off ns) v fun t=> Kept [⟨f,1024⟩,⟨w,1024⟩] v t ∧
     PolyIsW (cw true) t.mem f (ntt (samplePolyCBD 2 (bytesAt s.mem b 128)))) :
 WP isa (outCodeWith nttAt off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 have sample : WP isa (.seq (.block (([.addImm .x .x0 .x19 buf] : List Instr)++ptrTo .x1 .x28 off))
     (Impl.MlKem.AArch64.Noise.cbdCall)) s fun v=>Kept [⟨f,1024⟩,⟨w,1024⟩] s v ∧
       PolyIsW (cw true) v.mem f (samplePolyCBD 2 (bytesAt s.mem b 128)) := by
  refine WP.seq (wp_addImm hbuf fun a ha ea=>wp_ptrTo' (by decide) hoff fun u hu eu=>?_)
  have ou : Only [.x0,.x1] s u := (ha.trans hu).mono (by simp)
  have ku : Kept [⟨f,1024⟩,⟨w,1024⟩] s u := Kept.of_keep ou.keep ou.mem (by decide)
  exact cbdW_call (by rw [hu.get .x0 (by decide),ea]; exact hb)
    (by rw [eu,ha.get .x28 (by decide)]; exact hf) hbf
    (by rw [ou.rd,ou.wr]; exact hc)
    (by rw [ou.wr]; intro a n ⟨r,hr,ha⟩; exact hcw a n ⟨r,by simp at hr; simp [hr],ha⟩)
    (fun v kv pv=>⟨ku.trans (kv.mono (by simp)),by simpa only [ou.mem] using pv⟩)
 apply WP.assoc
 refine WP.seq (WP.mono_syms sample fun v ⟨kv,pv⟩ sv=>?_)
 cases transform
 · exact wp_nil ⟨kv,pv⟩
 · exact WP.mono (hn v kv sv pv) fun t ⟨kt,pt⟩=>⟨kv.trans kt,pt⟩
end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Paired PRF call, both polynomial outputs and register restoration -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyOut.lean`, which only this module imported.
section

section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

/-- One noise output with 16-bit coefficients, transformed (`nttAtWithW`) if `transform`. -/
theorem readonly_out_okW {s : State} {off ns buf : Nat} {b f w : Addr} (transform : Bool)
 (hoff : off<65536) (hns : ns<65536) (hbuf : buf<4096)
 (hb : s.gpr .x19+BitVec.ofNat 64 buf=b) (hf : s.gpr .x28+BitVec.ofNat 64 off=f)
 (hw : s.gpr .x28+BitVec.ofNat 64 ns=w)
 (hbf : (Region.mk b 128).Disjoint ⟨f,1024⟩) (hfw : (polyRegion f).Disjoint (polyRegion w))
 (hc : Covers [⟨b,128⟩,⟨f,1024⟩] (s.rd++s.wr))
 (hcw : Covers [⟨f,1024⟩,⟨w,1024⟩] s.wr)
 (ht : NttR.FastReady s f w) :
 WP isa (outCodeWith Ntt16.Readonly.nttAtWithW off ns buf transform) s fun t=>
   Kept [⟨f,1024⟩,⟨w,1024⟩] s t ∧
   PolyIsW (cw true) t.mem f (if transform then ntt (samplePolyCBD 2 (bytesAt s.mem b 128))
     else samplePolyCBD 2 (bytesAt s.mem b 128)) := by
 refine out_okWith transform _ hoff hbuf hb hf hbf hc hcw fun v kv sv pv=>?_
 have table := ht.frame sv kv.rd kv.wr kv.frame (by
   intro r hr
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
   rcases hr with rfl|rfl
   · exact ht.output.symm
   · exact ht.scratch.symm)
 have sub : ∀ x ∈ [Region.mk f 512, ⟨w,512⟩], ∃ r ∈ [Region.mk f 1024, ⟨w,1024⟩], Region.Sub x r := by
   intro x hx
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl
   · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
   · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
 refine WP.mono (Ntt16.W.nttAtWithW_ok hoff hns
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hf)
   (by rw [kv.cs .x28 (by decide) (by decide)]; exact hw)
   (hfw.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right (Region.sub_prefix (by decide : 512 ≤ 1024)))
   pv (by
     rw [kv.wr]
     exact Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head hcw))
       (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail hcw))) Covers.nil))
   table) fun t ⟨kt,pt⟩ => ⟨Kept.sub kt sub, pt⟩
end VG.Proof.MlKem.AArch64.Noise
end

end

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
  have r0 := output_prf (by omega_using [hn] : n<256) ra
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

end

end

/-! # Execute a pair using only the public scratch allocation -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/ReadonlyPair.lean`, which only this module imported.
section

/-! # Complete paired-noise operation -/
section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)

theorem readonly_noisePair_ok {s : State} {L : KemLay} (kg : Bool) {n : Nat} {p a f g w : Addr}
    (hn : n+1<256)
    (h0 : outOff L kg n <65536) (h1 : outOff L kg (n+1)<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SS else KEM.SS)=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.SG else KEM.RB)=a)
    (hf : s.gpr .x28+BitVec.ofNat 64 (outOff L kg n)=f)
    (hg : s.gpr .x28+BitVec.ofNat 64 (outOff L kg (n+1))=g)
    (hw : s.gpr .x28+BitVec.ofNat 64 (if kg then KG.NS else KEM.NS)=w)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk a 32).Disjoint (savedR p))
    (hap : (Region.mk a 32).Disjoint (pairR p))
    (hs : TailSetup s p f g w)
    (ht0 : NttR.FastReady s f w)
    (ht1 : NttR.FastReady s g w)
    (hfar : ∀r∈pairWrites p f g w,(NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites p f g w) s t ∧
      PolyIsW (cw true) t.mem f (sampled s.mem a n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem g (sampled s.mem a (n+1) (transformed L kg (n+1))) := by
  change WP isa (.seq (.block (Impl.MlKem.AArch64.Noise.noiseInit L kg n))
    (seqs [Impl.MlKem.AArch64.Noise.squeezePair,
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg n) (if kg then KG.NS else KEM.NS) 400 (transformed L kg n),
      outCodeWith Ntt16.Readonly.nttAtWithW (outOff L kg (n+1)) (if kg then KG.NS else KEM.NS) 528 (transformed L kg (n+1)),
      .block (Paired.saved.zipIdx.reverse.map fun (r,i) => .ldr .x r .x19 (1800+8*i))])) s _
  refine WP.seq (WP.mono_syms (init_ok (by cases kg <;> decide) hn
    (by cases kg <;> decide) (by cases kg <;> decide) hp ha hin hwr hsv has hap
    (Offset.disjoint_base p (by decide) (by decide))) fun u ⟨ku,fu,sv,h19,h20,h21,pair⟩ us => ?_)
  have pu : Partial (pairWrites p f g w) s u :=
    ⟨fun r hr hn => ku.gpr r (by revert r hr hn; decide),ku.rd,ku.wr,ku.sp,ku.vcs,
      fu.mono (by simp [pairWrites])⟩
  have t0 := ht0.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  have t1 := ht1.frame us ku.rd ku.wr fu (by
    intro r hr; exact hfar r (by simp only [pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; grind))
  exact readonly_pair_tail_ok (transformed L kg n) (transformed L kg (n+1)) hn h0 h1
    (by cases kg <;> decide) pu sv h19 h20 h21
    (by rw [ku.gpr .x28 (by decide)]; exact hf)
    (by rw [ku.gpr .x28 (by decide)]; exact hg)
    (by rw [ku.gpr .x28 (by decide)]; exact hw)
    (hs.regions ku.rd ku.wr) pair t0 t1 (by simpa only [NttR.fastRegion, NttR.sRegion, us] using hfar)

end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem (PolyIsW)
open VG.Proof.MlKem (cw)
open VG.Proof.Sha3.AArch64.Neon


theorem readonly_noisePair_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} {n : Nat} (hn : n+1<2*L.k) (hB : s.gpr .x28=B)
    (hc : Covers [⟨B,L.scl⟩] s.wr)
    (ht0 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (nttOff kg)))
    (ht1 : NttR.FastReady s
      (B+BitVec.ofNat 64 (outOff L kg (n+1))) (B+BitVec.ofNat 64 (nttOff kg)))
    (hfar : ∀r∈pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
      (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
      (B+BitVec.ofNat 64 (nttOff kg)), (NttR.fastRegion s).Disjoint r) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW L kg n) s fun t =>
      Kept (pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
        (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (B+BitVec.ofNat 64 (nttOff kg))) s t ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg n))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) n (transformed L kg n)) ∧
      PolyIsW (cw true) t.mem (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) (n+1) (transformed L kg (n+1))) := by
  have lim := layout_limits wf kg
  have fit0 := outOff_fits wf room kg (by omega_using [hn] : n<2*L.k)
  have fit1 := outOff_fits wf room kg hn
  have low0 := outOff_low wf room kg n
  have low1 := outOff_low wf room kg (n+1)
  change nttOff kg+1024≤outOff L kg n at low0
  change nttOff kg+1024≤outOff L kg (n+1) at low1
  have order := outOff_order wf room kg (Nat.lt_succ_self n)
  have size : L.scl<2^64 := by omega_using [lim]
  have iw {o l : Nat} (h : o+l≤L.scl) := inScratch hc h size
  have ir {o l : Nat} (h : o+l≤L.scl) : InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 o) l :=
    by obtain ⟨r,hr,hc⟩ := iw h; exact ⟨r,List.mem_append_right _ hr,hc⟩
  have cw {o l : Nat} (h : o+l≤L.scl) := coversScratch hc h
  have sep {o l d k : Nat} (h : o+l≤d ∨ d+k≤o) (ho : o+l≤L.scl) (hd : d+k≤L.scl) :=
    Offset.disjoint B h (by omega_using [lim, ho] : o+l≤2^64) (by omega_using [lim, hd] : d+k≤2^64)
  have snorm (k : Nat) : B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 k =
      B+BitVec.ofNat 64 (scratchOff kg+k) := by rw [BitVec.add_assoc,← BitVec.ofNat_add]
  refine readonly_noisePair_ok kg (by have := wf.facts; omega_using [hn, this]) (by omega_using [lim, fit0]) (by omega_using [lim, fit1])
    (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]) (by rw [hB]) (by rw [hB]; rfl)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_ ht0 ht1 hfar
  · rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact ir (by omega_using [lim, hj])
  · change InRegions s.wr (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*j)) 16
    rw [snorm]; exact iw (by omega_using [lim, hj])
  · rw [snorm]; exact iw (by omega_using [lim, hj])
  · change (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [snorm]; exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) (by omega_using [lim])
  · exact sep (Or.inl lim.2.1) (by omega_using [lim]) (by omega_using [lim])
  · constructor
    · intro i hi
      change InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*i)) 16
      rw [snorm]; exact ir (by omega_using [lim, hi])
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega_using [lim, hi])
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega_using [lim, hi])
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg),400⟩,
        ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩] s.wr
      rw [snorm]; exact coversTwo (cw (by omega_using [lim])) (cw (by omega_using [lim]))
    · intro i hi; rw [snorm]; exact ir (by omega_using [lim, hi])
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg n),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega_using [lim])) (cw fit0))
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg (n+1)),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega_using [lim])) (cw fit1))
    · exact coversTwo (cw fit0) (cw lim.2.2.1)
    · exact coversTwo (cw fit1) (cw lim.2.2.1)
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega_using [lim, low1])) (by omega_using [lim]) fit1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl
      · exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
      · exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) lim.2.2.1
    · exact sep (Or.inl order) fit0 fit1
    · exact sep (Or.inr low0) fit0 lim.2.2.1
    · exact sep (Or.inr low1) fit1 lim.2.2.1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800) 48).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl | rfl
      · exact sep (Or.inl (by omega_using [lim, low0])) (by omega_using [lim]) fit0
      · exact sep (Or.inl (by omega_using [lim, low1])) (by omega_using [lim]) fit1
      · exact sep (Or.inl (by omega_using [lim])) (by omega_using [lim]) lim.2.2.1

end VG.Proof.MlKem.AArch64.Noise

end

end


/-! # Key generation's noise from the first pairs' PRF outputs

`kgOut_ok`: `SamplePolyCBD₂` of buffer `N` into `ŝ[N]` or `ê[N - k]`,
transformed (`Kem16P.kgOut`). `noiseK_ok`: the six buffers the first two
pairs filled, then paired `PRF₂` for the rest of the noise, leave `ŝ` and `ê`
(`NK`) with `Â` as the pairs left it. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem (cw)
open VG.Impl.MlKem.AArch64.Noise (noiseOff)

variable {P : KemLay}

theorem kgTarget_eq (P : KemLay) (N : Nat) :
    Impl.MlKem.AArch64.Kem16P.kgTarget P N = Noise.outOff P true N := rfl

/-- `ŝ[N]` for `N < k`, `ê[N - k]` after. -/
abbrev kgPoly (P : KemLay) (s₀ : State) (N : Nat) : Poly :=
  if N < P.k then KPke.kgS P.params (dB s₀) N else KPke.kgE P.params (dB s₀) (N - P.k)

theorem kgPoly_eq (s₀ : State) (N : Nat) :
    kgPoly P s₀ N = ntt (samplePolyCBD 2 (prf 2 (KPke.kgSigma P.params (dB s₀)) (BitVec.ofNat 8 N))) := by
  unfold kgPoly
  split
  · rfl
  · rename_i h
    simp only [KPke.kgE, VG.Proof.MlKem.cbd, KemLay.params]
    rw [Nat.add_sub_cancel' (by omega_arith)]

/-- The polynomials of the noise lie between `NS + 1024` and the end of `scratch`, apart from
`TP`'s buffers. -/
theorem out_far (hw : P.Wf) (hr : Noise.Room P) {N : Nat} (hN : N < 2 * P.k) :
    NS + 1024 ≤ Noise.outOff P true N ∧ Noise.outOff P true N + 1024 ≤ P.scl ∧
      (Noise.outOff P true N + 1024 ≤ TP P ∨ SV P + 48 ≤ Noise.outOff P true N) ∧
      SH P ≤ Noise.outOff P true N := by
  have lo := Noise.outOff_low hw hr true N
  change KG.NS + 1024 ≤ _ at lo
  refine ⟨lo, Noise.outOff_fits hw hr true hN, ?_⟩
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sv : SV P = TP P + 2048 := rfl
  unfold Noise.outOff
  split
  · rename_i h
    simp only [ite_true]
    have so : KG.sOff P N = SH P + 1024 * N := rfl
    rw [so]
    have := Nat.mul_le_mul_left 1024 (show N + 1 ≤ P.k by omega_arith)
    omega_arith
  · have := Noise.noise_past_kg hr (N - P.k)
    omega_arith

/-- **`kgOut`**: `SamplePolyCBD₂` of buffer `N` into its polynomial, transformed. -/
theorem kgOut_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (h : KB P s₀ s)
    (htr : Optimized.TransformTables s) {N : Nat} (hN6 : N < 6) (hN : N < 2 * P.k) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P N) s fun t => KB P s₀ t ∧
      Frame [R (kA s₀) 3 (Noise.outOff P true N) 1024, R (kA s₀) 3 NS 1024] s.mem t.mem ∧
      t.gpr .x24 = s.gpr .x24 ∧ t.syms = s.syms ∧
      PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N))
        (ntt (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128))) := by
  have hw := hp.wf
  obtain ⟨tN, tS, tB, -⟩ := out_far hw hr hN
  generalize ht : Noise.outOff P true N = T at tN tS tB
  have h3 := kL_le hw 3
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have kl3 : kL P 3 = P.scl := rfl
  have cst : SV P + 48 ≤ P.scl ∧ KG.NS + 1024 ≤ TP P := ⟨by omega_using [hsv, kl3], by lom⟩
  have t64 : T < 65536 := by omega_using [tS, h3, kl3]
  have hbo : TP P + 168 * N < 65536 := by omega_using [hsv, sv, h3, hN6]
  have fT : T + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  have fN : KG.NS + 1024 ≤ kL P 3 := by omega_using [cst, hsv, sv]
  have fB : TP P + 168 * N + 128 ≤ kL P 3 := by omega_using [hsv, sv, hN6]
  have dBT : (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 T 1024) :=
    sdisjK hp fB fT (by rcases tB with h | h <;> omega_arith)
  have dTN : (R (kA s₀) 3 T 1024).Disjoint (R (kA s₀) 3 KG.NS 1024) := sdisjK hp fT fN (.inr tN)
  have cT : Covers [R (kA s₀) 3 T 1024] s.wr := cov_w hp h (b := 3) (by decide) fT
  have cN : Covers [R (kA s₀) 3 KG.NS 1024] s.wr := cov_w hp h (b := 3) (by decide) fN
  have cB : Covers [R (kA s₀) 3 (TP P + 168 * N) 128] (s.rd ++ s.wr) := cov_r hp h (b := 3) (by decide) fB
  have sT := kb_disj hp (b := 3) (o := T) (l := 1024) (by decide) fT
    (.inr (by rcases tB with h | h <;> omega_arith)) (by decide)
  have sN := kb_disj hp (b := 3) (o := KG.NS) (l := 1024) (by decide) fN (.inr (.inr (by omega_arith))) (by decide)
  unfold Impl.MlKem.AArch64.Kem16P.kgOut
  rw [kgTarget_eq, ht]
  simp only [seqs, Impl.MlKem.AArch64.Kem16P.bufOff]
  have sample : WP isa (.seq (.block (Impl.MlKem.AArch64.ptrTo .x0 .x28 (TP P + 168 * N) ++
      Impl.MlKem.AArch64.ptrTo .x1 .x28 T)) Impl.MlKem.AArch64.Noise.cbdCall) s fun v =>
      Kept [R (kA s₀) 3 T 1024] s v ∧
      PolyIsW (cw true) v.mem (kA s₀ 3 + BitVec.ofNat 64 T)
        (samplePolyCBD 2 (bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128)) := by
    refine WP.seq (wp_ptrTo (by decide) hbo fun a ha ea => wp_ptrTo' (by decide) t64 fun u hu eu => ?_)
    have ou : Only [.x0, .x1] s u := (ha.trans hu).mono (by simp)
    have ku : Kept [R (kA s₀) 3 T 1024] s u := Kept.of_keep ou.keep ou.mem (by decide)
    exact cbdW_call (by rw [hu.get .x0 (by decide), ea, h.x28])
      (by rw [eu, ha.get .x28 (by decide), h.x28]) dBT
      (by rw [ou.rd, ou.wr]; exact Covers.cons (Covers.head cB) (Covers.right cT))
      (by rw [ou.wr]; exact cT)
      (fun v kv pv => ⟨ku.trans kv, by simpa only [ou.mem] using pv⟩)
  apply WP.assoc
  refine WP.seq (WP.mono_syms sample fun v ⟨kv, pv⟩ sv' => ?_)
  have kbv := h.call kv (fun r hr => by rw [List.mem_singleton.mp hr]; exact sT)
  have tv := htr.frame sv' kv.rd kv.wr kv.sp kv.frame cT
  have cv : Covers [polyRegion (kA s₀ 3 + BitVec.ofNat 64 T), polyRegion (kA s₀ 3 + BitVec.ofNat 64 KG.NS)] v.wr := by
    rw [kv.wr]; exact Covers.cons (Covers.head cT) (Covers.cons (Covers.head cN) Covers.nil)
  refine WP.mono_syms (Ntt16.W.nttAtWithW_ok t64 (by decide) (by rw [kbv.x28]) (by rw [kbv.x28])
    (dTN.sub_left (Region.sub_prefix (by decide : 512 ≤ 1024)) |>.sub_right
      (Region.sub_prefix (by decide : 512 ≤ 1024))) pv
    (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head cv))
      (Covers.cons (covers_prefix (by decide : 512 ≤ 1024) (Covers.head (Covers.tail cv))) Covers.nil))
    (tv.fast.ready cv)) fun t ⟨kt, pt⟩ st => ?_
  have kt' : Kept [R (kA s₀) 3 T 1024, R (kA s₀) 3 KG.NS 1024] v t := kt.sub fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., Region.sub_prefix (by decide : 512 ≤ 1024)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Region.sub_prefix (by decide : 512 ≤ 1024)⟩
  refine ⟨kbv.call kt' fun r hr => ?_, (kv.frame.mono (by simp)).trans kt'.frame,
    (kt'.cs .x24 (by decide) (by decide)).trans (kv.cs .x24 (by decide) (by decide)), st.trans sv', pt⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact sT
  · exact sN

/-- After `G`, the first two pairs and the first `j` polynomials of the noise. -/
structure NK (P : KemLay) (s₀ s : State) (j : Nat) (t : State) : Prop where
  c : CInvW P s₀ s.mem (s.gpr .x24) 4 t
  syms : t.syms = s.syms
  tt : Optimized.TransformTables t
  buf : ∀ N < 6, bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128 =
    bytesAt s.mem (kA s₀ 3 + BitVec.ofNat 64 (TP P + 168 * N)) 128
  done : ∀ N < j, PolyIsW 16 t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true N)) (kgPoly P s₀ N)

/-- A region of `scratch` past `NS` and apart from `TP`'s buffers misses `σ`, `ρ`, `Â`, the
saved registers, the seed and the buffers. -/
theorem noise_regionK {s₀ : State} (hp : Pre P s₀) {o l : Nat} (hf : o + l ≤ kL P 3) (hNS : KG.NS ≤ o)
    (hm : o + l ≤ AH ∨ SH P ≤ o) (hb : o + l ≤ TP P ∨ SV P + 48 ≤ o) :
    ((R (kA s₀) 3 SB 32).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 3 SG 32).Disjoint (R (kA s₀) 3 o l) ∧
      (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint (R (kA s₀) 3 o l)) ∧
    ((svR P s₀).Disjoint (R (kA s₀) 3 o l) ∧ (R (kA s₀) 0 0 64).Disjoint (R (kA s₀) 3 o l)) ∧
    ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint (R (kA s₀) 3 o l) := by
  have hw := hp.wf
  have hsv := hp.sv
  have sv : SV P = TP P + 2048 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have cst : SB + 32 ≤ SG ∧ SG + 32 ≤ KG.NS := by decide
  refine ⟨⟨sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])),
    sdisjK hp (by kl) hf (.inl (by omega_using [cst, hNS])), sdisjK hp (by kl) hf (by omega_using [hm, sh])⟩,
    kb_disj hp (by decide) hf (.inr (by omega_using [hb, sv])) (by decide), fun N hN => ?_⟩
  exact sdisjK hp (by omega_using [hsv, sv, hN]) hf (by omega_using [hb, sv, hN, hm, tp, sh])

theorem NK.zero {s₀ s : State} (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) : NK P s₀ s 0 s :=
  ⟨⟨H.b.kb, H.b.rho, H.b.sig, rfl, by have := Nat.mul_le_mul hk3 hk3; omega_arith,
    fun e he => ⟨H.b.red e he, rfl⟩⟩, rfl, H.tables.transforms, fun _ _ => rfl,
    fun N hN => absurd hN (Nat.not_lt_zero N)⟩

/-- `kgOut` keeps `NK`. -/
theorem kgOut_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {j : Nat} (hj6 : j < 6)
    (hj : j < 2 * P.k) (hprf : PrfK P s₀ s.mem j) (H : NK P s₀ s j t) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgOut P j) t (NK P s₀ s (j + 1)) := by
  have hw := hp.wf
  refine WP.mono (kgOut_ok hp hr H.c.kb H.tt hj6 hj) fun u ⟨ku, fu, xu, su, pu⟩ => ?_
  obtain ⟨tN, tS, tB, tH⟩ := out_far hw hr hj
  have kl3 : kL P 3 = P.scl := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have fT : Noise.outOff P true j + 1024 ≤ kL P 3 := by omega_using [tS, kl3]
  have fN : KG.NS + 1024 ≤ kL P 3 := by kl
  have rT := noise_regionK hp fT (by omega_using [tN]) (.inr tH) tB
  have c0 : KG.NS + 1024 ≤ AH := by decide
  have rN := noise_regionK hp fN (Nat.le_refl _) (.inl (by decide)) (.inl (by omega_using [tp, sh, c0]))
  have far : ∀ r ∈ [R (kA s₀) 3 (Noise.outOff P true j) 1024, R (kA s₀) 3 KG.NS 1024],
      (((R (kA s₀) 3 SB 32).Disjoint r ∧ (R (kA s₀) 3 SG 32).Disjoint r ∧
        (R (kA s₀) 3 AH (1024 * (P.k * P.k))).Disjoint r) ∧
      ((svR P s₀).Disjoint r ∧ (R (kA s₀) 0 0 64).Disjoint r) ∧
      ∀ N < 6, (R (kA s₀) 3 (TP P + 168 * N) 128).Disjoint r) := by
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact rT
    · exact rN
  have rdt : t.rd = s₀.rd := H.c.kb.rd
  have wrt : t.wr = s₀.wr := H.c.kb.wr
  refine ⟨H.c.frame ku xu fu fun r hr' => (far r hr').1, su.trans H.syms,
    H.tt.frame su (ku.rd.trans rdt.symm) (ku.wr.trans wrt.symm) (ku.sp.trans H.c.kb.sp.symm) fu
      (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fT))
        (Covers.cons (Covers.head (cov_w hp H.c.kb (b := 3) (by decide) fN)) Covers.nil)),
    fun N hN => ?_, fun N hN => ?_⟩
  · rw [bytesAt_frame fu (fun r hr' => (far r hr').2.2 N hN) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < j ∨ N = j) with hN | rfl
    · obtain ⟨tN', tS', -, -⟩ := out_far hw hr (N := N) (by omega_arith)
      have fT' : Noise.outOff P true N + 1024 ≤ kL P 3 := by omega_using [tS', kl3]
      have ord := Noise.outOff_order hw hr true hN
      refine polyIsW_frame_poly (w16 := true) fu (fun r hr' => ?_) (H.done N hN)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with rfl | rfl
      · exact sdisjK hp fT' fT (.inl ord)
      · exact sdisjK hp fT' fN (.inr tN')
    · rw [H.buf N hj6, hprf, ← kgPoly_eq] at pu
      exact pu

/-- The writes of a noise pair miss a region apart from its working space and outputs. -/
theorem writes_apartK {B : Addr} {n : Nat} {r : Region}
    (hs : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.scratchOff true), 2048⟩)
    (hn : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.nttOff true), 1024⟩)
    (ho : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true n), 1024⟩)
    (ho' : r.Disjoint ⟨B + BitVec.ofNat 64 (Noise.outOff P true (n + 1)), 1024⟩) :
    ∀ q ∈ Noise.writes P true B n, r.Disjoint q := by
  intro q hq
  simp only [Noise.writes, Noise.pairWrites, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (Offset.sub_base _ (d := 1800) (n := 48) (k := 2048) (by decide))
  · exact hs.sub_right (Region.sub_prefix (by decide : 400 ≤ 2048))
  · exact hs.sub_right (Offset.sub_base _ (d := 400) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 528) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 1536) (n := 136) (k := 2048) (by decide))
  · exact ho
  · exact ho'
  · exact hn

/-- A noise pair (`Noise.noisePairWith`) for outputs `n` and `n + 1` keeps `NK`. -/
theorem pairK_step {s₀ s t : State} (hp : Pre P s₀) (hr : Noise.Room P) {n : Nat} (hn : n + 1 < 2 * P.k)
    (H : NK P s₀ s n t) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true n) t (NK P s₀ s (n + 2)) := by
  have hw := hp.wf
  have kb := H.c.kb
  have kl3 : kL P 3 = P.scl := rfl
  have hc : Covers [⟨kA s₀ 3, P.scl⟩] t.wr := by
    simpa only [R, ptr_zero] using cov_w hp kb (b := 3) (o := 0) (l := P.scl) (by decide) (by kl)
  have lim := Noise.layout_limits hw true
  simp only [Noise.scratchOff, Noise.nttOff, Noise.seedOff, ite_true] at lim
  obtain ⟨oN, oS, oB, oH⟩ := out_far hw hr (N := n) (by omega_arith)
  obtain ⟨oN', oS', oB', oH'⟩ := out_far hw hr (N := n + 1) hn
  have fO : Noise.outOff P true n + 1024 ≤ kL P 3 := by omega_using [oS, kl3]
  have fO' : Noise.outOff P true (n + 1) + 1024 ≤ kL P 3 := by omega_using [oS', kl3]
  have fS : KG.SS + 2048 ≤ kL P 3 := by kl
  have fN : KG.NS + 1024 ≤ kL P 3 := by kl
  have cvs {o l : Nat} (h : o + l ≤ P.scl) := Noise.coversScratch hc h
  have rdy (m : Nat) (hm : m < 2 * P.k) :=
    H.tt.fast.ready (Noise.coversTwo (cvs (Noise.outOff_fits hw hr true hm)) (cvs (o := KG.NS) (l := 1024) (by omega_using [fN, kl3])))
  -- Every region apart from the pair's working space, `NS` and both outputs misses its writes.
  have away {r : Region} (h1 : r.Disjoint (R (kA s₀) 3 KG.SS 2048)) (h2 : r.Disjoint (R (kA s₀) 3 KG.NS 1024))
      (h3 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true n) 1024))
      (h4 : r.Disjoint (R (kA s₀) 3 (Noise.outOff P true (n + 1)) 1024)) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, r.Disjoint q :=
    writes_apartK (P := P) h1 h2 h3 h4
  have tfar (sym : String) (H' : List Nat) (tt : Optimized.TransformTable t sym H') :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (Region.mk (t.syms sym) 512).Disjoint q :=
    away (tt.apart (cov_w hp kb (b := 3) (by decide) fS)) (tt.apart (cov_w hp kb (b := 3) (by decide) fN))
      (tt.apart (cov_w hp kb (b := 3) (by decide) fO)) (tt.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have ffar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastRegion t).Disjoint q :=
    away (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.fast.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have ifar : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (NttR.fastInvRegion t).Disjoint q :=
    away (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fS)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fN))
      (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO)) (H.tt.inverse.apart (cov_w hp kb (b := 3) (by decide) fO'))
  have sc (o l : Nat) (hf : o + l ≤ kL P 3) (hs : o + l ≤ KG.SS) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inl hs)) (sdisjK hp hf fN (.inl (by omega_using [hs, lim])))
      (sdisjK hp hf fO (.inl (by omega_using [hs, lim, oN]))) (sdisjK hp hf fO' (.inl (by omega_using [hs, lim, oN'])))
  have hi (o l : Nat) (hf : o + l ≤ kL P 3) (h1 : KG.NS + 1024 ≤ o)
      (h2 : o + l ≤ Noise.outOff P true n ∨ Noise.outOff P true n + 1024 ≤ o)
      (h3 : o + l ≤ Noise.outOff P true (n + 1) ∨ Noise.outOff P true (n + 1) + 1024 ≤ o) :
      ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 3 o l).Disjoint q :=
    away (sdisjK hp hf fS (.inr (by omega_using [h1, lim]))) (sdisjK hp hf fN (.inr h1))
      (sdisjK hp hf fO h2) (sdisjK hp hf fO' h3)
  refine WP.mono_syms (Noise.readonly_noisePair_layout (B := kA s₀ 3) hw hr true hn kb.x28 hc
    (rdy n (by omega_arith)) (rdy (n + 1) hn) ffar) fun u ⟨ku, pu, qu⟩ sy => ?_
  have sv : SV P = TP P + 2048 := rfl
  have tp : TP P = SH P + 1024 * P.k + 1024 := rfl
  have sh : SH P = AH + 1024 * (P.k * P.k) := rfl
  have hsv := hp.sv
  have cst : KG.SB + 32 ≤ KG.SG ∧ KG.SG + 32 ≤ KG.SS ∧ KG.NS + 1024 ≤ AH := by decide
  have seed0 : ∀ q ∈ Noise.writes P true (kA s₀ 3) n, (R (kA s₀) 0 0 64).Disjoint q :=
    away (seed_disj hp (b := 3) (by decide) fS (by decide)) (seed_disj hp (b := 3) (by decide) fN (by decide))
      (seed_disj hp (b := 3) (by decide) fO (by decide)) (seed_disj hp (b := 3) (by decide) fO' (by decide))
  have kbu : KB P s₀ u := kb.call ku fun r hr' =>
    ⟨hi (SV P) 48 hsv (by omega_using [sv, tp, sh, cst]) (by omega_using [oB, oH, sv, tp])
        (by omega_using [oB', oH', sv, tp]) r hr', seed0 r hr'⟩
  have hsig : bytesAt t.mem (kA s₀ 3 + BitVec.ofNat 64 KG.SG) 32 = KPke.kgSigma P.params (dB s₀) := H.c.sig
  have samp {m : Nat} (hm : m < 2 * P.k) (h' : PolyIsW (cw true) u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m))
      (Noise.sampled t.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.seedOff true)) m (Noise.transformed P true m))) :
      PolyIsW 16 u.mem (kA s₀ 3 + BitVec.ofNat 64 (Noise.outOff P true m)) (kgPoly P s₀ m) := by
    rw [kgPoly_eq]
    simpa only [Noise.sampled, Noise.seedOff, Noise.transformed, Bool.true_or, ite_true, hsig, cw] using h'
  refine ⟨H.c.frame kbu (ku.cs .x24 (by decide) (by decide)) ku.frame fun r hr' =>
      ⟨sc KG.SB 32 (by kl) (by omega_using [cst]) r hr', sc KG.SG 32 (by kl) (by omega_using [cst]) r hr',
        hi AH (1024 * (P.k * P.k)) (by kl) (by omega_using [cst]) (by omega_using [oH, sh]) (by omega_using [oH', sh]) r hr'⟩,
    ?_, ?_, fun N hN => ?_, fun N hN => ?_⟩
  · rw [sy]; exact H.syms
  · exact H.tt.frameFar sy ku.rd ku.wr ku.sp ku.frame fun r hr' =>
      ⟨tfar _ _ H.tt.forward r hr', ifar r hr', ffar r hr'⟩
  · rw [bytesAt_frame ku.frame (hi (TP P + 168 * N) 128 (by omega_using [hsv, sv, hN]) (by omega_using [tp, sh, cst])
      (by omega_using [oB, oH, sv, tp, hN]) (by omega_using [oB', oH', sv, tp, hN])) (by decide)]
    exact H.buf N hN
  · rcases (by omega_arith : N < n ∨ N = n ∨ N = n + 1) with hN' | rfl | rfl
    · exact polyIsW_frame_poly (w16 := true) ku.frame (Noise.writes_old_far hw hr true (kA s₀ 3) hn hN') (H.done N hN')
    · exact samp (by omega_arith) pu
    · exact samp hn qu

/-- **The noise** from the first pairs' buffers, then paired `PRF₂` for the rest. -/
theorem noiseK_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s) :
    WPs (((List.range 6).map (Impl.MlKem.AArch64.Kem16P.kgOut P)) ++
      ((List.range (P.k - 3)).map fun i =>
        Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))) s
      (NK P s₀ s (2 * P.k)) := by
  refine WPs.append (WPs.mono (WPs.range (I := NK P s₀ s) (fun j hj t ht =>
    kgOut_step hp hr hj (by omega_arith) (H.prf j hj) ht) (NK.zero hk3 H)) fun t ht => ?_)
  have r := WPs.range (f := fun i => Impl.MlKem.AArch64.Noise.noisePairWith Ntt16.Readonly.nttAtWithW P true (6 + 2 * i))
    (I := fun i => NK P s₀ s (6 + 2 * i)) (n := P.k - 3) (fun i hi u hu => by
      have st := pairK_step hp hr (n := 6 + 2 * i) (by omega_arith) hu
      rwa [show 6 + 2 * i + 2 = 6 + 2 * (i + 1) by omega_arith] at st) ht
  rwa [show 6 + 2 * (P.k - 3) = 2 * P.k by omega_arith] at r

/-- The noise as `KgRows` encodes `ŝ` from it. -/
theorem NK.encode {s₀ s t : State} (H : NK P s₀ s (2 * P.k) t) :
    EncodeInvW P s₀ s.mem t.mem (s.gpr .x24) 4 0 t := by
  refine ⟨H.c, fun j hj => ?_, fun j hj => ?_, fun _ hj => absurd hj (Nat.not_lt_zero _), Frame.refl _ _⟩
  · have d := H.done j (by omega_arith)
    simp only [kgPoly, ite_true, hj, Noise.outOff] at d
    exact d
  · have d := H.done (P.k + j) (by omega_arith)
    simp only [kgPoly, Noise.outOff, show ¬ P.k + j < P.k by omega_arith, ite_false, Nat.add_sub_cancel_left] at d
    exact d

end VG.Proof.MlKem.AArch64.KeyGen

end

end


/-! # After the first two pairs: the noise, `ŝ` into `dk`, the all-zero third state

`pre_ok`: after `G` and the first two pairs of the matrix (`FInv`),
`Kem16P.kgPre` establishes the interleaved invariant with the first four entries
of the matrix and nothing of the rows or the hash done. -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.KeyGen

open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt stateAt)
open VG.Proof.MlKem.AArch64.Optimized
open VG.Proof.MlKem.AArch64.Hybrid (TStk)

variable {P : KemLay}

/-- The third state, `scratch`'s first 200 bytes, is apart from the other values. -/
theorem st_far {s₀ : State} (hp : Pre P s₀) {b o l : Nat} (hb : b < 4) (f : o + l ≤ kL P b)
    (hs : b ≠ 3 ∨ 200 ≤ o) : (R (kA s₀) b o l).Disjoint (R (kA s₀) 3 0 200) := by
  have hw := hp.wf
  exact hp.args.rdisj hb (by decide) f (by kl) (by rcases hs with hs | hs <;> omega_using [hs])

/-- The all-zero third state. -/
theorem zero_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) {mB mN : Mem} {v : BitVec 64} {n : Nat}
    (h : EncodeInvW P s₀ mB mN v n P.k s) :
    WP isa (.block (zeroState .x28 KG.ST)) s fun t =>
      EncodeInvW P s₀ mB t.mem v n P.k t ∧ stateAt t.mem (kA s₀ 3) = Spec.Sha3.zero := by
  have hw := hp.wf
  have kb := h.c.kb
  refine WP.mono (zeroState_ok (hsetup hp kb (rate := 136) (by decide)) ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩)
    fun t ⟨kt, zt⟩ => ?_
  have e : STr .x28 KG.ST s = R (kA s₀) 3 0 200 := by simp only [STr, R, kb.x28, KG.ST]
  rw [e] at kt
  rw [kb.x28, show KG.ST = 0 from rfl, ptr_zero] at zt
  have kbt := kb.call kt fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact ⟨(st_far hp (b := 3) (o := SV P) (l := 48) (by decide) hp.sv (.inr (by lom))),
      st_far hp (by decide) (by kl) (.inl (by decide))⟩
  have far : ∀ {b o l : Nat}, b < 4 → o + l ≤ kL P b → (b ≠ 3 ∨ 200 ≤ o) →
      ∀ r ∈ [R (kA s₀) 3 0 200], (R (kA s₀) b o l).Disjoint r := fun hb f hs r hr => by
    rw [List.mem_singleton.mp hr]; exact st_far hp hb f hs
  refine ⟨⟨h.c.frame kbt (kt.cs .x24 (by decide) (by decide)) kt.frame fun r hr => ⟨far (by decide) (by kl) (.inr (by decide)) r hr,
      far (by decide) (by kl) (.inr (by decide)) r hr, far (by decide) (by kl) (.inr (by lom)) r hr⟩,
    fun j hj => polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (by kl) (.inr (by lom))) (h.sp j hj),
    fun j hj => ?_, fun j hj => ?_, Frame.refl _ _⟩, zt⟩
  · exact polyIsW_frame_poly (w16 := true) kt.frame (far (by decide) (Noise.noise_fits hr hj)
      (.inr (by have := Noise.noise_past_kg hr j; lom))) (h.errors j hj)
  · rw [bytesAt_frame kt.frame (far (by decide) (by kl) (.inl (by decide))) (by decide)]
    exact h.dk j hj

/-- **The noise, `ŝ` into `dk` and the all-zero third state**, after `G` and the first two
pairs of the matrix (`Kem16P.kgPre`). -/
theorem pre_ok {s₀ s : State} (hp : Pre P s₀) (hr : Noise.Room P) (hk3 : 3 ≤ P.k) (H : FInv P s₀ 4 6 s)
    (depth : (Impl.MlKem.AArch64.Kem16P.kgPre P).aarch64Depth ≤ 1) :
    WP isa (Impl.MlKem.AArch64.Kem16P.kgPre P) s (IL P s₀ 4 0 0) := by
  have hw := hp.wf
  have body : WP isa (Impl.MlKem.AArch64.Kem16P.kgPre P) s fun v => ∃ mN,
      EncodeInvW P s₀ s.mem mN (s.gpr .x24) 4 P.k v ∧ stateAt v.mem (kA s₀ 3) = Spec.Sha3.zero := by
    unfold Impl.MlKem.AArch64.Kem16P.kgPre
    refine WPs.seqs (by simp) (WPs.append (WPs.append (WPs.mono (noiseK_ok hp hr hk3 H) fun t ht => ?_)))
    exact WPs.mono (encode_okW hp hr ht.encode) fun u eu =>
      WPs.single (WP.mono (zero_ok hp hr eu) fun v ⟨ev, zv⟩ => ⟨_, ev, zv⟩)
  refine WP.mono_syms (WP.tablesDepth body H.tables depth) fun v ⟨⟨mN, ev, zv⟩, tv⟩ hs => ?_
  have kbv := ev.c.kb
  refine ⟨⟨kbv, ev.c.rho, ev.c.sig, by rw [ev.c.x24, H.b.acc], fun e he => (ev.c.ahat e he).1,
      fun e he => ?_⟩,
    ev.sp, ev.errors, ev.dk, fun i hi => absurd hi (Nat.not_lt_zero _), by simp,
    ev.c.le, Nat.zero_le _, ?_, by simp, tv,
    H.tstk.of hs (by rw [kbv.sp, H.b.kb.sp])⟩
  · rcases H.b.res e he with h | h
    · exact .inl h
    · refine .inr (h.trans ?_)
      exact congrArg some ((ev.c.ahat e he).2).symm
  · rw [zv, Hybrid.hstate_zero]

end VG.Proof.MlKem.AArch64.KeyGen
