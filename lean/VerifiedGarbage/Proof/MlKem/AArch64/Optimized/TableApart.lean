module

public import VerifiedGarbage.Proof.MlKem.AArch64.KemEnc
public import VerifiedGarbage.Proof.MlKem.AArch64.Dot.Table
public import VerifiedGarbage.Proof.MlKem.AArch64.KgCommon
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
public import VerifiedGarbage.Impl.MlKem.AArch64.Noise
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Saved
public import VerifiedGarbage.Proof.MlKem.PolyContract
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Squeeze
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.State
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Output
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.AArch64.PrimCall
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Load
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.RegionsSub
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Keep
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.InitMemory
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Zero
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Words
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Tail

/-! ### `MlKem.AArch64.Noise.Offsets`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Noise.Pair`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Noise.InitCall`, which this module and modules that import it used -/

section

/-! # Paired-noise prologue, including the register record -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/InitCore.lean`, which only this module imported.
section

/-! # Exact instruction proof of paired noise state initialization -/

section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem imm64 {n : Nat} (hn : n < 65536) :
    (BitVec.ofNat 16 n).setWidth 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem initCore_ok {s : State} {p a : Addr} {sb n : Nat}
    (hn : n+1 < 256) (hoff : sb+32 ≤ 32768) (halign : sb%8=0)
    (hp : s.gpr .x19=p) (ha : s.gpr .x28+BitVec.ofNat 64 sb=a)
    (hin : ∀ j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hw : ∀ j<25, InRegions s.wr (wordAddr p j) 16)
    (hsep : (Region.mk a 32).Disjoint (pairR p)) :
    WP isa (.block (Impl.MlKem.AArch64.Noise.initCore sb n)) s fun t =>
      RegKeep [.x6,.x7] s t ∧ Frame [pairR p] s.mem t.mem ∧
      PairAt t.mem p (seedState s.mem a n) (seedState s.mem a (n+1)) := by
  change WP isa (.block (zeroStates ++
    (((List.range 4).flatMap fun j => [.ldr .x .x6 .x28 (sb+8*j),
      .vop (.dup .d2 .v0 .x6),.strq .v0 .x19 (16*j)]) ++
    (tailWords n ++ [.movz .x .x6 0x8000 3,.vop (.dup .d2 .v0 .x6),.strq .v0 .x19 256])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (zeros_ok hp hw) fun z ⟨hz,hfz,hzero⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (seedWords_ok hoff halign ((hz.gpr .x19 (by simp)).trans hp)
    (by rw [hz.gpr .x28 (by simp)]; exact ha)
    (fun j hj => by rw [hz.rd,hz.wr]; exact hin j hj)
    (fun j hj => by rw [hz.wr]; exact hw j (by omega))
    (hsep.sub_right (Region.sub_prefix (by decide : 64≤400)))) fun v ⟨hv,hfv,hvals⟩ => ?_
  have hseed : SeedWords v.mem s.mem p a := seedWords_of_zero hzero hfv (fun j hj => by
    rw [hvals j hj]
    have hr : z.mem.readW (a+BitVec.ofNat 64 (8*j)) 64 = s.mem.readW (a+BitVec.ofNat 64 (8*j)) 64 :=
      hfz.read (Offset.contains_base a (d := 8*j) (n := 8) (k := 32) (by omega) (by omega))
        (by intro r hr; rw [List.mem_singleton.mp hr]; exact hsep) (by decide)
    rw [hr])
  rw [WP.block_append_iff]
  refine WP.mono (tailWords_ok (p := p) (by rw [hv.gpr .x19 (by simp),hz.gpr .x19 (by simp),hp])
    (by rw [hv.wr,hz.wr]; exact hw 4 (by decide))) fun w ⟨hwk,hmw⟩ => ?_
  refine WP.mono (padWord_ok (p := p) (j := 16) (by decide)
    (by rw [hwk.gpr .x19 (by simp),hv.gpr .x19 (by simp),hz.gpr .x19 (by simp),hp])
    (by rw [hwk.wr,hv.wr,hz.wr]; exact hw 16 (by decide))) fun t ⟨ht,hmt⟩ => ?_
  have he : t.mem = (v.mem.write (wordAddr p 4) 16
      (ofVDwords (BitVec.ofNat 64 (n+0x1f00)) (BitVec.ofNat 64 (n+1+0x1f00)))).write
      (wordAddr p 16) 16 (ofVDwords 0x8000000000000000 0x8000000000000000) := by
    rw [hmt,hmw,imm64 (by omega),imm64 (by omega)]; rfl
  refine ⟨(((hz.trans hv).trans hwk).trans ht).mono (by simp),?_,?_⟩
  · have hf : Frame [pairR p] s.mem v.mem := hfz.trans (hfv.sub (fun r hr => by
      rw [List.mem_singleton.mp hr]
      exact ⟨pairR p,by exact List.mem_singleton_self _,Region.sub_prefix (by decide : 64≤400)⟩))
    rw [he]
    exact (hf.write (by simp) _ (pair_contains p (by decide : 4<25))).write
      (by simp) _ (pair_contains p (by decide : 16<25))
  · rw [he]; exact tail_pair hseed

end VG.Proof.MlKem.AArch64.Noise
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

theorem seedState_frame {m m' : Mem} {a : Addr} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, (Region.mk a 32).Disjoint r) (n : Nat) :
    seedState m' a n = seedState m a n := by
  apply Vector.ext; intro i hi
  simp only [seedState,Vector.getElem_ofFn]
  split
  · rw [hf.readW (r := ⟨a,32⟩) (Offset.contains_base a (by omega_arith) (by omega_using [hi])) hd (by decide)]
  · rfl

def initRegs : List Reg := [.x2,.x19,.x20,.x21,.x6,.x7]

theorem init_ok {s : State} {p a : Addr} {ss sb n : Nat}
    (hss : ss < 65536) (hn : n+1<256) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (ha : s.gpr .x28+BitVec.ofNat 64 sb=a)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (a+BitVec.ofNat 64 (8*j)) 8)
    (hwr : ∀j<25, InRegions s.wr (wordAddr p j) 16)
    (hsv : ∀j<6, InRegions s.wr (p+BitVec.ofNat 64 (1800+8*j)) 8)
    (has : (Region.mk a 32).Disjoint (savedR p))
    (hap : (Region.mk a 32).Disjoint (pairR p))
    (hps : (savedR p).Disjoint (pairR p)) :
    WP isa (.block (ptrTo .x2 .x28 ss ++
      (Paired.saved.zipIdx.map fun (r,i) => .str .x r .x2 (1800+8*i)) ++
      ([mov .x19 .x2] : List Instr) ++ Impl.MlKem.AArch64.Noise.initCore sb n ++
      ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 528] : List Instr))) s fun t =>
      Keep initRegs s t ∧ Frame [savedR p,pairR p] s.mem t.mem ∧ Saved p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x20=p+400 ∧ t.gpr .x21=p+528 ∧
      PairAt t.mem p (seedState s.mem a n) (seedState s.mem a (n+1)) := by
  rw [List.append_assoc,List.append_assoc,List.append_assoc]
  refine wp_ptrTo (by decide) hss fun u hu eu => ?_
  rw [WP.block_append_iff]
  refine WP.mono (saves_ok (p := p) (by rw [eu]; exact hp)
    (fun j hj => by rw [hu.wr]; exact hsv j hj)) fun v ⟨kv,sv,fv⟩ => ?_
  have sv' : Saved p s v.mem := fun j hj => by
    rw [sv j hj,hu.get _ (by
      have hh : j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 := by omega_using [hj]
      rcases hh with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
  have fv' : Frame [savedR p] s.mem v.mem := by rw [hu.mem] at fv; exact fv
  refine wp_mov fun w hw ew => ?_
  change WP isa (.block (Impl.MlKem.AArch64.Noise.initCore sb n ++
    ([.addImm .x .x20 .x19 400,.addImm .x .x21 .x19 528] : List Instr))) w _
  rw [WP.block_append_iff]
  refine WP.mono (WP.preservedV (initCore_ok hn hsb h8
    (by rw [ew,kv.gpr .x2 (by simp),eu]; exact hp)
    (by rw [hw.get .x28 (by decide),kv.gpr .x28 (by simp),hu.get .x28 (by decide)]; exact ha)
    (fun j hj => by rw [hw.rd,hw.wr,kv.rd,kv.wr,hu.rd,hu.wr]; exact hin j hj)
    (fun j hj => by rw [hw.wr,kv.wr,hu.wr]; exact hwr j hj) hap)
    (hc := by rfl)) fun z ⟨⟨kz,fz,pz⟩,vz⟩ => ?_
  refine wp_addImm (by decide) fun y hy ey => wp_addImm (by decide) fun t ht et => wp_nil ?_
  have ksz : Keep [.x6,.x7] w z := ⟨kz.gpr,kz.rd,kz.wr,kz.sp,vz⟩
  have kt : Keep initRegs s t := (((((hu.keep.trans kv).trans hw.keep).trans ksz).trans hy.keep).trans ht.keep).mono (by simp [initRegs])
  have hm : t.mem=z.mem := ht.mem.trans hy.mem
  have h19 : z.gpr .x19=p := by
    rw [kz.gpr .x19 (by simp),ew,kv.gpr .x2 (by simp),eu]; exact hp
  have fw : Frame [savedR p] s.mem w.mem := by rw [hw.mem]; exact fv'
  have state_eq (k : Nat) : seedState w.mem a k = seedState s.mem a k :=
    seedState_frame fw (by intro r hr; rw [List.mem_singleton.mp hr]; exact has) k
  refine ⟨kt,?_,?_,?_,?_,?_,?_⟩
  · rw [hm]; exact (fw.mono (by simp)).trans (fz.mono (by simp))
  · rw [hm]; apply Saved.frame (m := w.mem) _ fz (by intro r hr; rw [List.mem_singleton.mp hr]; exact hps)
    rw [hw.mem]; exact sv'
  · rw [ht.get .x19 (by decide),hy.get .x19 (by decide),h19]
  · rw [ht.get .x20 (by decide),ey,h19]; rfl
  · rw [et,hy.get .x19 (by decide),h19]; rfl
  · rw [hm]; simpa only [state_eq n,state_eq (n+1)] using pz

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! ### `MlKem.AArch64.Noise.PairTail`, which this module and modules that import it used -/

section

/-! # Paired PRF call, both polynomial outputs and register restoration -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/OutCall.lean`, which only this module imported.

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

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Complete paired-noise operation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def outOff (L : KemLay) (kg : Bool) (n : Nat) : Nat :=
 if n<L.k then (if kg then KG.sOff L n else KEM.yOff L n) else Impl.MlKem.AArch64.Noise.noiseOff L (n-L.k)
def transformed (L : KemLay) (kg : Bool) (n : Nat) : Bool := kg || n<L.k

theorem TailSetup.regions {s t : State} {p f g w : Addr} (h : TailSetup s p f g w)
    (hr : t.rd=s.rd) (hw : t.wr=s.wr) : TailSetup t p f g w := by
  rcases h with ⟨a,b,c,d,e,f,g,j,k,l,m,n,o,q,r,v⟩
  exact ⟨by simpa only [hr,hw] using a,by simpa only [hw] using b,
    by simpa only [hw] using c,by simpa only [hw] using d,by simpa only [hr,hw] using e,
    by simpa only [hr,hw] using f,by simpa only [hr,hw] using g,
    by simpa only [hw] using j,by simpa only [hw] using k,l,m,n,o,q,r,v⟩

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! # Noise output bounds and nonoverlap for both layouts -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.Impl.MlKem.AArch64

variable {L : KemLay}

theorem outOff_fits (wf : L.Wf) (room : Room L) (kg : Bool) {j : Nat} (hj : j<2*L.k) :
    outOff L kg j+1024≤L.scl := by
  unfold outOff
  split
  · cases kg <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> lom
  · apply noise_fits room; omega_using [hj]

theorem outOff_low (wf : L.Wf) (room : Room L) (kg : Bool) (j : Nat) :
    (if kg then KG.NS else KEM.NS)+1024≤outOff L kg j := by
  have hkg := noise_past_kg room (j-L.k)
  have hkem := noise_past_kem room (j-L.k)
  cases kg <;> simp only [outOff,Bool.false_eq_true,ite_false,ite_true] <;> split <;> lom

theorem outOff_order (wf : L.Wf) (room : Room L) (kg : Bool) {i j : Nat}
    (hi : i<j) : outOff L kg i+1024≤outOff L kg j := by
  have hkg := noise_past_kg room (j-L.k)
  have hkem := noise_past_kem room (j-L.k)
  cases kg <;> simp only [outOff,Bool.false_eq_true,ite_false,ite_true] <;> split <;> split
  all_goals unfold Impl.MlKem.AArch64.Noise.noiseOff at *; lom

end VG.Proof.MlKem.AArch64.Noise

end

end

/-! ### `MlKem.AArch64.Optimized.KeyGenTables`, which this module and modules that import it used -/

section

/-! ### `MlKem.AArch64.Optimized.KeyGenRow`, which this module and modules that import it used -/

section

/-! # One fused key-generation row with a precomputed error polynomial -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
open VG.Impl.MlKem.AArch64.Noise (noiseOff)
variable {P : KemLay}

def rowTerms (P : KemLay) (i : Nat) : List (Nat × Nat) :=
 (List.range P.k).map fun j => (aOff P i j,sOff P j)

def rowWrites (P : KemLay) (s₀ : State) (i : Nat) : List Region :=
 [R (kA s₀) 3 (TP P) 1024,R (kA s₀) 1 (384*i) 384,R (kA s₀) 2 (384*P.k+384*i) 384]

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # Readonly gamma data through the fused key-generation rows -/

@[expose] public section
namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG VG.Proof.MlKem.AArch64
open VG.Spec.MlKem
variable {P : KemLay}

structure RowTable (P : KemLay) (s₀ s : State) : Prop where
  table : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA")
  read : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr)
  apart : ∀ i < P.k, ∀ r ∈ rowWrites P s₀ i, (⟨s.syms "VG_MLKEM_GAMMA",512⟩ : Region).Disjoint r

end VG.Proof.MlKem.AArch64.KeyGen

end

end

/-! # Readonly artifact tables are separate from every writable operand -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Optimized
open VG VG.AArch64

theorem apart_of_covers {r q : Region} {wr : List Region}
    (h : ∀p∈wr,r.Disjoint p) (hc : Covers [q] wr) : r.Disjoint q := by
  intro a ha hb
  obtain ⟨p,hp,hb⟩ := hc a 1 ⟨q,by simp,hb⟩
  exact h p hp a ha hb

end VG.Proof.MlKem.AArch64.Optimized

namespace VG.Proof.MlKem.AArch64.KeyGen
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KG
variable {P : KemLay}

theorem readonly_rows {s₀ s : State} (hp : Pre P s₀) (h : KB P s₀ s)
    (ta : Dot.GammaArtifact s.mem (s.syms "VG_MLKEM_GAMMA"))
    (tr : Covers [⟨s.syms "VG_MLKEM_GAMMA",512⟩] (s.rd++s.wr))
    (td : ∀r∈s.wr,(Region.mk (s.syms "VG_MLKEM_GAMMA") 512).Disjoint r) : RowTable P s₀ s := by
  have hw := hp.wf
  refine ⟨ta,tr,?_⟩
  intro i hi r hr
  simp only [rowWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=3) (o:=TP P) (l:=1024) (by decide) (by kl))
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=1) (o:=384*i) (l:=384) (by decide) (by kl))
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=2) (o:=384*P.k+384*i) (l:=384) (by decide) (by kl))

end VG.Proof.MlKem.AArch64.KeyGen

namespace VG.Proof.MlKem.AArch64.Kem
open VG VG.AArch64 VG.Impl.MlKem.AArch64 VG.Impl.MlKem.AArch64.KEM
variable {P : KemLay} {L : Layout}

theorem readonly_enc {s₀ s : State} (hp : Pre P L s₀) (h : KB P L s₀ s)
    {kE eo kC co : Nat} (ha : EncArgs P L kE eo kC co)
    {r : Region} (td : ∀q∈s.wr,r.Disjoint q) (ts : r.Disjoint (below s.sp 16)) :
    ∀q∈encW P L s₀ kC co,r.Disjoint q := by
  have hw := hp.wf
  intro q hq
  simp only [encW,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl|rfl|rfl|rfl|rfl
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=0) (l:=840) (by lom))
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=RB+32) (l:=1) (by lom))
  · exact Optimized.apart_of_covers td (cov_s hp h (o:=PB) (l:=SV P-PB) (by lom))
  · rwa [h.sp] at ts
  · exact Optimized.apart_of_covers td (cov_w hp h (b:=L.slot kC) (o:=co) (l:=P.ctLen)
      ⟨ha.wC,hp.lt ha.hkC⟩ ha.fC)

end VG.Proof.MlKem.AArch64.Kem
