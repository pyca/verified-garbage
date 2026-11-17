module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SeedSpec
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Segment
import VerifiedGarbage.Proof.MlKem.AArch64.HashProof
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Zero
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.FullInit
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Readonly
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.SingleStep
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Squeeze
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Output
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.MlKem.AArch64.Shared
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Dd10Step
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.DdStore
import VerifiedGarbage.Proof.MlKem.AArch64.CodecV.Blocks
import VerifiedGarbage.Proof.MlKem.AArch64.NttVec
import VerifiedGarbage.Proof.MlKem.Compress
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Pair
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.Store
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
import VerifiedGarbage.Proof.Sha3.AArch64.Sha3.Vector.Common
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Env
import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.RegionsSub

/-! ### `MlKem.AArch64.Paired.FullReject`, which only this module used -/

section

/-! # Reject the first three paired SHAKE128 blocks -/

@[expose] public section

namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Proof.MlKem.AArch64 VG.Spec.MlKem VG.Proof.MlKem
open VG.Impl.MlKem.AArch64

def fullEntry (buf out : Nat) : List Instr := ptrTo .x3 .x28 out ++
  [.addImm .x .x2 .x19 buf,.movz .x .x4 256 0,.movz .x .x5 280 0,
   .movz .x .x9 3329 0,.movz .x .x10 15 0]

theorem fullEntry_ok {w16 : Bool} (s : State) {buf out : Nat} (hb : buf<4096) (ho : out<65536)
    {B : Nat → Byte} (hp : Rej8.EnvW w16 280 B (s.gpr .x19+BitVec.ofNat 64 buf)
      (s.gpr .x28+BitVec.ofNat 64 out) s) (hc : Rej8.Constants s) :
    WP isa (.block (fullEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      Rej8.EntryW w16 [] 280 B (s.gpr .x19+BitVec.ofNat 64 buf) (s.gpr .x28+BitVec.ofNat 64 out) u := by
  have hw : WP isa (.block (fullEntry buf out)) s fun u =>
      Only [.x2,.x3,.x4,.x5,.x9,.x10] s u ∧
      u.gpr .x2=s.gpr .x19+BitVec.ofNat 64 buf ∧
      u.gpr .x3=s.gpr .x28+BitVec.ofNat 64 out ∧
      (u.gpr .x4).toNat=256 ∧ (u.gpr .x5).toNat=280 ∧
      (u.gpr .x9).toNat=q ∧ (u.gpr .x10).toNat=15 := by
    refine wp_ptrTo (by decide) ho fun a ha ea => wp_addImm hb fun b hb eb =>
      wp_movz fun c hc ec => wp_movz fun d hd ed => wp_movz fun e he ee =>
      wp_movz fun u hu eu => wp_nil ?_
    refine ⟨(((((ha.trans hb).trans hc).trans hd).trans he).trans hu).mono (by decide),?_,?_,?_,?_,?_,?_⟩
    · rw [hu.get .x2,he.get .x2,hd.get .x2,hc.get .x2,eb,ha.get .x19]
    · rw [hu.get .x3,he.get .x3,hd.get .x3,hc.get .x3,hb.get .x3,ea]
    · rw [hu.get .x4,he.get .x4,hd.get .x4,ec]; rfl
    · rw [hu.get .x5,he.get .x5,ed]; rfl
    · rw [hu.get .x9,ee]; rfl
    · rw [eu]; rfl
  have hnov : (fullEntry buf out).all (fun i => !writesV i)=true := by
    unfold fullEntry ptrTo
    split <;> rfl
  refine WP.mono (WP.keepV hnov hw) fun u ⟨⟨hk,x2,x3,x4,x5,x9,x10⟩,hv⟩ => ⟨hk,?_⟩
  refine ⟨hp.transfer hk.mem hk.rd hk.wr (hk.get .x16),?_,by simp,
    fun _ h => False.elim (Nat.not_lt_zero _ h),x2,?_,x4,x5,x9,x10⟩
  · exact ⟨by rw [hv]; exact hc.index,by rw [hv]; exact hc.mask,
      by simpa only [hv] using hc.q,by simpa only [hv] using hc.weights,
      by simpa only [hv] using hc.zero⟩
  · simpa only [List.length_nil,cAddr,Nat.mul_zero,ptr_zero] using x3

def fullFinish (w16 : Bool := false) : Prog isa := seqs [Impl.MlKem.AArch64.Rej8.rejLoop w16,
  .block [.logic .and .x .x24 .x24 .x0],Rej8.zeroSuffix w16,
  .block [.ldr .x .x22 .x19 1848,.ldr .x .x23 .x19 1856]]

def fullFinishRegs : List Reg := [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x22,.x23,.x24]

structure FullFinishPostW (w16 : Bool) (B : Nat → Byte) (out : Addr) (flags s u : State) : Prop where
  keep : Keep fullFinishRegs s u
  frame : Frame [polyRegion out] s.mem u.mem
  coeffs : CoeffsUpToW w16 u.mem out (sampleAfter [] B 280).length (Sample.cvW w16 (sampleAfter [] B 280))
    (fun _ => 0)
  reduced : ReducedW (cw w16) u.mem out
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] B 280).length=256 then 1 else 0)
  flag22 : u.gpr .x22=flags.gpr .x22
  flag23 : u.gpr .x23=flags.gpr .x23

theorem fullFinish_ok {w16 : Bool} {s flags : State} {p out : Addr} {B : Nat → Byte}
    (he : Rej8.EntryW w16 [] 280 B (p+400) out s)
    (hp : s.gpr .x19=p) (hf : Flags p flags s.mem)
    (hd : (flagR p).Disjoint (polyRegion out))
    (hr0 : InRegions (s.rd++s.wr) (p+1848) 8)
    (hr1 : InRegions (s.rd++s.wr) (p+1856) 8) :
    WP isa (fullFinish w16) s (FullFinishPostW w16 B out flags s) := by
  refine WP.seq (WP.mono (Rej8.segment_ok he (by decide) (by decide)) fun a ha => ?_)
  refine WP.seq (wp_and fun b hb eb => wp_nil ?_)
  refine WP.seq (WP.mono (Rej8.zeroSuffix_prefix (aP := out) (L := sampleAfter [] B 280)
    (by intro i hi; rw [hb.wr,ha.keep.wr]; exact he.env.ina i hi)
    ha.acc.len (by rw [hb.mem]; exact ha.acc.coeffs)
    (by rw [hb.get .x3]; exact ha.acc.x3)
    (by rw [hb.get .x4]; exact ha.acc.x4)) fun c ⟨kc,fc,cc⟩ => ?_)
  have frame : Frame [polyRegion out] s.mem c.mem := by
    exact ha.acc.frame.trans (by rw [←hb.mem]; exact fc)
  have flagsC := hf.frame frame (by simpa using hd)
  have h19 : c.gpr .x19=p := by rw [kc.get .x19,hb.get .x19,ha.keep.get .x19,hp]
  refine wp_ldrx (by decide) (by rw [h19])
    (by rw [kc.rd,kc.wr,hb.rd,hb.wr,ha.keep.rd,ha.keep.wr]; exact hr0) fun d kd ed =>
    wp_ldrx (by decide) (by rw [kd.get .x19,h19])
    (by rw [kd.rd,kd.wr,kc.rd,kc.wr,hb.rd,hb.wr,ha.keep.rd,ha.keep.wr]; exact hr1) fun u ku eu => wp_nil ?_
  refine ⟨((((ha.keep.trans hb.keep).trans kc).trans kd.keep).trans ku.keep).mono (by decide),
    ?_,?_,?_,?_,?_,?_⟩
  · rw [ku.mem,kd.mem]; exact frame
  · rw [ku.mem,kd.mem]; exact cc
  · rw [ku.mem,kd.mem]; exact Sample.reduced_of_coeffs cc
  · rw [ku.get .x24,kd.get .x24,kc.get .x24,eb,ha.keep.get .x24]
    apply congrArg (fun w : BitVec 64 => s.gpr .x24 &&& w)
    apply BitVec.eq_of_toNat_eq
    rw [ha.status]
    split <;> rfl
  · rw [ku.get .x22,ed]; exact flagsC.1
  · rw [eu,kd.mem]; exact flagsC.2

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! ### `MlKem.AArch64.Paired.Single`, which only this module used -/

section

/-! # Five complete SHAKE128 blocks in the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF iterF_succ)

def fullR (a : Addr) : Region := ⟨a,840⟩
def singleWrites (p a : Addr) : List Region := [pairR p,fullR a,X2.callR (p+1536)]
structure SingleInv (initial : State) (p a : Addr) (A B : Spec.Sha3.State) (k : Nat) (s : State) : Prop where
  keep : Keep singleRegs initial s
  pair : PairAt s.mem p (iterF k A) (iterF k B)
  ptr : s.gpr .x19=p
  pa : s.gpr .x20=blockAt a k
  count : (s.gpr .x22).toNat=5-k
  frame : Frame (singleWrites p a) initial.mem s.mem
  out : Blocks s.mem a k A

theorem single_block_sub (a : Addr) {j : Nat} (hj : j<5) :
    Region.Sub (rateR21 (blockAt a j)) (fullR a) := Offset.sub_base a (by omega_using [hj])

theorem single_ok {s : State} {p a : Addr} {A B : Spec.Sha3.State}
    (hp : s.gpr .x19=p) (ha : s.gpr .x20=a) (hcount : (s.gpr .x22).toNat=5)
    (pair : PairAt s.mem p A B)
    (hin : ∀i<21,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 8)
    (hout : ∀j<5,∀i<21,InRegions s.wr (outAddr (blockAt a j) i) 8)
    (hpa : (pairR p).Disjoint (fullR a))
    (hwa : (X2.callR (p+1536)).Disjoint (fullR a))
    (hpw : (pairR p).Disjoint (X2.callR (p+1536)))
    (hcov : Covers [pairR p,X2.callR (p+1536)] s.wr) :
    WP isa (.loop (singleBody sha3) (.nonzero .x .x22)) s (SingleInv s p a A B 5) := by
  apply count_loop (by decide : 0<5) (SingleInv s p a A B)
  · intro k hk t h
    refine WP.mono (singleStep_ok (sha3 := sha3) h.ptr h.pa h.pair
      (fun i hi => by rw [h.keep.rd,h.keep.wr]; exact hin i hi)
      (fun i hi => by rw [h.keep.wr]; exact hout k hk i hi)
      (hpa.sub_right (single_block_sub a hk)) hpw
      (by rw [h.keep.wr]; exact hcov)) fun u ⟨ku,pu,au,fu,ua,uc⟩ => ?_
    have count : (u.gpr .x22).toNat=5-(k+1) := by
      rw [uc,toNat_sub_n (by rw [h.count]; change 1≤5-k; omega_using [hk]),h.count]
      change 5-k-1=5-(k+1); omega_using []
    refine ⟨⟨(h.keep.trans ku).mono (by simp),?_,?_,?_,count,?_,?_⟩,by rw [count]; omega_using [hk]⟩
    · simpa only [iterF_succ] using pu
    · rw [ku.gpr .x19 (by decide),h.ptr]
    · rw [ua]; change a+BitVec.ofNat 64 (168*k)+BitVec.ofNat 64 168 = _
      rw [BitVec.add_assoc,← BitVec.ofNat_add]; congr 2
    · exact h.frame.trans (fu.sub (by
        intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact ⟨pairR p,by simp [singleWrites],fun _ h => h⟩
        · exact ⟨fullR a,by simp [singleWrites],single_block_sub a hk⟩
        · exact ⟨X2.callR (p+1536),by simp [singleWrites],fun _ h => h⟩))
    · intro j hj
      by_cases he : j=k
      · subst j; simpa only [iterF_succ] using au
      · have hjk : j<k := by omega_using [hj, he]
        intro i hi
        have hc : (rateR21 (blockAt a j)).Contains (outAddr (blockAt a j) i) 8 :=
          Offset.contains_base _ (by omega_using [hi]) (by omega_using [hi])
        rw [fu.readW hc (by
          intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact (hpa.sub_right (single_block_sub a (by omega_using [hk, hj]))).symm
          · exact Offset.disjoint a (Or.inl (by omega_using [hj, he])) (by omega_using [hk, hj]) (by omega_using [hk])
          · exact (hwa.sub_right (single_block_sub a (by omega_using [hk, hj]))).symm) (by decide)]
        exact h.out j hjk i hi
  · exact ⟨⟨fun _ _ => rfl,rfl,rfl,rfl,fun _ _ => rfl⟩,pair,hp,
      by simpa [blockAt] using ha,hcount,Frame.refl _ _,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Paired

end

end

/-! # The complete singleton fallback, including parser failure and saved flags -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/FullPrepare.lean`, which only this module imported.
section

/-! # Constants and complete-stream rejection entry for the singleton fallback -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def fullPrep (out : Nat) : List Instr := Rej8.rejConsts ++
  [.movz .x .x9 0 0,.str .x .x9 .x19 1240] ++ fullEntry 400 out

def prepWrites (p : Addr) : List Region := [⟨p+1408,8⟩,⟨p+1240,8⟩]
def prepRegs : List Reg := [.x2,.x3,.x4,.x5,.x9,.x10,.x16]

theorem fullPrep_ok {w16 : Bool} {s : State} {p out : Addr} {off : Nat} {B : Nat → Byte}
    (hoff : off<65536) (hp : s.gpr .x19=p) (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (bytes : ∀i<840,s.mem ((p+400)+BitVec.ofNat 64 i)=B i)
    (tab : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE"))
    (tr : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr))
    (ts : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨p,2048⟩)
    (to : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨out,1024⟩) :
    WP isa (.block (fullPrep off)) s fun u =>
      Keep prepRegs s u ∧ Frame (prepWrites p) s.mem u.mem ∧ Rej8.EntryW w16 [] 280 B (p+400) out u ∧ u.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  rw [fullPrep,List.append_assoc,WP.block_append_iff]
  refine WP.mono_syms (Rej8.constants_ok s (by rw [hp]; exact iw (by decide))) fun a ⟨ka,ca,ma,ta⟩ sa => ?_
  have fa : Frame (prepWrites p) s.mem a.mem := by
    rw [ma,hp]
    exact (Frame.refl _ _).writeW (r := ⟨p+1408,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have zero : WP isa (.block [.movz .x .x9 0 0,.str .x .x9 .x19 1240]) a fun c =>
      Keep [.x9] a c ∧ c.mem=a.mem.writeW (p+1240) (0 : BitVec 64) := by
    refine wp_movz fun b kb eb => wp_strx (a := p+1240) (by decide)
      (by rw [kb.get .x19,ka.get .x19,hp]; rfl)
      (by rw [kb.wr,ka.wr]; exact iw (by decide)) fun c kc => wp_nil ?_
    exact ⟨(kb.keep.trans kc.keep).mono (by decide),by rw [kc.mem,eb,kb.mem]; rfl⟩
  rw [WP.block_append_iff]
  refine WP.mono (WP.keepV (by decide) zero) fun c ⟨⟨kc,mc⟩,vc⟩ => ?_
  have pc : Keep [.x9,.x16] s c := (ka.trans kc).mono (by decide)
  have fc : Frame (prepWrites p) s.mem c.mem := by
    rw [mc]; exact fa.writeW (r := ⟨p+1240,8⟩) (by simp [prepWrites]) _ (Region.contains_self _ 8)
  have subs : ∀r∈prepWrites p,Region.Sub r ⟨p,2048⟩ := by
    intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> exact Offset.sub_base p (by decide)
  have cc : Rej8.Constants c := by
    have v : c.v=a.v := vc
    exact ⟨by rw [v]; exact ca.index,by rw [v]; exact ca.mask,
      by simpa only [v] using ca.q,by simpa only [v] using ca.weights,by simpa only [v] using ca.zero⟩
  have c16 : c.gpr .x16=s.syms "VG_MLKEM_REJ_SHUFFLE" := by rw [kc.get .x16,ta,sa]
  have ready : Rej8.TableReady c out := by
    refine ⟨?_,?_,?_⟩
    · rw [c16]; exact tab.frame fc (fun r hr => ts.sub_right (subs r hr))
    · rw [c16,pc.rd,pc.wr]; exact tr
    · rw [c16]; exact to
  have env : Rej8.EnvW w16 280 B (p+400) out c := rejection_envW (w16 := w16) (by decide) (by decide)
    (by rw [pc.wr]; exact hc) (by rw [pc.wr]; exact ho) hd
    (by
      intro i hi
      have hsep : ∀r∈prepWrites p,(Region.mk (p+400) 840).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      exact (fc.bytes hsep (by change 840≤2^64; decide) hi).trans (bytes i hi))
    (fun _ hm => ready.read hm) (fun _ hm => ready.artifact.vector hm) (fun _ hm => ready.disjoint hm)
  have env' : Rej8.EnvW w16 280 B (c.gpr .x19+400) (c.gpr .x28+BitVec.ofNat 64 off) c := by
    rw [pc.get .x19,pc.get .x28,hp,hout]; exact env
  refine WP.mono (fullEntry_ok c (by decide) hoff env' cc) fun u ⟨ku,eu⟩ => ?_
  refine ⟨(pc.trans ku.keep).mono (by decide),?_,?_,(ku.get .x16).trans c16⟩
  · rw [ku.mem]; exact fc
  · rw [pc.get .x19,pc.get .x28,hp,hout] at eu
    exact eu

end VG.Proof.MlKem.AArch64.Paired
end

end

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Paired/FullStart.lean`, which only this module imported.
section

/-! # Singleton fallback through all five SHAKE128 blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.Sha3 (iterF)

def fullStartRegs : List Reg := initRegs++singleRegs

theorem fullStart_ok {s initial : State} {p seed : Addr} {sb ss a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hp : s.gpr .x19=p) (hbase : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (hin : ∀j<4, InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr) (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (sv : Noise.Saved p initial s.mem) :
    WP isa (.seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
      (.loop (singleBody sha3) (.nonzero .x .x22))) s fun t =>
      Keep fullStartRegs s t ∧ Frame [⟨p,2048⟩] s.mem t.mem ∧ Noise.Saved p initial t.mem ∧ Flags p s t.mem ∧
      t.gpr .x19=p ∧ t.gpr .x22=0 ∧
      PairAt t.mem p (iterF 5 (seedState s.mem seed a k)) (iterF 5 (seedState s.mem seed a k)) ∧
      Blocks t.mem (p+400) 5 (seedState s.mem seed a k) := by
  have iw {o l : Nat} (h : o+l≤2048) := Noise.inScratch hc h (by decide)
  refine WP.seq (WP.mono (fullInit_ok hss hsb h8 hp hbase hseed hin hc hsep)
    fun u ⟨ku,fu,flags,h19,h20,_,h22,pair⟩ => ?_)
  have svu : Noise.Saved p initial u.mem := sv.frame fu (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint_base p (by decide) (by decide))
  refine WP.mono (single_ok (sha3 := sha3) h19 h20 (by rw [h22]; rfl) pair
    (fun i hi => by
      rw [ku.rd,ku.wr]; obtain ⟨r,hr,hh⟩ := iw (by omega_using [hi] : 16*i+8≤2048)
      exact ⟨r,List.mem_append_right _ hr,hh⟩)
    (fun j hj i hi => by
      rw [ku.wr]; change InRegions s.wr ((p+BitVec.ofNat 64 400+BitVec.ofNat 64 (168*j))+BitVec.ofNat 64 (8*i)) 8
      rw [BitVec.add_assoc,BitVec.add_assoc,← BitVec.ofNat_add,← BitVec.ofNat_add]
      exact iw (by omega_using [hj, hi]))
    (Offset.base_disjoint p (by decide) (by decide))
    (Offset.disjoint p (by decide) (by decide) (by decide))
    (Offset.base_disjoint p (by decide) (by decide))
    (by
      rw [ku.wr]
      have ha : Covers [pairR p] s.wr := by
        simpa only [BitVec.add_zero,pairR] using (Noise.coversScratch (off := 0) (len := 400) hc (by decide))
      exact Noise.coversTwo ha (Noise.coversScratch (off := 1536) (len := 136) hc (by decide)))) fun t ht => ?_
  refine ⟨ku.trans ht.keep,?_,?_,?_,ht.ptr,?_,ht.pair,ht.out⟩
  · have fi : Frame [⟨p,2048⟩] s.mem u.mem := fu.sub (by
      intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩)
    exact fi.trans (ht.frame.sub (by
      intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨⟨p,2048⟩,by simp,Region.sub_prefix (by decide : 400≤2048)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩
      · exact ⟨⟨p,2048⟩,by simp,Offset.sub_base p (by decide)⟩))
  · apply svu.frame ht.frame
    intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
  · apply flags.frame ht.frame
    intro r hr; simp only [singleWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Offset.disjoint_base p (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
    · exact Offset.disjoint p (by decide) (by decide) (by decide)
  · apply BitVec.eq_of_toNat_eq; exact ht.count

end VG.Proof.MlKem.AArch64.Paired
end

end

@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
variable {sha3 : Bool}
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.MlKem VG.Spec.MlKem

def fullSampleCode (sha3 : Bool) (sb ss off a k : Nat) (w16 : Bool := false) : Prog isa :=
  .seq (.block (Impl.MlKem.AArch64.Paired.fullInit sb ss a k))
    (.seq (.loop (singleBody sha3) (.nonzero .x .x22)) (.seq (.block (fullPrep off)) (fullFinish w16)))

theorem fullSample_eq (L : KemLay) (kg : Bool) (a : Nat) (w16 : Bool) :
    Impl.MlKem.AArch64.Paired.fullSample sha3 L kg a w16 =
      fullSampleCode sha3 (if kg then KG.SB else KEM.SB) (if kg then KG.SS else KEM.SS)
        ((if kg then KG.AH else KEM.AH)+1024*a) a L.k w16 := by
  simp only [Impl.MlKem.AArch64.Paired.fullSample,fullSampleCode,fullPrep,fullEntry,
    fullFinish,singleBody,singleWords,Rej8.zeroSuffix,Rej8.zeroBody,seqs,List.append_assoc]

def fullRegs : List Reg := fullStartRegs++prepRegs++fullFinishRegs

def fullWrites (p out : Addr) : List Region := [⟨p,2048⟩,polyRegion out]

structure FullPostW (w16 : Bool) (B : Nat → Byte) (p out : Addr) (initial s u : State) : Prop where
  keep : Keep fullRegs s u
  frame : Frame (fullWrites p out) s.mem u.mem
  saved : Noise.Saved p initial u.mem
  coeffs : CoeffsUpToW w16 u.mem out (sampleAfter [] B 280).length (Sample.cvW w16 (sampleAfter [] B 280)) (fun _ => 0)
  reduced : ReducedW (cw w16) u.mem out
  status : u.gpr .x24=s.gpr .x24 &&& BitVec.ofNat 64 (if (sampleAfter [] B 280).length=256 then 1 else 0)
  flag22 : u.gpr .x22=s.gpr .x22
  flag23 : u.gpr .x23=s.gpr .x23
  ptr : u.gpr .x19=p

theorem fullSampleCode_ok {w16 : Bool} {s initial : State} {p seed out : Addr} {sb ss off a k : Nat}
    (hss : ss<4096) (hsb : sb+32≤32768) (h8 : sb%8=0) (hoff : off<65536)
    (hk : 0<k) (hk256 : k≤256)
    (hp : s.gpr .x19=p) (hbase : s.gpr .x28+BitVec.ofNat 64 ss=p)
    (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed) (hout : s.gpr .x28+BitVec.ofNat 64 off=out)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hc : Covers [⟨p,2048⟩] s.wr) (ho : Covers [⟨out,1024⟩] s.wr)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (hd : (Region.mk p 2048).Disjoint ⟨out,1024⟩)
    (sv : Noise.Saved p initial s.mem)
    (tab : Rej8.TableArtifact s.mem (s.syms "VG_MLKEM_REJ_SHUFFLE"))
    (tr : Covers [⟨s.syms "VG_MLKEM_REJ_SHUFFLE",4096⟩] (s.rd++s.wr))
    (ts : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨p,2048⟩)
    (to : (Region.mk (s.syms "VG_MLKEM_REJ_SHUFFLE") 4096).Disjoint ⟨out,1024⟩) :
    WP isa (fullSampleCode sha3 sb ss off a k w16) s
      (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s) := by
  have combined := WP.mono_syms (fullStart_ok (sha3 := sha3) (a := a) (k := k) hss hsb h8 hp hbase hseed hin hc hsep sv)
    (R := fun b => WP isa (.seq (.block (fullPrep off)) (fullFinish w16)) b
      (FullPostW w16 (xofByte (seedBytes s.mem seed a k)) p out initial s))
    (fun b ⟨kb,fb,svb,flagsb,b19,_,_,blocks⟩ sy => by
      refine WP.seq (WP.mono (fullPrep_ok (w16 := w16) hoff b19
        (by rw [kb.get .x28]; exact hout) (by rw [kb.wr]; exact hc) (by rw [kb.wr]; exact ho) hd
        (fun i hi => blocks.xof hk hk256 hi)
        (by rw [sy]; exact tab.frame fb (by simpa using ts))
        (by rw [sy,kb.rd,kb.wr]; exact tr) (by rw [sy]; exact ts) (by rw [sy]; exact to)) fun c ⟨kc,fc,entry,_⟩ => ?_)
      have prepSub : ∀r∈prepWrites p,Region.Sub r ⟨p,2048⟩ := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.sub_base p (by decide)
      have prepFlag : ∀r∈prepWrites p,(flagR p).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      have prepSaved : ∀r∈prepWrites p,(Noise.savedR p).Disjoint r := by
        intro r hr; simp only [prepWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl <;> exact Offset.disjoint p (by decide) (by decide) (by decide)
      have cf := flagsb.frame fc prepFlag
      have cs := svb.frame fc prepSaved
      have flagOut : (flagR p).Disjoint (polyRegion out) :=
        hd.sub_left (Offset.sub_base p (by decide))
      have savedOut : (Noise.savedR p).Disjoint (polyRegion out) :=
        hd.sub_left (Offset.sub_base p (by decide))
      have read {off : Nat} (fit : off+8≤2048) : InRegions (c.rd++c.wr) (p+BitVec.ofNat 64 off) 8 := by
        rw [kc.rd,kc.wr,kb.rd,kb.wr]
        obtain ⟨r,hr,hh⟩ := Noise.inScratch hc fit (by decide)
        exact ⟨r,List.mem_append_right _ hr,hh⟩
      refine WP.mono (fullFinish_ok entry (by rw [kc.get .x19,b19]) cf flagOut
        (read (by decide)) (read (by decide))) fun u hu => ?_
      refine ⟨?_,?_,cs.frame hu.frame (by simpa using savedOut),hu.coeffs,hu.reduced,?_,hu.flag22,hu.flag23,?_⟩
      · exact ((kb.trans kc).trans hu.keep).mono (by simp [fullRegs,List.append_assoc])
      · have first : Frame (fullWrites p out) s.mem b.mem := fb.mono (by simp [fullWrites])
        have second : Frame (fullWrites p out) b.mem c.mem := fc.sub (fun r hr =>
          ⟨⟨p,2048⟩,by simp [fullWrites],prepSub r hr⟩)
        exact (first.trans second).trans (hu.frame.mono (by simp [fullWrites]))
      · rw [hu.status,kc.get .x24,kb.get .x24]
      · rw [hu.keep.get .x19,kc.get .x19,b19])
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun b hb => WP.seq hb)

end VG.Proof.MlKem.AArch64.Paired
