module

public import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.BoundedFour
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourInitWord
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourBatchGeometry
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFlagValue
import VerifiedGarbage.Proof.MlDsa.AArch64.Arith.Basic
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.AArch64.Exec
import VerifiedGarbage.Proof.Sha3.AArch64.Sums
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `MlDsa.AArch64.Optimized.BoundedFourMaskInit`, which only this module used -/

section

/-! ## From `BoundedFourMaskLoop.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

theorem maskGuard {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) :
    isa.eval (.nonzero .x .x5) s=some (decide (j<64)) := by
  rw [eval_nonzero,hi.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega_using [])]
  congr 1
  apply decide_eq_decide.mpr
  have:=hi.bound
  omega_using []

theorem maskLoop_ok {σ s : State} {p : Addr} {v : BitVec 128} {j : Nat}
    (hi : MaskInv σ s p v j) (hj : j<64)
    (hr : ∀i<64,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5)) s
      (fun t=>MaskInv σ t p v 64) := by
  refine WP.loop (M := isa) (fun rank s=>∃j,rank=64-j ∧MaskInv σ s p v j ∧j<64)
    ?_ (64-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (maskStep_ok hi hj hr hw) fun t ht=>?_
  have hg:=maskGuard ht
  by_cases hn : j+1<64
  · exact .inr ⟨by rw [hg,decide_eq_true hn],64-(j+1),by omega_using [hj],j+1,rfl,ht,hn⟩
  · have he : j+1=64 := by omega_using [hj, hn]
    exact .inl ⟨by rw [hg,decide_eq_false hn],by rw [←he]; exact ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64
open VG.Proof.MlKem.AArch64

def outputMask (x : BitVec 64) : BitVec 128 := if x=0#64 then ~~~0#128 else 0#128

def maskScalar : List Instr :=
 [.subImm .x .x4 .x4 1,.lsr .x .x4 .x4 63,.movz .x .x6 0 0,.sub .w .x4 .x6 .x4]

theorem maskScalar_ok (s : State) (hx : (s.gpr .x4).toNat≤256) :
    WP isa (.block maskScalar) s fun t=>
      ((t.gpr .x4=(if s.gpr .x4=0#64 then 4294967295#64 else 0#64) ∧t.mem=s.mem) ∧
        Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskScalar
  arun
  have h:=ResidentRej.smallFlag_status (s.gpr .x4) (by omega_using [hx])
  rw [h]
  by_cases hz : s.gpr .x4=0#64
  · simp only [ite_eq_left hz]
    rfl
  · simp only [ite_eq_right hz]
    rfl

def maskFooter (k : Nat) : List Instr :=
 [.addImm .x .x3 .x21 (1024*k),.movz .x .x5 64 0]

theorem maskFooter_ok (s : State) {k : Nat} (hk : k<4) :
    WP isa (.block (maskFooter k)) s fun t=>
      ((t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧t.mem=s.mem) ∧
        Keep [.x3,.x5] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold maskFooter
  have hb : 1024*k<4096 := by omega_using [hk]
  arun [hb]


def maskLoadScalar (k : Nat) : List Instr := .ldr .x .x4 .x19 (7904+8*k)::maskScalar

theorem maskLoadScalar_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskLoadScalar k)) s fun t=>
      ((t.gpr .x4=(if s.mem.readW (countAt b k) 64=0#64 then 4294967295#64 else 0#64) ∧
        t.mem=s.mem) ∧Keep [.x4,.x6] s t) ∧t.v=s.v := by
  apply WP.keepV (by rfl)
  unfold maskLoadScalar
  refine wp_ldrx (by omega_using [hk]) (by rw [hb]; rfl) hr fun a ha h4=>?_
  refine WP.mono (maskScalar_ok a (by rw [h4]; exact hx)) fun t ⟨⟨⟨hv,hm⟩,ht⟩,_⟩=>?_
  exact ⟨⟨by rw [hv,h4],hm.trans ha.mem⟩,(ha.keep.trans ht).mono (by decide)⟩

def maskSetup (k : Nat) : List Instr := maskLoadScalar k ++
 [.vop (.dup .s4 .v0 .x4)]++maskFooter k

theorem maskSetup_ok {s : State} {k : Nat} (hk : k<4) {b : Addr}
    (hb : s.gpr .x19=b) (hr : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256) :
    WP isa (.block (maskSetup k)) s fun t=>
      InitKeep [.x3,.x4,.x5,.x6] [.v0] s t ∧
      t.gpr .x3=s.gpr .x21+BitVec.ofNat 64 (1024*k) ∧t.gpr .x5=64#64 ∧
      t.v .v0=outputMask (s.mem.readW (countAt b k) 64) := by
  unfold maskSetup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (maskLoadScalar_ok hk hb hr hx) fun a ⟨⟨⟨h4,hm⟩,ha⟩,hv⟩=>?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v0) rfl fun c hc=>?_
  refine WP.mono (maskFooter_ok c hk) fun t ⟨⟨⟨hp,h5,htm⟩,ht⟩,htv⟩=>?_
  refine ⟨?_,?_,h5,?_⟩
  · refine ⟨((ha.trans (hc.keep (by decide))).trans ht).mono (by decide),?_,?_⟩
    · rw [htm,hc.mem,hm]
    · intro r hr
      rw [htv,hc.other r (by simpa using hr),hv]
  · rw [hp,hc.gpr,ha.get .x21]
  · rw [htv,hc.v,h4]
    unfold outputMask
    split <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

end

end


/-! ## From `BoundedFourMaskOne.lean` -/

@[expose] public section

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

theorem maskOne_ok {s : State} {k : Nat} (hk : k<4) {b p : Addr}
    (hb : s.gpr .x19=b) (hp : s.gpr .x21+BitVec.ofNat 64 (1024*k)=p)
    (hc : InRegions (s.rd++s.wr) (countAt b k) 8)
    (hx : (s.mem.readW (countAt b k) 64).toNat≤256)
    (hr : ∀i<64,InRegions (s.rd++s.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<64,InRegions s.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>
      Keep [.x3,.x4,.x5,.x6] s t ∧
      (∀r,r∉[VReg.v0,.v1]→t.v r=s.v r) ∧Frame [polyR p] s.mem t.mem ∧
      (s.mem.readW (countAt b k) 64=0#64→t.mem=s.mem) ∧
      (s.mem.readW (countAt b k) 64≠0#64→∀i<256,coeffAt t.mem p i=0#32) := by
  change WP isa (.seq (.block (maskSetup k))
    (.loop (.block (maskGroup++maskAdvance)) (.nonzero .x .x5))) s _
  refine WP.seq (WP.mono (maskSetup_ok hk hb hc hx) fun a ⟨ha,hp',h5,hv⟩=>?_)
  let v:=outputMask (s.mem.readW (countAt b k) 64)
  have hi : MaskInv a a p v 0 := by
    refine ⟨by decide,Keep.refl _ _,fun _ _=>rfl,rfl,?_,h5,hv⟩
    change a.gpr .x3=p+0#64
    rw [BitVec.add_zero]
    exact hp'.trans hp
  refine WP.mono (maskLoop_ok hi (by decide)
    (fun i hi=>by rw [ha.keep.rd,ha.keep.wr]; exact hr i hi)
    (fun i hi=>by rw [ha.keep.wr]; exact hw i hi)) fun t ht=>?_
  refine ⟨(ha.keep.trans ht.keep).mono (by decide),?_,?_,?_,?_⟩
  · intro r h
    rw [ht.vec r (by simpa using fun he=>h (by simp [he])),ha.vec r (fun he=>h (by simp_all))]
  · rw [ht.mem,ha.mem]
    exact maskRun_frame _ _ _ (by decide)
  · intro hz
    rw [ht.mem,ha.mem]
    change maskRun s.mem p (outputMask _) 64=s.mem
    rw [outputMask,ite_eq_left hz,maskRun_identity]
  · intro hz i hi
    rw [ht.mem,ha.mem]
    change coeffAt (maskRun s.mem p (outputMask _) 64) p i=0#32
    rw [outputMask,ite_eq_right hz]
    exact maskRun_zero (by decide) i hi

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskRows.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlKem.AArch64

def maskedWord (m : Mem) (b p : Addr) (i j : Nat) : BitVec 32 :=
 if m.readW (countAt b i) 64=0#64 then coeffAt m (outputAt p i) j else 0#32

structure MaskRows (σ s : State) (b p : Addr) (k : Nat) : Prop where
 keep : Keep [.x3,.x4,.x5,.x6] σ s
 frame : Frame [⟨p,4096⟩] σ.mem s.mem
 counts : ∀i<4,s.mem.readW (countAt b i) 64=σ.mem.readW (countAt b i) 64
 words : ∀i<4,∀j<256,coeffAt s.mem (outputAt p i) j=
   if i<k then maskedWord σ.mem b p i j else coeffAt σ.mem (outputAt p i) j

theorem maskRows_zero (s : State) (b p : Addr) : MaskRows s s b p 0 :=
 ⟨Keep.refl _ _,Frame.refl _ _,fun _ _=>rfl,by intro i hi j hj; simp⟩

theorem maskRows_step {σ s : State} {b p : Addr} {k : Nat} (hk : k<4)
    (hs : MaskRows σ s b p k) (hb : σ.gpr .x19=b) (hp : σ.gpr .x21=p)
    (hbound : ∀i<4,(σ.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (σ.rd++σ.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (σ.rd++σ.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions σ.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (polyR (outputAt p j))) :
    WP isa (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne k) s fun t=>MaskRows σ t b p (k+1) := by
  refine WP.mono (maskOne_ok (s := s) (b := b) (p := outputAt p k) hk (by rw [hs.keep.get .x19]; exact hb)
    (by rw [hs.keep.get .x21,hp]; rfl)
    (by rw [hs.keep.rd,hs.keep.wr]; exact hrc k hk)
    (by rw [hs.counts k hk]; exact hbound k hk)
    (fun j hj=>by rw [hs.keep.rd,hs.keep.wr]; exact hr k hk j hj)
    (fun j hj=>by rw [hs.keep.wr]; exact hw k hk j hj)) fun t ⟨ht,_,hf,hyes,hno⟩=>?_
  refine ⟨(hs.keep.trans ht).mono (by decide),hs.frame.trans (hf.sub (fun r hr=>by
    rw [List.mem_singleton.mp hr]; exact ⟨_,by simp,outputAt_sub p hk⟩)),?_,?_⟩
  · intro i hi
    rw [hf.readW (Region.contains_self _ _) (fun r hr=>by rw [List.mem_singleton.mp hr]; exact hsep i hi k hk) (by decide)]
    exact hs.counts i hi
  · intro i hi j hj
    by_cases hik : i=k
    · subst i
      rw [ite_eq_left (by omega_using [])]
      unfold maskedWord
      by_cases hz : σ.mem.readW (countAt b k) 64=0#64
      · rw [ite_eq_left hz,hyes (by rw [hs.counts k hk]; exact hz),hs.words k hk j hj,ite_eq_right (by omega_using [])]
      · rw [ite_eq_right hz]
        exact hno (by rw [hs.counts k hk]; exact hz) j hj
    · have hframe : coeffAt t.mem (outputAt p i) j=coeffAt s.mem (outputAt p i) j := by
        unfold coeffAt
        apply hf.readW
          (Offset.contains_base (outputAt p i) (by omega_using [hj] : 4*j+4≤1024) (by omega_using [hj]))
          (fun r hr=>by rw [List.mem_singleton.mp hr]; exact outputs_apart p hi hk hik) (by decide)
      rw [hframe,hs.words i hi j hj]
      by_cases hlt : i<k
      · rw [ite_eq_left hlt,ite_eq_left (by omega_using [hlt])]
      · rw [ite_eq_right hlt,ite_eq_right (by omega_using [hik, hlt])]

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end

/-! ## From `BoundedFourMaskFour.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.BoundedFour
open VG VG.AArch64

def maskFour : Prog isa :=
 .seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 0)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 1)
 (.seq (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 2)
       (Impl.MlDsa.AArch64.Optimized.BoundedFour.maskOne 3)))

theorem maskFour_ok {s : State} {b p : Addr} (hb : s.gpr .x19=b) (hp : s.gpr .x21=p)
    (hbound : ∀i<4,(s.mem.readW (countAt b i) 64).toNat≤256)
    (hrc : ∀i<4,InRegions (s.rd++s.wr) (countAt b i) 8)
    (hr : ∀i<4,∀j<64,InRegions (s.rd++s.wr) (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hw : ∀i<4,∀j<64,InRegions s.wr (outputAt p i+BitVec.ofNat 64 (16*j)) 16)
    (hsep : ∀i<4,∀j<4,(⟨countAt b i,8⟩ : Region).Disjoint (Proof.MlDsa.Sample.polyR (outputAt p j))) :
    WP isa maskFour s (fun t=>MaskRows s t b p 4) := by
  unfold maskFour
  refine WP.seq (WP.mono (maskRows_step (by decide) (maskRows_zero s b p) hb hp hbound hrc hr hw hsep) fun a ha=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) ha hb hp hbound hrc hr hw hsep) fun b hb'=>?_)
  refine WP.seq (WP.mono (maskRows_step (by decide) hb' hb hp hbound hrc hr hw hsep) fun c hc=>?_)
  exact maskRows_step (by decide) hc hb hp hbound hrc hr hw hsep

end VG.Proof.MlDsa.AArch64.Optimized.BoundedFour

end
