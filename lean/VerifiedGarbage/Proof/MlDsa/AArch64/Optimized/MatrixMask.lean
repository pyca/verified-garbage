import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResponseAdd
import VerifiedGarbage.Impl.MlDsa.AArch64.Optimized.MatrixMask
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskStep
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskMemory
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.BoundedFourMaskInit
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.Blocks

/-! ## From `MatrixMaskGroup.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)

def maskMem (m : Mem) (p : Addr) (v : BitVec 128) : Mem :=
 m.write p 16 (m.read p 16 &&& v)

theorem group_ok {s : State} {i : Nat} (hi : i<4)
    (hr : InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block (group i)) s fun t=>
      StepKeep [.v1] s t ∧ t.mem=maskMem s.mem (s.gpr .x1+BitVec.ofNat 64 (16*i)) (s.v .v0) := by
  unfold group
  refine wp_ldrq (by omega) rfl hr fun a ha=>?_
  refine wp_vop (d := .v1) rfl fun b hb=>?_
  have hk : VChg [.v1] s b := (ha.chg.trans hb.chg).mono (by decide)
  refine wp_strq (a := s.gpr .x1+BitVec.ofNat 64 (16*i)) (by omega) (by rw [hk.gpr]) (by rw [hk.wr]; exact hw) fun t ht=>wp_nil ?_
  refine ⟨((StepKeep.ofChg hk (by decide)).trans (StepKeep.ofMem ht)).mono (by decide),?_⟩
  rw [ht.mem,hk.mem,hb.v,ha.v,ha.get .v0]
  rfl

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end

/-! ## From `MatrixMaskBody.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.AArch64.Optimized.Response (StepKeep)
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem groups_ok {s : State}
    (hr : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block ((List.range 4).flatMap group)) s fun t =>
      StepKeep [.v1] s t ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) 4 := by
  refine wp_range_flatMap (M := isa) (N := 4)
    (fun j t => StepKeep [.v1] s t ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) j)
    (fun j t hj ht => ?_) 4 (by omega) s ⟨⟨Keep.refl [] s,fun _ _ => rfl⟩,rfl⟩
  refine WP.mono (group_ok hj (by rw [ht.1.keep.rd,ht.1.keep.wr,ht.1.keep.get .x1]; exact hr j hj)
    (by rw [ht.1.keep.wr,ht.1.keep.get .x1]; exact hw j hj)) fun u ⟨hu,hm⟩ => ?_
  refine ⟨(ht.1.trans hu).mono (by decide),?_⟩
  rw [hm,ht.2,ht.1.keep.get .x1,ht.1.vec .v0 (by decide)]
  rfl

theorem advance_ok (s : State) : WP isa (.block advance) s fun t =>
    ((t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x2=s.gpr .x2-1 ∧ t.mem=s.mem) ∧
      Keep [.x1,.x2] s t) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold advance
  arun
  exact ⟨rfl,rfl⟩

theorem body_ok {s : State}
    (hr : ∀i<4,InRegions (s.rd++s.wr) (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4,InRegions s.wr (s.gpr .x1+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block body) s fun t => Keep [.x1,.x2] s t ∧
      (∀r,r≠.v1→t.v r=s.v r) ∧ t.mem=maskRun s.mem (s.gpr .x1) (s.v .v0) 4 ∧
      t.gpr .x1=s.gpr .x1+64 ∧ t.gpr .x2=s.gpr .x2-1 := by
  rw [body,WP.block_append_iff]
  refine WP.mono (groups_ok hr hw) fun a ⟨ha,hm⟩ => ?_
  refine WP.mono (advance_ok a) fun t ⟨⟨⟨hp,hc,hmem⟩,hk⟩,hv⟩ => ?_
  exact ⟨(ha.keep.trans hk).mono (by decide),fun r hn => by
    rw [hv,ha.vec r (by simpa using hn)],hmem.trans hm,
    by rw [hp,ha.keep.get .x1],by rw [hc,ha.keep.get .x2]⟩

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end

/-! ## From `MatrixMaskLoop.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem maskRun_add (m : Mem) (p : Addr) (v : BitVec 128) (n k : Nat) :
    maskRun (maskRun m p v n) (p+BitVec.ofNat 64 (16*n)) v k=maskRun m p v (n+k) := by
  induction k with
  | zero => simp only [maskRun,Nat.add_zero]
  | succ k ih =>
    rw [maskRun,ih,show n+(k+1)=(n+k)+1 by omega,maskRun]
    simp only [Nat.mul_add,BitVec.ofNat_add,BitVec.add_assoc]

structure LoopInv (σ s : State) (p : Addr) (v : BitVec 128) (N j : Nat) : Prop where
  bound : j≤N
  keep : Keep [.x1,.x2] σ s
  vec : ∀r,r≠.v1→s.v r=σ.v r
  mem : s.mem=maskRun σ.mem p v (4*j)
  ptr : s.gpr .x1=p+BitVec.ofNat 64 (64*j)
  count : s.gpr .x2=BitVec.ofNat 64 (N-j)
  mask : s.v .v0=v

theorem step_ok {σ s : State} {p : Addr} {v : BitVec 128} {N j : Nat}
    (hi : LoopInv σ s p v N j) (hj : j<N) (_hN : N≤64)
    (hr : ∀i<4*N,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4*N,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.block body) s (fun t => LoopInv σ t p v N (j+1)) := by
  have addr k : s.gpr .x1+BitVec.ofNat 64 (16*k)=p+BitVec.ofNat 64 (16*(4*j+k)) := by
    rw [hi.ptr,BitVec.add_assoc,←BitVec.ofNat_add]
    rw [show 64*j+16*k=16*(4*j+k) by omega]
  refine WP.mono (body_ok (fun k hk => by rw [hi.keep.rd,hi.keep.wr,addr]; exact hr _ (by omega))
    (fun k hk => by rw [hi.keep.wr,addr]; exact hw _ (by omega))) fun t ⟨ht,hv,hm,hp,hc⟩ => ?_
  refine ⟨by omega,(hi.keep.trans ht).mono (by decide),fun r hn => (hv r hn).trans (hi.vec r hn),?_,?_,?_,?_⟩
  · rw [hm,hi.mem,hi.mask,hi.ptr,show 64*j=16*(4*j) by omega,maskRun_add]
    congr 1
  · rw [hp,hi.ptr,BitVec.add_assoc]
    change p+(BitVec.ofNat 64 (64*j)+BitVec.ofNat 64 64)=_
    rw [←BitVec.ofNat_add]
    congr 1
  · rw [hc,hi.count]
    change BitVec.ofNat 64 (N-j)-BitVec.ofNat 64 1=_
    rw [BitVec.ofNat_sub_ofNat_of_le (N-j) 1 (by decide) (by omega)]
    congr 1
  · rw [hv .v0 (by decide),hi.mask]

theorem loop_ok {σ s : State} {p : Addr} {v : BitVec 128} {N j : Nat}
    (hi : LoopInv σ s p v N j) (hj : j<N) (hN : N≤64)
    (hr : ∀i<4*N,InRegions (σ.rd++σ.wr) (p+BitVec.ofNat 64 (16*i)) 16)
    (hw : ∀i<4*N,InRegions σ.wr (p+BitVec.ofNat 64 (16*i)) 16) :
    WP isa (.loop (.block body) (.nonzero .x .x2)) s (fun t => LoopInv σ t p v N N) := by
  refine WP.loop (M := isa) (fun rank s => ∃j,rank=N-j ∧ LoopInv σ s p v N j ∧ j<N)
    ?_ (N-j) s ⟨j,rfl,hi,hj⟩
  rintro rank s ⟨j,rfl,hi,hj⟩
  refine WP.mono (step_ok hi hj hN hr hw) fun t ht => ?_
  have hg : isa.eval (.nonzero .x .x2) t=some (decide (j+1<N)) := by
    rw [eval_nonzero,ht.count,ne_zero_iff,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    congr 1
    apply decide_eq_decide.mpr
    have := ht.bound
    omega
  by_cases hn : j+1<N
  · exact .inr ⟨by rw [hg,decide_eq_true hn],N-(j+1),by omega,j+1,rfl,ht,hn⟩
  · have he : j+1=N := by omega
    exact .inl ⟨by rw [hg,decide_eq_false hn],by simpa only [he] using ht⟩

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end

/-! ## From `MatrixMaskMemory.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Arith.Neon
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun maskMem)

theorem coeffAt_write16_1024 (m : Mem) (p : Addr) {j : Nat} (hj : j+4≤1024)
    (v : BitVec 128) {i : Nat} (hi : i<1024) :
    coeffAt (m.write (coeffAddr p j) 16 v) p i =
      if j≤i ∧ i<j+4 then vword v (i-j) else coeffAt m p i := by
  split
  · rename_i h
    rw [coeffAt_eq,show coeffAddr p i=coeffAddr p j+BitVec.ofNat 64 (4*(i-j)) by
      unfold coeffAddr
      rw [BitVec.add_assoc,←BitVec.ofNat_add,show 4*j+4*(i-j)=4*i by omega]]
    exact readW_write16 _ _ _ (by omega)
  · have hw : m.write (coeffAddr p j) 16 v=m.writeW (coeffAddr p j) v := by
      simp only [Mem.writeW,BitVec.setWidth_eq]
    rw [hw]
    exact Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide)

theorem maskRun_zero {m : Mem} {p : Addr} {n : Nat} (hn : n≤256) :
    ∀i<4*n,coeffAt (maskRun m p 0#128 n) p i=0#32 := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [maskRun,BoundedFour.maskMem,BitVec.and_zero]
    have hp : p+BitVec.ofNat 64 (16*n)=coeffAddr p (4*n) := by
      unfold coeffAddr
      congr 2
      omega
    rw [hp,coeffAt_write16_1024 _ _ (by omega) _ (by omega)]
    split
    · simp [vword]
    · exact ih (by omega) i (by omega)

theorem maskRun_frame (m : Mem) (p : Addr) (v : BitVec 128) {n N : Nat}
    (hn : n≤4*N) (hN : N≤64) : Frame [⟨p,64*N⟩] m (maskRun m p v n) := by
  induction n with
  | zero => exact Frame.refl _ _
  | succ n ih =>
    unfold maskRun BoundedFour.maskMem
    exact (ih (by omega)).write (List.mem_singleton_self _) _
      (by simpa only [BitVec.add_zero] using (Offset.contains p (d := 16*n) (e := 0) (n := 16) (k := 64*N)
        (by omega) (by omega) (by omega)))

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end

/-! ## From `MatrixMaskInit.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr lea)
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (InitKeep)

abbrev scalar : List Instr := [.movz .x .x8 0 0,.sub .w .x8 .x8 .x0]
def footer (a : Ptr) (N : Nat) : List Instr := lea .x1 a.1 a.2 ++ [.movz .x .x2 (BitVec.ofNat 16 N) 0]
def setup (a : Ptr) (N : Nat) : List Instr := scalar ++ [.vop (.dup .s4 .v0 .x8)] ++ footer a N

def resultMask (s : State) : BitVec 128 :=
  if (s.gpr .x0).setWidth 32=1 then ~~~0#128 else 0#128

theorem scalar_ok (s : State) : WP isa (.block scalar) s fun t =>
    ((t.gpr .x8=((0#32-(s.gpr .x0).setWidth 32).setWidth 64) ∧ t.mem=s.mem) ∧
      Keep [.x8] s t) ∧ t.v=s.v := by
  apply WP.keepV (by rfl)
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl) (hv := rfl)
  unfold scalar
  arun
  rfl

theorem footer_ok {s : State} {a : Ptr} (ha : a.1∈VG.Proof.MlDsa.AArch64.keptRegs)
    {N : Nat} (hN : N<65536) : WP isa (.block (footer a N)) s fun t =>
    ((t.gpr .x1=pa s a ∧ t.gpr .x2=BitVec.ofNat 64 N ∧ t.mem=s.mem) ∧
      Keep [.x1,.x2,.x9] s t) ∧ t.v=s.v := by
  apply WP.keepV (by
    unfold footer lea
    split
    · rfl
    · unfold Impl.MlDsa.AArch64.Call.movV
      split <;> rfl)
  unfold footer
  have h1 : a.1≠.x1 := by intro h; rw [h] at ha; revert ha; decide
  refine VG.Proof.MlDsa.AArch64.lea_ok h1.symm a.2 fun b hb hp => ?_
  refine wp_movz fun t ht hc => wp_nil ?_
  refine ⟨⟨by rw [ht.get .x1,hp],?_,ht.mem.trans hb.mem⟩,(hb.keep.trans ht.keep).mono (by simp)⟩
  rw [hc]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat]
  omega

theorem setup_ok {s : State} {a : Ptr} (ha : a.1∈VG.Proof.MlDsa.AArch64.keptRegs)
    {N : Nat} (hN : N<65536) (hr : (s.gpr .x0).setWidth 32=0 ∨ (s.gpr .x0).setWidth 32=1) :
    WP isa (.block (setup a N)) s fun t =>
      InitKeep [.x1,.x2,.x8,.x9] [.v0] s t ∧ t.gpr .x1=pa s a ∧
      t.gpr .x2=BitVec.ofNat 64 N ∧ t.v .v0=resultMask s := by
  unfold setup
  rw [List.append_assoc,WP.block_append_iff]
  refine WP.mono (scalar_ok s) fun b ⟨⟨⟨h8,hm⟩,hb⟩,hv⟩ => ?_
  simp only [List.cons_append,List.nil_append]
  refine wp_vop (d := .v0) rfl fun c hc => ?_
  refine WP.mono (footer_ok ha hN) fun t ⟨⟨⟨hp,h2,htm⟩,ht⟩,htv⟩ => ?_
  refine ⟨⟨((hb.trans (hc.keep (by decide))).trans ht).mono (by decide),?_,?_⟩,?_,h2,?_⟩
  · rw [htm,hc.mem,hm]
  · intro r hr
    rw [htv,hc.other r (by simpa using hr),hv]
  · have h8 : a.1∉[Reg.x8] := by
      intro h; rw [List.mem_singleton.mp h] at ha; revert ha; decide
    rw [hp,pa,hc.gpr,hb.get a.1 h8]
  · rw [htv,hc.v,h8]
    unfold resultMask
    rcases hr with h | h <;> rw [h] <;> rfl

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end

/-! ## From `MatrixMask.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.MatrixMask
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Proof.MlKem.AArch64
open VG.Impl.MlDsa.AArch64.Call (Ptr)
open VG.Impl.MlDsa.AArch64.Optimized.MatrixMask
open VG.Proof.MlDsa.AArch64.Optimized.BoundedFour (maskRun)

theorem mask_ok {S : Nat} {rbs wbs : List (Reg × Nat)} {s : State}
    (L : Lay S rbs wbs s) {a : Ptr} {N : Nat} (hpos : 0<N) (hN : N≤64)
    (hw : inB wbs a (64*N)=true) (hin : inB (rbs++wbs) a (64*N)=true)
    (hr : (s.gpr .x0).setWidth 32=0 ∨ (s.gpr .x0).setWidth 32=1) :
    WP isa (code a (16*N)) s fun t => PPostB S s t [(a,64*N)] ∧
      Keep [.x1,.x2,.x8,.x9] s t ∧ ∀i<16*N,coeffAt t.mem (pa s a) i=
        if (s.gpr .x0).setWidth 32=1 then coeffAt s.mem (pa s a) i else 0 := by
  have hcode : code a (16*N)=.seq (.block (setup a N)) (.loop (.block body) (.nonzero .x .x2)) := by
    simp only [code,setup,scalar,footer,Nat.mul_div_cancel_left _ (by decide : 0<16),List.append_assoc]
    rfl
  rw [hcode]
  apply WP.seq
  refine WP.mono (setup_ok (L.ptrBs hin) (by omega) hr) fun u ⟨hu,hp,hc,hv⟩ => ?_
  have hr' i (hi : i<4*N) : InRegions (u.rd++u.wr) (pa s a+BitVec.ofNat 64 (16*i)) 16 := by
    rw [hu.keep.rd,hu.keep.wr]
    exact VG.Proof.MlKem.AArch64.in_rd_wr (inRegions_sub (L.inW hw) (by omega) (by omega))
  have hw' i (hi : i<4*N) : InRegions u.wr (pa s a+BitVec.ofNat 64 (16*i)) 16 := by
    rw [hu.keep.wr]
    exact inRegions_sub (L.inW hw) (by omega) (by omega)
  have hi : LoopInv u u (pa s a) (resultMask s) N 0 :=
    ⟨by omega,Keep.refl _ _,fun _ _ => rfl,rfl,by simpa using hp,by simpa using hc,hv⟩
  refine WP.mono (loop_ok hi hpos hN hr' hw') fun t ht => ?_
  have hk : Keep [.x1,.x2,.x8,.x9] s t := (hu.keep.trans ht.keep).mono (by decide)
  have hm : t.mem=maskRun s.mem (pa s a) (resultMask s) (4*N) := by rw [ht.mem,hu.mem]
  have hf : Frame [⟨pa s a,64*N⟩] s.mem t.mem := by
    rw [hm]
    exact maskRun_frame _ _ _ (Nat.le_refl _) hN
  refine ⟨postB_of_keep hk (by decide) hf,hk,?_⟩
  intro i hi
  rw [hm]
  rcases hr with h | h
  · simp only [resultMask,h]
    exact maskRun_zero (by omega) i (by omega)
  · simp only [resultMask,h,ite_true,BoundedFour.maskRun_identity]

end VG.Proof.MlDsa.AArch64.Optimized.MatrixMask

end
