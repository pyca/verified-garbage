module

public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Start
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.NextBlock
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Initial
public import VerifiedGarbage.Proof.MlKem.AArch64.Paired.Resume
public import VerifiedGarbage.Proof.MlKem.AArch64.Rej8Constants

/-! # Initialize and parse the first three paired matrix blocks -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Paired
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def beginCode (sb ss a b k oa ob : Nat) (w16 : Bool := false) : Prog isa :=
 .seq (.block (Impl.MlKem.AArch64.Paired.init sb ss a b k))
  (.seq Impl.MlKem.AArch64.Paired.squeeze
   (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)))

def beginRegs : List Reg := startRegs++[.x9,.x16]++
 [.x0,.x2,.x3,.x4,.x5,.x6,.x7,.x8,.x9,.x10,.x11,.x12,.x13,.x14,.x15,.x22,.x23]

structure BeginPostW (w16 : Bool) (A B : Spec.Sha3.State) (p a b c : Addr) (s t : State) : Prop where
 keep : Keep beginRegs s t
 frame : Frame (stepWrites p a b) s.mem t.mem
 saved : Noise.Saved p s t.mem
 progress : ProgressW w16 A B 3 p a b c t
 flag : (t.gpr .x6).toNat=if (accepted A 3).length=256 ∧ (accepted B 3).length=256 then 1 else 0

theorem begin_ok {w16 : Bool} {s : State} {p seed outA outB table : Addr} {sb ss a b k oa ob : Nat}
    (hss : ss<65536) (hsb : sb+32≤32768) (h8 : sb%8=0)
    (hoa : oa<65536) (hob : ob<65536)
    (hp : s.gpr .x28+BitVec.ofNat 64 ss=p) (hseed : s.gpr .x28+BitVec.ofNat 64 sb=seed)
    (houtA : s.gpr .x28+BitVec.ofNat 64 oa=outA) (houtB : s.gpr .x28+BitVec.ofNat 64 ob=outB)
    (hin : ∀j<4,InRegions (s.rd++s.wr) (seed+BitVec.ofNat 64 (8*j)) 8)
    (hsep : (Region.mk seed 32).Disjoint ⟨p,2048⟩)
    (ctx : Context p outA outB table s) (ht : s.syms "VG_MLKEM_REJ_SHUFFLE"=table) :
    WP isa (beginCode sb ss a b k oa ob w16) s
      (BeginPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB table s) := by
  have combined := WP.mono_syms (start_ok (a := a) (b := b) (k := k) hss hsb h8 hp hseed hin ctx.scratch hsep)
    (R := fun u => WP isa (.seq (.block Impl.MlKem.AArch64.Rej8.rejConsts) (initialCode oa ob w16)) u
      (BeginPostW w16 (seedState s.mem seed a k) (seedState s.mem seed b k) p outA outB table s))
    (fun u ⟨ku,fu,svu,u19,_,pu,buA,buB⟩ sy => by
      have cu : Context p outA outB table u := ctx.frame ku.rd ku.wr (fu.mono (by simp [stepWrites]))
      refine WP.seq (WP.mono_syms (Rej8.constants_ok u (by
        rw [u19]; exact Noise.inScratch cu.scratch (by decide) (by decide)))
        fun v ⟨kv,cv,mv,tv⟩ syv => ?_)
      have fv : Frame [⟨p+1408,8⟩] u.mem v.mem := by
        rw [mv,u19]
        exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ 8)
      have fvBig : Frame (stepWrites p outA outB) u.mem v.mem := fv.sub (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
      have ctv := cu.frame kv.rd kv.wr fvBig
      have v19 : v.gpr .x19=p := (kv.get .x19).trans u19
      have v28 : v.gpr .x28=s.gpr .x28 := (kv.get .x28).trans (ku.get .x28)
      have v16 : v.gpr .x16=table := by rw [tv,syv,sy,ht]
      have streamA : ∀i<504,v.mem ((p+400)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed a k) i := by
        intro i hi
        have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+400) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact (Offset.disjoint p (d := 400) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide))
        exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buA.byte hi)
      have streamB : ∀i<504,v.mem ((p+904)+BitVec.ofNat 64 i)=shakeStream (seedState s.mem seed b k) i := by
        intro i hi
        have hd : ∀r∈[Region.mk (p+1408) 8],(Region.mk (p+904) 504).Disjoint r := by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact (Offset.disjoint p (d := 904) (e := 1408) (n := 504) (k := 8) (by decide) (by decide) (by decide))
        exact (fv.bytes hd (by change 504≤2^64; decide) hi).trans (buB.byte hi)
      have ea := ctv.envW (w16 := w16) (N := 168) (off := 400) v16 (by decide) (by decide) (Or.inl rfl) streamA
      have eb := ctv.envW (w16 := w16) (N := 168) (off := 904) v16 (by decide) (by decide) (Or.inr rfl) streamB
      have pv := pair_frame pu fv (by
        simp only [List.mem_singleton,forall_eq]
        exact Offset.base_disjoint p (by decide) (by decide))
      have svv := svu.frame fv (by
        simp only [List.mem_singleton,forall_eq]
        exact Offset.disjoint p (by decide) (by decide) (by decide))
      have pars := initial_ok hoa hob
        (by rw [v19,v28,houtA]; exact ea)
        (by rw [v19,v28,houtB]; exact eb) cv
        (by rw [v19]; exact ctv.scratch)
        (by rw [v19,v28,houtA]; exact ctv.farA.symm)
        (by rw [v19,v28,houtB]; exact ctv.farB.symm)
        (by rw [v28,houtA,houtB]; exact ctv.apart)
        (by intro mask hm; rw [v19,v16]; exact ctv.tableScratch.sub_left (Rej8.table_sub table hm))
      refine WP.mono pars fun t ht' => ?_
      have ft : Frame (initialRegions p outA outB) v.mem t.mem := by
        simpa only [v19,v28,houtA,houtB] using ht'.frame
      have ftBig : Frame (stepWrites p outA outB) v.mem t.mem := ft.sub (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ⟨_,by simp [stepWrites],fun _ h => h⟩
        · exact ⟨_,by simp [stepWrites],fun _ h => h⟩
        · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩
        · exact ⟨⟨p,2048⟩,by simp [stepWrites],Offset.sub_base p (by decide)⟩)
      have ctt := ctv.frame ht'.keep.rd ht'.keep.wr ftBig
      have pt := pair_frame pv ft (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ctx.farA.sub_left (Region.sub_prefix (by decide : 400≤2048))
        · exact ctx.farB.sub_left (Region.sub_prefix (by decide : 400≤2048))
        · exact Offset.base_disjoint p (by decide) (by decide)
        · exact Offset.base_disjoint p (by decide) (by decide))
      have svt := svv.frame ft (by
        intro r hr; simp only [initialRegions,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        · exact ctx.farA.sub_left (Offset.sub_base p (by decide))
        · exact ctx.farB.sub_left (Offset.sub_base p (by decide))
        · exact Offset.disjoint p (by decide) (by decide) (by decide)
        · exact Offset.disjoint p (by decide) (by decide) (by decide))
      refine ⟨((ku.trans kv).trans ht'.keep).mono (by simp [beginRegs,List.append_assoc]),
        ((fu.mono (by simp [stepWrites])).trans fvBig).trans ftBig,svt,
        ⟨ctt,(ht'.keep.get .x19).trans v19,pt,?_,?_,?_,?_⟩,?_⟩
      · simpa only [accepted,v28,houtA] using ht'.first
      · simpa only [accepted,v28,houtB] using ht'.second
      · have hh := ht'.savedA
        rw [v19,v28,houtA] at hh
        exact hh
      · have hh := ht'.savedB
        rw [v19,v28,houtB] at hh
        exact hh
      · exact ht'.both)
  exact WP.seq (WP.mono (WP.seq_iff.mp combined) fun u hu => WP.seq hu)

end VG.Proof.MlKem.AArch64.Paired
