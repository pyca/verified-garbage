module

public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Save
public import VerifiedGarbage.Proof.Gcm.RISCV64.Prepared.Block

/-! # Load the prepared GHASH key and accumulator -/

@[expose] public section
namespace VG.Proof.Gcm.RISCV64
open VG.Impl.Gcm.RISCV64.Prepared
open VG VG.RISCV64 VG.RISCV64.Steps VG.Impl.Gcm.RISCV64
open VG.Spec.Gcm (Block blockAt blocksAt ghashFrom)

structure CachedPre (H : Block) (s : State) : Prop where
  rd : s.rd = [⟨s.gpr .a0,288⟩,⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩]
  wr : s.wr = [⟨s.gpr .a1,16⟩,⟨s.gpr .a4,256⟩]
  tableAlign : (s.gpr .a0).toNat % 8 = 0
  stackTable : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a0,288⟩
  stackY : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a1,16⟩
  stackData : (⟨(allocd 112 s).sp,112⟩ : Region).Disjoint ⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩
  fd : (s.gpr .a2).toNat + 16*(s.gpr .a3).toNat ≤ 2^64
  frame : CompactFrame (allocd 112 s).sp (allocd 112 s)
  key : ∃ h0 h1, H = h0 ++ h1 ∧ Tab (Holes.key0 h0 h1) (Holes.key1 h0 h1)
    (fun d => s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 d) 64)

structure SplitHead (H : Block) (s a sY : State) : Prop where
  loop : SplitLoopPre H (s.gpr .a2) s.mem (s.gpr .a3).toNat sY
  inv : SplitInv H (blockAt s.mem (s.gpr .a1)) (s.gpr .a2) s.mem (s.gpr .a3).toNat sY 0 sY
  yp : sY.gpr YP=s.gpr .a1
  wr : sY.wr=a.wr
  sp : sY.sp=a.sp
  spill : sY.gpr .a0=a.sp
  slots : ∀ p ∈ compactSaved, sY.mem.readW (a.sp+BitVec.ofNat 64 p.2) 64=s.gpr p.1
  fy : Frame [⟨a.sp,112⟩] s.mem sY.mem

theorem cached_head_ok {H : Block} (s : State) (hp : CachedPre H s) :
    WP isa (.block (.addSp .t0 0 :: compactSave ++ [.addi FP HP 0, .addSp HP 0] ++ maskCode ++ loadY)) (allocd 112 s)
      (SplitHead H s (allocd 112 s)) := by
  set a := allocd 112 s with ha
  have ard : a.rd = s.rd := rfl
  have awr : a.wr = ⟨a.sp,112⟩ :: s.wr := rfl
  have amem : a.mem = s.mem := rfl
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (compact_save_ok a hp.frame) fun u1 ⟨fp1,sp1,k1,p1,m1⟩ => ?_
  refine WP.mono (maskCode_ok u1) fun u2 ⟨K2,k2,m2,p2⟩ => ?_
  obtain hYr : InRegions (u2.rd ++ u2.wr) (u2.gpr YP) 16 := by
    rw [k2.2.1,k2.2.2,Keep.gpr k2 (by decide),k1.2.1,k1.2.2,Keep.gpr k1 (by decide)]
    exact ⟨⟨s.gpr .a1,16⟩,List.mem_append_right _ (by rw [awr,hp.wr];simp),Region.contains_self _ _⟩
  refine WP.mono (ld2_ok (d₀ := Y0) (d₁ := Y1) (tmp := .t2) (n := YP) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) u2 hYr) fun sY ⟨y0,y1,k3,m3,p3⟩ => ?_
  obtain FY : Frame [⟨a.sp,112⟩] s.mem sY.mem := by
    rw [m3,m2,m1,←amem]; exact compactSaveMem_frame _ _ _
  have keep := Keep.trans k2 k3
  have total := Keep.trans k1 keep
  obtain fpY : sY.gpr FP=s.gpr .a0 := (Keep.gpr keep (by decide)).trans fp1
  obtain spillY : sY.gpr .a0=a.sp := (Keep.gpr keep (by decide)).trans sp1
  obtain hF : CompactFrame (sY.gpr .a0) sY := by rw [spillY]; exact hp.frame.of_wr total.2.2
  obtain dataY : sY.gpr DP = s.gpr .a2 := Keep.gpr total (by decide)
  obtain countY : sY.gpr N = s.gpr .a3 := Keep.gpr total (by decide)
  obtain keyRead : ∀ k < 36, Rd8 sY (8*k) := by
    intro k hk
    refine ⟨by omega_using [hk], ?_, ?_⟩
    · rw [fpY]
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (a:=8*k) (by omega_using [hk])]
      have := (s.gpr .a0).isLt
      omega_using [hp.tableAlign]
    · rw [total.2.1,total.2.2,ard,hp.rd,fpY]
      exact ⟨_,List.mem_append_left _ List.mem_cons_self,Offset.contains_base _ (by omega_using [hk]) (by omega_using [hk])⟩
  obtain S : SpillSlots sY .a0 0 := by
    refine ⟨by decide,fun k hk => ⟨by simp only [slot,Nat.zero_add];omega_using [hk], hF.al8 (by simp [slot]) (by simp only [slot,Nat.zero_add];omega_using [hk]),
      hF.inW (by simp only [slot,Nat.zero_add];omega_using [hk])⟩,?_⟩
    intro j hj k hk x hx hz
    rw [fpY] at hx
    simp only [spillY, slot, Nat.zero_add] at hz
    have shrink (B : Addr) {i n : Nat} (hi : 8*i + 8 ≤ n) (fit : n < 2^64) {x : Addr} (h : (x-(B+BitVec.ofNat 64 (8*i))).toNat < 8) :
        (⟨B,n⟩ : Region).Contains x 1 := by
      simp only [Region.Contains]
      rw [Offset.toNat_sub_add x B (by omega_using [hi,fit])] at h
      omega_using [hi,fit,h]
    apply hp.stackTable x (shrink a.sp (i:=k) (by omega_using [hk]) (by decide) hz)
    exact shrink _ (i:=j) (by omega_using [hj]) (by decide) hx
  obtain keySame : ∀ k < 36, fw sY (8*k) = s.mem.readW (s.gpr .a0 + BitVec.ofNat 64 (8*k)) 64 := by
    intro k hk
    unfold fw
    rw [fpY]
    exact FY.readW (Offset.contains_base (s.gpr .a0) (d:=8*k) (by omega_using [hk]) (by omega_using [hk]) :
      (⟨s.gpr .a0,288⟩ : Region).Contains _ (64/8)) (fun r hr => by simp only [List.mem_singleton] at hr; subst r; exact hp.stackTable.symm) (by decide)
  obtain out : ∀ {m : Mem}, Frame [⟨a.sp,112⟩] s.mem m → ∀ {R : Region}, (⟨a.sp,112⟩ : Region).Disjoint R →
      R.len ≤ 2^64 → ∀ i < R.len, m (R.base + BitVec.ofNat 64 i) = s.mem (R.base + BitVec.ofNat 64 i) :=
    fun hm R hd hR i hi => hm _ fun r hr hc => by
      simp only [List.mem_singleton] at hr
      subst r
      exact hd _ hc (Offset.contains_base _ (by omega_using [hi]) (by omega_using [hR,hi]))
  obtain hYk : blockAt s.mem (s.gpr .a1) = w2 (sY.gpr Y0) (sY.gpr Y1) := by
    rw [y0, y1, Keep.gpr k2 (by decide), Keep.gpr k1 (by decide),
      show w2 (ByteLoad.be64 u2.mem (a.gpr YP) 0) (ByteLoad.be64 u2.mem (a.gpr YP) 8) = hOf u2.mem (s.gpr .a1) from rfl,
      ← blockAt_hOf, ← m3]
    exact (Proof.Gcm.blockAt_congr fun i hi => out FY (R := ⟨s.gpr .a1,16⟩) hp.stackY (by simp) i hi).symm
  refine ⟨⟨S,keyRead,Keep.masks k3 K2 (fun i hi => by interval_cases i <;> decide),?_,?_,?_⟩,
    ⟨?_,?_,?_,Keep.refl _ _,rfl,fun _ _ => rfl,Frame.refl _ _⟩,
    Keep.gpr total (by decide),total.2.2,p3.trans (p2.trans p1),spillY,?_,FY⟩
  · obtain ⟨h0,h1,hH,hk⟩ := hp.key
    exact ⟨h0,h1,hH,fun i hi j hj => (keySame (4*i+j) (by omega_using [hi,hj])).trans (hk i hi j hj)⟩
  · intro i hi
    rw [total.2.1,total.2.2,ard]
    exact ⟨⟨s.gpr .a2,16*(s.gpr .a3).toNat⟩,List.mem_append_left _ (by rw [hp.rd];simp),
      Offset.contains_base _ (by omega_using [hi]) (by omega_using [hp.fd,hi])⟩
  · intro i hi j hj m hm
    have hm' : Frame [⟨a.sp,112⟩] s.mem m := FY.trans (hm.sub fun r hr => ⟨_,List.mem_cons_self,by
      simp only [List.mem_singleton] at hr;subst r;rw [spillY];simpa using Offset.sub_base a.sp (d:=0) (n:=32) (k:=112) (by decide)⟩)
    have := out hm' hp.stackData (by simp;omega_using [hp.fd]) (16*i+j) (by simp;omega_using [hi,hj])
    rwa [BitVec.add_assoc,BitVec.ofNat_add_ofNat]
  · rw [Proof.Gcm.ghashFrom_blocksAt_zero,hYk]
  · rw [dataY];simp
  · rw [countY,Nat.sub_zero,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · intro p ht
    rw [m3,m2,m1]
    exact readW_compactSaveMem _ _ _ _ ht

end VG.Proof.Gcm.RISCV64
